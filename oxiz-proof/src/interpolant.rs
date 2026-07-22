//! Craig interpolant extraction from resolution refutations.
//!
//! An interpolant for a pair of formulas `(A, B)` where `A ∧ B` is
//! unsatisfiable is a formula `I` such that:
//! - `A ⟹ I`
//! - `I ∧ B` is unsatisfiable
//! - `I` only contains symbols common to both `A` and `B`
//!
//! Interpolants are useful for model checking, invariant generation,
//! and compositional verification.
//!
//! # Algorithm
//!
//! This module implements McMillan's interpolation system over a propositional
//! resolution refutation (Reference: McMillan, "Interpolation and SAT-Based
//! Model Checking", CAV 2003; and Z3's `iz3`/interpolation machinery). Given
//! the proof DAG that derives the empty clause from the input clauses of
//! `A ∪ B`:
//!
//! 1. Each input clause (axiom) is colored `A` or `B` from the caller's
//!    explicit [`Partition`], resolved through the
//!    [`PremiseTracker`] by matching the
//!    axiom's conclusion text to a [`PremiseId`].
//!    Axioms outside the partition are colored by which side's *vocabulary*
//!    their symbols touch. A clause whose vocabulary spans both sides without
//!    an explicit assignment (`AB`) cannot be soundly decomposed by this
//!    leaf-based system and is reported as an error rather than fabricated.
//! 2. The shared/global vocabulary -- the only symbols a sound interpolant may
//!    mention -- is the intersection of the vocabulary observed on `A` axioms
//!    and on `B` axioms.
//! 3. Partial interpolants are computed bottom-up over the DAG:
//!    - `A`-axiom: the disjunction of its shared-vocabulary literals (`false`
//!      when it has none).
//!    - `B`-axiom: `true`.
//!    - binary resolution on pivot `x`: `I₁ ∨ I₂` when `x` is `A`-local, and
//!      `I₁ ∧ I₂` when `x` is `B`-local or shared.
//!
//! Inference steps that are not binary propositional resolution (e.g. theory
//! lemmas) cannot be soundly colored here and produce an explicit unsupported
//! error rather than a placeholder.

use crate::premise::{PremiseId, PremiseTracker};
use crate::proof::{Proof, ProofNodeId, ProofStep};
use rustc_hash::{FxHashMap, FxHashSet};
use std::fmt;

/// A partition of premises into A-side and B-side.
#[derive(Debug, Clone)]
pub struct Partition {
    /// Premises in the A partition.
    a_premises: FxHashSet<PremiseId>,
    /// Premises in the B partition.
    b_premises: FxHashSet<PremiseId>,
}

impl Partition {
    /// Create a new partition.
    #[must_use]
    pub fn new(
        a_premises: impl IntoIterator<Item = PremiseId>,
        b_premises: impl IntoIterator<Item = PremiseId>,
    ) -> Self {
        Self {
            a_premises: a_premises.into_iter().collect(),
            b_premises: b_premises.into_iter().collect(),
        }
    }

    /// Check if a premise is in the A partition.
    #[must_use]
    pub fn is_a_premise(&self, premise: PremiseId) -> bool {
        self.a_premises.contains(&premise)
    }

    /// Check if a premise is in the B partition.
    #[must_use]
    pub fn is_b_premise(&self, premise: PremiseId) -> bool {
        self.b_premises.contains(&premise)
    }

    /// Get all A premises.
    #[must_use]
    pub fn a_premises(&self) -> &FxHashSet<PremiseId> {
        &self.a_premises
    }

    /// Get all B premises.
    #[must_use]
    pub fn b_premises(&self) -> &FxHashSet<PremiseId> {
        &self.b_premises
    }
}

/// Color of a proof node in the interpolation procedure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Color {
    /// Node depends only on A premises.
    A,
    /// Node depends only on B premises.
    B,
    /// Node depends on both A and B premises (mixed).
    AB,
}

impl fmt::Display for Color {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::A => write!(f, "A"),
            Self::B => write!(f, "B"),
            Self::AB => write!(f, "AB"),
        }
    }
}

/// An interpolant formula.
#[derive(Debug, Clone)]
pub struct Interpolant {
    /// The interpolant formula (as an SMT-LIB-style string).
    pub formula: String,
    /// Symbols used in the interpolant.
    pub symbols: FxHashSet<String>,
}

impl Interpolant {
    /// Create a new interpolant.
    #[must_use]
    pub fn new(formula: impl Into<String>) -> Self {
        let formula = formula.into();
        let symbols = extract_symbols(&formula);
        Self { formula, symbols }
    }

    /// Check if the interpolant only uses common symbols.
    #[must_use]
    pub fn is_valid(&self, a_symbols: &FxHashSet<String>, b_symbols: &FxHashSet<String>) -> bool {
        let common: FxHashSet<String> = a_symbols.intersection(b_symbols).cloned().collect();
        self.symbols.is_subset(&common)
    }
}

impl fmt::Display for Interpolant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.formula)
    }
}

/// Locality of a resolution pivot relative to the A/B vocabulary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Locality {
    /// The pivot symbol occurs only on the A side.
    ALocal,
    /// The pivot symbol occurs only on the B side.
    BLocal,
    /// The pivot symbol occurs on both sides (shared/global).
    Global,
}

/// A structured interpolant formula, kept as a small AST so that intermediate
/// combinations can be simplified before being rendered to a string.
#[derive(Debug, Clone, PartialEq, Eq)]
enum IForm {
    /// Boolean constant `true`.
    True,
    /// Boolean constant `false`.
    False,
    /// An opaque literal rendered verbatim (e.g. `p` or `(not p)`).
    Lit(String),
    /// Conjunction.
    And(Vec<IForm>),
    /// Disjunction.
    Or(Vec<IForm>),
}

impl IForm {
    /// Build a conjunction, collapsing constants and flattening nesting.
    fn and(terms: Vec<IForm>) -> IForm {
        let mut flat = Vec::new();
        for t in terms {
            match t {
                IForm::True => continue,
                IForm::False => return IForm::False,
                IForm::And(inner) => flat.extend(inner),
                other => {
                    if !flat.contains(&other) {
                        flat.push(other);
                    }
                }
            }
        }
        match flat.len() {
            0 => IForm::True,
            1 => flat.into_iter().next().unwrap_or(IForm::True),
            _ => IForm::And(flat),
        }
    }

    /// Build a disjunction, collapsing constants and flattening nesting.
    fn or(terms: Vec<IForm>) -> IForm {
        let mut flat = Vec::new();
        for t in terms {
            match t {
                IForm::False => continue,
                IForm::True => return IForm::True,
                IForm::Or(inner) => flat.extend(inner),
                other => {
                    if !flat.contains(&other) {
                        flat.push(other);
                    }
                }
            }
        }
        match flat.len() {
            0 => IForm::False,
            1 => flat.into_iter().next().unwrap_or(IForm::False),
            _ => IForm::Or(flat),
        }
    }

    /// Render to an SMT-LIB-style string.
    fn render(&self) -> String {
        match self {
            IForm::True => "true".to_string(),
            IForm::False => "false".to_string(),
            IForm::Lit(s) => s.clone(),
            IForm::And(ts) => Self::render_nary("and", ts),
            IForm::Or(ts) => Self::render_nary("or", ts),
        }
    }

    fn render_nary(op: &str, ts: &[IForm]) -> String {
        let mut out = String::from("(");
        out.push_str(op);
        for t in ts {
            out.push(' ');
            out.push_str(&t.render());
        }
        out.push(')');
        out
    }
}

/// Interpolant extractor.
///
/// Extracts Craig interpolants from resolution refutations using McMillan's
/// symmetric interpolation system.
#[derive(Debug)]
pub struct InterpolantExtractor {
    /// Partition of premises.
    partition: Partition,
    /// Premise tracker for looking up premises.
    premise_tracker: PremiseTracker,
    /// Node colors (computed during extraction).
    colors: FxHashMap<ProofNodeId, Color>,
    /// Partial interpolants for each node.
    partial_interpolants: FxHashMap<ProofNodeId, IForm>,
    /// Axiom colors resolved directly from the caller's partition.
    direct_axiom_colors: FxHashMap<ProofNodeId, Color>,
    /// Vocabulary observed on directly-colored A axioms.
    a_vocab: FxHashSet<String>,
    /// Vocabulary observed on directly-colored B axioms.
    b_vocab: FxHashSet<String>,
    /// Shared/global vocabulary: `a_vocab ∩ b_vocab`.
    shared: FxHashSet<String>,
}

impl InterpolantExtractor {
    /// Create a new interpolant extractor.
    #[must_use]
    pub fn new(partition: Partition, premise_tracker: PremiseTracker) -> Self {
        Self {
            partition,
            premise_tracker,
            colors: FxHashMap::default(),
            partial_interpolants: FxHashMap::default(),
            direct_axiom_colors: FxHashMap::default(),
            a_vocab: FxHashSet::default(),
            b_vocab: FxHashSet::default(),
            shared: FxHashSet::default(),
        }
    }

    /// Extract an interpolant from a proof.
    ///
    /// The proof must derive the empty clause (`false`) from `A ∪ B`.
    ///
    /// # Errors
    ///
    /// Returns an error when the proof is not a refutation (its root is not
    /// the empty clause), when an axiom mixes A and B vocabulary without an
    /// explicit partition assignment, or when the proof contains an inference
    /// step that is not binary propositional resolution (which this system
    /// cannot soundly color).
    pub fn extract(&mut self, proof: &Proof) -> Result<Interpolant, String> {
        let root = proof
            .root()
            .ok_or_else(|| "Proof has no root".to_string())?;

        // A valid interpolation problem requires a refutation: the proof must
        // derive the empty clause. Refuse to fabricate an interpolant for a
        // proof that does not.
        let root_conclusion = proof
            .get_node(root)
            .map(|n| n.conclusion().to_string())
            .ok_or_else(|| "Root node not found".to_string())?;
        if !is_empty_clause_conclusion(&root_conclusion) {
            return Err(format!(
                "proof does not derive the empty clause (root conclusion is {root_conclusion:?}); \
                 interpolation requires a refutation of A ∧ B"
            ));
        }

        // Determine the ground-truth A/B coloring and shared vocabulary from
        // the caller's explicit premise partition.
        self.precompute_axiom_partition(proof);

        // Fresh per-extraction state (supports repeated calls).
        self.colors.clear();
        self.partial_interpolants.clear();

        // Phase 1: color every node (bottom-up).
        self.compute_colors(proof, root)?;

        // Phase 2: build partial interpolants (bottom-up).
        self.build_interpolants(proof, root)?;

        let form = self
            .partial_interpolants
            .get(&root)
            .ok_or_else(|| "No interpolant at root".to_string())?;

        Ok(Interpolant::new(form.render()))
    }

    /// Precompute, from the proof's axioms, which are directly identifiable as
    /// A- or B-premises via the caller-supplied partition (matched by
    /// conclusion text against the premise tracker), and derive the resulting
    /// per-side vocabulary plus the shared vocabulary.
    fn precompute_axiom_partition(&mut self, proof: &Proof) {
        self.direct_axiom_colors.clear();
        let mut a_symbols = FxHashSet::default();
        let mut b_symbols = FxHashSet::default();

        for node in proof.nodes() {
            let ProofStep::Axiom { conclusion } = &node.step else {
                continue;
            };
            let Some(premise_id) = self.premise_tracker.get_id(conclusion) else {
                continue;
            };
            let in_a = self.partition.is_a_premise(premise_id);
            let in_b = self.partition.is_b_premise(premise_id);
            let color = match (in_a, in_b) {
                (true, false) => Color::A,
                (false, true) => Color::B,
                (true, true) => Color::AB,
                (false, false) => continue,
            };
            self.direct_axiom_colors.insert(node.id, color);

            let mut symbols = FxHashSet::default();
            for lit in parse_clause_literals(conclusion) {
                symbols.extend(lit.symbols);
            }
            match color {
                Color::A => a_symbols.extend(symbols),
                Color::B => b_symbols.extend(symbols),
                Color::AB => {
                    a_symbols.extend(symbols.iter().cloned());
                    b_symbols.extend(symbols);
                }
            }
        }

        self.shared = a_symbols.intersection(&b_symbols).cloned().collect();
        self.a_vocab = a_symbols;
        self.b_vocab = b_symbols;
    }

    /// Compute the color of each proof node.
    fn compute_colors(&mut self, proof: &Proof, node_id: ProofNodeId) -> Result<Color, String> {
        if let Some(&color) = self.colors.get(&node_id) {
            return Ok(color);
        }

        let node = proof
            .get_node(node_id)
            .ok_or_else(|| format!("Node {node_id} not found"))?;

        let color = match &node.step {
            ProofStep::Axiom { conclusion } => self.color_axiom(node_id, conclusion),
            ProofStep::Inference { premises, .. } => {
                let premises: Vec<ProofNodeId> = premises.iter().copied().collect();
                let mut has_a = false;
                let mut has_b = false;
                for premise_id in premises {
                    match self.compute_colors(proof, premise_id)? {
                        Color::A => has_a = true,
                        Color::B => has_b = true,
                        Color::AB => {
                            has_a = true;
                            has_b = true;
                        }
                    }
                }
                match (has_a, has_b) {
                    (true, true) => Color::AB,
                    (false, true) => Color::B,
                    // Pure-A, and the degenerate premise-less case, both color A.
                    _ => Color::A,
                }
            }
        };

        self.colors.insert(node_id, color);
        Ok(color)
    }

    /// Color an axiom using the caller's explicit partition when available,
    /// falling back to a vocabulary-membership heuristic for axioms outside
    /// the partition (typically synthesized theory lemmas rather than original
    /// user assertions).
    fn color_axiom(&self, node_id: ProofNodeId, conclusion: &str) -> Color {
        if let Some(&color) = self.direct_axiom_colors.get(&node_id) {
            return color;
        }
        let mut symbols = FxHashSet::default();
        for lit in parse_clause_literals(conclusion) {
            symbols.extend(lit.symbols);
        }
        let touches_a = symbols.iter().any(|s| self.a_vocab.contains(s));
        let touches_b = symbols.iter().any(|s| self.b_vocab.contains(s));
        match (touches_a, touches_b) {
            (true, false) => Color::A,
            (false, true) => Color::B,
            (true, true) => Color::AB,
            (false, false) => Color::A,
        }
    }

    /// Build partial interpolants for each node.
    fn build_interpolants(&mut self, proof: &Proof, node_id: ProofNodeId) -> Result<(), String> {
        if self.partial_interpolants.contains_key(&node_id) {
            return Ok(());
        }

        let node = proof
            .get_node(node_id)
            .ok_or_else(|| format!("Node {node_id} not found"))?;

        let form = match &node.step {
            ProofStep::Axiom { conclusion } => {
                let color = *self
                    .colors
                    .get(&node_id)
                    .ok_or_else(|| format!("Node {node_id} has no color"))?;
                self.axiom_interpolant(node_id, color, conclusion)?
            }
            ProofStep::Inference { rule, premises, .. } => {
                let rule = rule.clone();
                let premises: Vec<ProofNodeId> = premises.iter().copied().collect();
                for &premise_id in &premises {
                    self.build_interpolants(proof, premise_id)?;
                }
                self.resolution_interpolant(proof, node_id, &rule, &premises)?
            }
        };

        self.partial_interpolants.insert(node_id, form);
        Ok(())
    }

    /// Base-case interpolant for an axiom leaf (McMillan's system):
    /// - `A`: disjunction of its shared-vocabulary literals (`false` if none),
    /// - `B`: `true`,
    /// - `AB`: not soundly decomposable at a leaf -> explicit error.
    fn axiom_interpolant(
        &self,
        node_id: ProofNodeId,
        color: Color,
        conclusion: &str,
    ) -> Result<IForm, String> {
        match color {
            Color::A => {
                let shared_lits: Vec<IForm> = parse_clause_literals(conclusion)
                    .into_iter()
                    .filter(|lit| {
                        !lit.symbols.is_empty()
                            && lit.symbols.iter().all(|s| self.shared.contains(s))
                    })
                    .map(|lit| lit.to_iform())
                    .collect();
                if shared_lits.is_empty() {
                    Ok(IForm::False)
                } else {
                    Ok(IForm::or(shared_lits))
                }
            }
            Color::B => Ok(IForm::True),
            Color::AB => Err(format!(
                "unsupported: axiom {node_id} ({conclusion:?}) mixes A and B vocabulary; \
                 this leaf-based interpolation system cannot soundly decompose a mixed axiom"
            )),
        }
    }

    /// Combine premise interpolants across a binary resolution step using
    /// McMillan's pivot rule. Any inference that is not binary propositional
    /// resolution with a recoverable, propositional pivot is reported as an
    /// unsupported error rather than approximated.
    fn resolution_interpolant(
        &self,
        proof: &Proof,
        node_id: ProofNodeId,
        rule: &str,
        premises: &[ProofNodeId],
    ) -> Result<IForm, String> {
        if !is_resolution_rule(rule) {
            return Err(format!(
                "unsupported: cannot interpolate `{rule}` inference at {node_id} \
                 (only binary propositional resolution steps are supported; \
                 theory-level steps are not soundly colorable here)"
            ));
        }
        if premises.len() != 2 {
            return Err(format!(
                "unsupported: resolution step {node_id} has {} premises (expected 2)",
                premises.len()
            ));
        }

        let c1 = proof
            .get_node(premises[0])
            .map(|n| n.conclusion().to_string())
            .ok_or_else(|| format!("premise {} of {node_id} not found", premises[0]))?;
        let c2 = proof
            .get_node(premises[1])
            .map(|n| n.conclusion().to_string())
            .ok_or_else(|| format!("premise {} of {node_id} not found", premises[1]))?;

        let pivot = find_pivot(&c1, &c2).ok_or_else(|| {
            format!(
                "cannot recover a unique resolution pivot for step {node_id} \
                 between clauses {c1:?} and {c2:?}"
            )
        })?;
        let locality = self.classify_pivot(&pivot)?;

        let i1 = self
            .partial_interpolants
            .get(&premises[0])
            .cloned()
            .ok_or_else(|| format!("missing interpolant for premise {}", premises[0]))?;
        let i2 = self
            .partial_interpolants
            .get(&premises[1])
            .cloned()
            .ok_or_else(|| format!("missing interpolant for premise {}", premises[1]))?;

        Ok(match locality {
            Locality::ALocal => IForm::or(vec![i1, i2]),
            Locality::BLocal | Locality::Global => IForm::and(vec![i1, i2]),
        })
    }

    /// Classify a resolution pivot's locality against the known A/B
    /// vocabulary. The pivot must be a propositional atom (a bare identifier):
    /// theory-level pivots are rejected as unsupported.
    fn classify_pivot(&self, pivot_atom: &str) -> Result<Locality, String> {
        let atom = pivot_atom.trim();
        let is_propositional_atom = !atom.is_empty()
            && atom.chars().all(|c| c.is_alphanumeric() || c == '_')
            && !atom.chars().all(|c| c.is_numeric());
        if !is_propositional_atom {
            return Err(format!(
                "unsupported: resolution pivot {atom:?} is not a propositional atom \
                 (theory-level interpolation is not supported here)"
            ));
        }
        if self.shared.contains(atom) {
            Ok(Locality::Global)
        } else if self.b_vocab.contains(atom) {
            Ok(Locality::BLocal)
        } else {
            Ok(Locality::ALocal)
        }
    }
}

/// A parsed clause literal: an atom together with its polarity.
#[derive(Debug, Clone)]
struct ClauseLiteral {
    /// The un-negated atom text, e.g. `p` or `(= a b)`.
    atom: String,
    /// `true` if the literal occurs positively, `false` if negated.
    positive: bool,
    /// Symbols occurring in the atom.
    symbols: FxHashSet<String>,
}

impl ClauseLiteral {
    /// Render this literal as an interpolant formula atom.
    fn to_iform(&self) -> IForm {
        if self.positive {
            IForm::Lit(self.atom.clone())
        } else {
            IForm::Lit(format!("(not {})", self.atom))
        }
    }
}

/// Whether a conclusion string denotes the empty clause / `false`.
fn is_empty_clause_conclusion(s: &str) -> bool {
    let trimmed = s.trim();
    if trimmed == "⊥" {
        return true;
    }
    matches!(
        trimmed.to_ascii_lowercase().as_str(),
        "" | "false" | "()" | "(or)" | "$false" | "bottom"
    )
}

/// Rule names this module treats as binary propositional resolution.
fn is_resolution_rule(rule: &str) -> bool {
    matches!(
        rule,
        "resolution" | "resolve" | "unit_prop" | "unit_propagation"
    )
}

/// Parse a textual clause conclusion into its literals.
///
/// Understands exactly the minimal clause syntax this crate's propositional
/// proof steps use: a bare atom, `(not X)`, and `(or L1 L2 ... Ln)`. The empty
/// clause parses to an empty literal list. Anything else is treated as a
/// single opaque atomic literal (its exact text becomes the atom).
fn parse_clause_literals(conclusion: &str) -> Vec<ClauseLiteral> {
    let trimmed = conclusion.trim();
    if is_empty_clause_conclusion(trimmed) {
        return Vec::new();
    }
    if let Some(inner) = strip_wrapped(trimmed, "or") {
        split_top_level(inner)
            .into_iter()
            .map(parse_literal)
            .collect()
    } else {
        vec![parse_literal(trimmed)]
    }
}

/// Parse a single literal: `(not X)` flips polarity; anything else becomes an
/// opaque atom named after its exact text.
fn parse_literal(text: &str) -> ClauseLiteral {
    let trimmed = text.trim();
    if let Some(inner) = strip_wrapped(trimmed, "not") {
        let mut lit = parse_literal(inner);
        lit.positive = !lit.positive;
        return lit;
    }
    ClauseLiteral {
        atom: trimmed.to_string(),
        positive: true,
        symbols: extract_symbols(trimmed),
    }
}

/// If `text` is `(keyword ...)`, return the content following `keyword`.
fn strip_wrapped<'a>(text: &'a str, keyword: &str) -> Option<&'a str> {
    let inner = text.strip_prefix('(')?.strip_suffix(')')?;
    let inner = inner.trim();
    let rest = inner.strip_prefix(keyword)?;
    if rest.is_empty() {
        Some(rest)
    } else if rest.starts_with(char::is_whitespace) {
        Some(rest.trim_start())
    } else {
        None
    }
}

/// Split `text` on top-level whitespace, treating parenthesised groups as
/// atomic (so `(not p) q` splits into `["(not p)", "q"]`).
fn split_top_level(text: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut start: Option<usize> = None;

    for (i, ch) in text.char_indices() {
        match ch {
            '(' => {
                depth += 1;
                start.get_or_insert(i);
            }
            ')' => {
                depth -= 1;
            }
            c if c.is_whitespace() && depth == 0 => {
                if let Some(s) = start.take() {
                    out.push(&text[s..i]);
                }
            }
            _ => {
                start.get_or_insert(i);
            }
        }
    }
    if let Some(s) = start {
        out.push(&text[s..]);
    }
    out
}

/// Find the unique resolution pivot atom between two clauses given as raw
/// text. Returns `None` when there is not *exactly one* complementary literal
/// pair -- an ambiguous or absent pivot must not be fabricated.
fn find_pivot(clause_a: &str, clause_b: &str) -> Option<String> {
    let lits_a = parse_clause_literals(clause_a);
    let lits_b = parse_clause_literals(clause_b);

    let mut pivots: FxHashSet<String> = FxHashSet::default();
    for la in &lits_a {
        for lb in &lits_b {
            if la.atom == lb.atom && la.positive != lb.positive {
                pivots.insert(la.atom.clone());
            }
        }
    }
    if pivots.len() == 1 {
        pivots.into_iter().next()
    } else {
        None
    }
}

/// Extract symbols from a formula string.
///
/// This is a lightweight heuristic tokenizer: it collects maximal
/// alphanumeric/underscore runs, excluding numeric literals and logical
/// keywords.
fn extract_symbols(formula: &str) -> FxHashSet<String> {
    let mut symbols = FxHashSet::default();

    // Logical operators and keywords to exclude
    let keywords: FxHashSet<&str> = [
        "and", "or", "not", "implies", "iff", "xor", "forall", "exists", "true", "false", "let",
        "ite", "distinct",
    ]
    .iter()
    .copied()
    .collect();

    let mut current = String::new();
    for ch in formula.chars() {
        if ch.is_alphanumeric() || ch == '_' {
            current.push(ch);
        } else {
            if !current.is_empty()
                && !current.chars().all(|c| c.is_numeric())
                && !keywords.contains(current.as_str())
            {
                symbols.insert(current.clone());
            }
            current.clear();
        }
    }

    if !current.is_empty()
        && !current.chars().all(|c| c.is_numeric())
        && !keywords.contains(current.as_str())
    {
        symbols.insert(current);
    }

    symbols
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::proof::Proof;

    #[test]
    fn test_partition_creation() {
        let partition = Partition::new(vec![PremiseId(0), PremiseId(1)], vec![PremiseId(2)]);

        assert!(partition.is_a_premise(PremiseId(0)));
        assert!(partition.is_a_premise(PremiseId(1)));
        assert!(partition.is_b_premise(PremiseId(2)));
        assert!(!partition.is_b_premise(PremiseId(0)));
    }

    #[test]
    fn test_color_display() {
        assert_eq!(format!("{}", Color::A), "A");
        assert_eq!(format!("{}", Color::B), "B");
        assert_eq!(format!("{}", Color::AB), "AB");
    }

    #[test]
    fn test_interpolant_creation() {
        let interp = Interpolant::new("(and p q)");
        assert_eq!(interp.formula, "(and p q)");
        // "and" is a keyword and should not be included
        assert!(!interp.symbols.contains("and"));
        assert!(interp.symbols.contains("p"));
        assert!(interp.symbols.contains("q"));
    }

    #[test]
    fn test_interpolant_validity() {
        let interp = Interpolant::new("(and x y)");

        let mut a_symbols = FxHashSet::default();
        a_symbols.insert("x".to_string());
        a_symbols.insert("y".to_string());
        a_symbols.insert("z".to_string());

        let mut b_symbols = FxHashSet::default();
        b_symbols.insert("x".to_string());
        b_symbols.insert("y".to_string());
        b_symbols.insert("w".to_string());

        // x and y are common, so the interpolant is valid
        assert!(interp.is_valid(&a_symbols, &b_symbols));
    }

    #[test]
    fn test_interpolant_invalid() {
        let interp = Interpolant::new("(and x z)");

        let mut a_symbols = FxHashSet::default();
        a_symbols.insert("x".to_string());
        a_symbols.insert("z".to_string());

        let mut b_symbols = FxHashSet::default();
        b_symbols.insert("x".to_string());
        b_symbols.insert("w".to_string());

        // z is not common, so the interpolant is invalid
        assert!(!interp.is_valid(&a_symbols, &b_symbols));
    }

    #[test]
    fn test_extract_symbols() {
        let symbols = extract_symbols("(and x (or y z))");
        // Keywords like "and" and "or" should be excluded
        assert!(!symbols.contains("and"));
        assert!(symbols.contains("x"));
        assert!(!symbols.contains("or"));
        assert!(symbols.contains("y"));
        assert!(symbols.contains("z"));
    }

    #[test]
    fn test_extract_symbols_numbers() {
        let symbols = extract_symbols("(= x 42)");
        assert!(symbols.contains("x"));
        // Numbers should not be included as symbols
        assert!(!symbols.contains("42"));
    }

    #[test]
    fn test_extractor_creation() {
        let partition = Partition::new(vec![PremiseId(0)], vec![PremiseId(1)]);
        let tracker = PremiseTracker::new();
        let extractor = InterpolantExtractor::new(partition, tracker);

        assert_eq!(extractor.colors.len(), 0);
        assert_eq!(extractor.partial_interpolants.len(), 0);
    }

    #[test]
    fn test_non_refutation_is_rejected() {
        let partition = Partition::new(vec![PremiseId(0)], vec![PremiseId(1)]);
        let tracker = PremiseTracker::new();
        let mut extractor = InterpolantExtractor::new(partition, tracker);

        // A lone axiom does not derive the empty clause, so it is not a
        // refutation and must be rejected rather than yield a fabricated
        // interpolant.
        let mut proof = Proof::new();
        proof.add_axiom("p");

        let result = extractor.extract(&proof);
        assert!(result.is_err());
    }

    // ------------------------------------------------------------------
    // Clause / literal parsing
    // ------------------------------------------------------------------

    #[test]
    fn test_parse_clause_literals_disjunction() {
        let lits = parse_clause_literals("(or (not p) q)");
        assert_eq!(lits.len(), 2);
        assert_eq!(lits[0].atom, "p");
        assert!(!lits[0].positive);
        assert_eq!(lits[1].atom, "q");
        assert!(lits[1].positive);
    }

    #[test]
    fn test_parse_empty_clause() {
        assert!(parse_clause_literals("false").is_empty());
        assert!(parse_clause_literals("⊥").is_empty());
        assert!(parse_clause_literals("(or)").is_empty());
    }

    #[test]
    fn test_find_pivot_unique() {
        assert_eq!(find_pivot("p", "(not p)"), Some("p".to_string()));
        assert_eq!(find_pivot("p", "(or (not p) q)"), Some("p".to_string()));
    }

    #[test]
    fn test_find_pivot_ambiguous_is_none() {
        // Two complementary pairs -> ambiguous -> refuse.
        assert_eq!(find_pivot("(or p q)", "(or (not p) (not q))"), None);
        // No complementary pair -> none.
        assert_eq!(find_pivot("(or p q)", "(or r s)"), None);
    }

    // ------------------------------------------------------------------
    // End-to-end interpolant extraction (exact-formula checks; the full
    // A=>I / I&B-UNSAT semantic validation lives in tests/interpolant_mcmillan.rs)
    // ------------------------------------------------------------------

    /// Classic shape: A = p ∧ q, B = ¬p. Interpolant is `p`.
    #[test]
    fn test_classic_interpolant_is_shared_atom() {
        let mut tracker = PremiseTracker::new();
        let a_p = tracker.add_assertion("p");
        let a_q = tracker.add_assertion("q");
        let b_np = tracker.add_assertion("(not p)");
        let partition = Partition::new(vec![a_p, a_q], vec![b_np]);

        let mut proof = Proof::new();
        let n_p = proof.add_axiom("p");
        let _n_q = proof.add_axiom("q");
        let n_np = proof.add_axiom("(not p)");
        proof.add_inference("resolution", vec![n_p, n_np], "false");

        let mut extractor = InterpolantExtractor::new(partition, tracker);
        let interp = extractor
            .extract(&proof)
            .expect("classic refutation should interpolate");
        assert_eq!(interp.formula, "p");
        assert!(interp.symbols.contains("p"));
    }

    /// A-local pivot (`p`) combined with a shared pivot (`q`) yields `q`.
    /// A = p ∧ (¬p ∨ q), B = ¬q.
    #[test]
    fn test_alocal_and_shared_pivot() {
        let mut tracker = PremiseTracker::new();
        let a_p = tracker.add_assertion("p");
        let a_pq = tracker.add_assertion("(or (not p) q)");
        let b_nq = tracker.add_assertion("(not q)");
        let partition = Partition::new(vec![a_p, a_pq], vec![b_nq]);

        let mut proof = Proof::new();
        let n_p = proof.add_axiom("p");
        let n_pq = proof.add_axiom("(or (not p) q)");
        let n_nq = proof.add_axiom("(not q)");
        let n_q = proof.add_inference("resolution", vec![n_p, n_pq], "q");
        proof.add_inference("resolution", vec![n_q, n_nq], "false");

        let mut extractor = InterpolantExtractor::new(partition, tracker);
        let interp = extractor
            .extract(&proof)
            .expect("refutation should interpolate");
        assert_eq!(interp.formula, "q");
    }

    /// All input clauses on the A side (A alone is unsat) -> interpolant `false`.
    #[test]
    fn test_all_a_interpolant_is_false() {
        let mut tracker = PremiseTracker::new();
        let a_p = tracker.add_assertion("p");
        let a_np = tracker.add_assertion("(not p)");
        let partition = Partition::new(vec![a_p, a_np], Vec::new());

        let mut proof = Proof::new();
        let n_p = proof.add_axiom("p");
        let n_np = proof.add_axiom("(not p)");
        proof.add_inference("resolution", vec![n_p, n_np], "false");

        let mut extractor = InterpolantExtractor::new(partition, tracker);
        let interp = extractor
            .extract(&proof)
            .expect("all-A refutation should interpolate");
        assert_eq!(interp.formula, "false");
        assert!(interp.symbols.is_empty());
    }

    /// All input clauses on the B side (B alone is unsat) -> interpolant `true`.
    #[test]
    fn test_all_b_interpolant_is_true() {
        let mut tracker = PremiseTracker::new();
        let b_p = tracker.add_assertion("p");
        let b_np = tracker.add_assertion("(not p)");
        let partition = Partition::new(Vec::new(), vec![b_p, b_np]);

        let mut proof = Proof::new();
        let n_p = proof.add_axiom("p");
        let n_np = proof.add_axiom("(not p)");
        proof.add_inference("resolution", vec![n_p, n_np], "false");

        let mut extractor = InterpolantExtractor::new(partition, tracker);
        let interp = extractor
            .extract(&proof)
            .expect("all-B refutation should interpolate");
        assert_eq!(interp.formula, "true");
        assert!(interp.symbols.is_empty());
    }

    /// A non-resolution inference cannot be soundly colored -> honest error.
    #[test]
    fn test_unsupported_rule_errors() {
        let mut tracker = PremiseTracker::new();
        let a_p = tracker.add_assertion("p");
        let b_np = tracker.add_assertion("(not p)");
        let partition = Partition::new(vec![a_p], vec![b_np]);

        let mut proof = Proof::new();
        let n_p = proof.add_axiom("p");
        let n_np = proof.add_axiom("(not p)");
        // A theory-flavored rule name is not recognized as resolution.
        proof.add_inference("theory-lemma", vec![n_p, n_np], "false");

        let mut extractor = InterpolantExtractor::new(partition, tracker);
        let err = extractor
            .extract(&proof)
            .expect_err("non-resolution inference should be unsupported");
        assert!(err.contains("unsupported"), "unexpected error: {err}");
    }

    /// A mixed (AB) axiom cannot be decomposed at a leaf -> honest error.
    #[test]
    fn test_mixed_axiom_errors() {
        let mut tracker = PremiseTracker::new();
        // A single premise declared to be on *both* sides.
        let shared = tracker.add_assertion("(or p q)");
        let b_np = tracker.add_assertion("(not p)");
        let partition = Partition::new(vec![shared], vec![shared, b_np]);

        let mut proof = Proof::new();
        let n_shared = proof.add_axiom("(or p q)");
        let n_np = proof.add_axiom("(not p)");
        // The AB axiom is an ancestor of the empty-clause root, so building
        // its partial interpolant fails during extraction.
        proof.add_inference("resolution", vec![n_shared, n_np], "false");

        let mut extractor = InterpolantExtractor::new(partition, tracker);
        let err = extractor
            .extract(&proof)
            .expect_err("mixed axiom should be unsupported");
        assert!(
            err.contains("mixes A and B") || err.contains("unsupported"),
            "unexpected error: {err}"
        );
    }
}
