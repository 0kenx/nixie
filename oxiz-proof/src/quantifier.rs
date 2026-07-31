//! Quantifier instantiation proof generation.
//!
//! This module provides infrastructure for generating proofs of quantifier
//! instantiation steps: [`QuantifierProofRecorder`] records forall-elimination,
//! exists-introduction, and skolemization steps against the crate's generic
//! [`crate::proof::Proof`], and [`EMatchPattern`] provides a small
//! S-expression e-matching unifier for finding instantiations by pattern.
//!
//! # Relationship to `theory`'s quantifier rules
//!
//! [`crate::theory::TheoryProof`] already has its own quantifier
//! proof-step constructors -- `forall_elim`, `exists_intro`, `skolemize`,
//! `quant_inst` -- built on [`crate::theory::TheoryRule`] and checkable
//! (structurally) via [`crate::checker::ProofChecker::check_theory_proof`].
//! This module is a parallel, independent facility for the crate's *other*
//! proof representation, the generic string-conclusion [`crate::proof::Proof`]
//! used by [`crate::builder::ProofBuilder`] -- the same relationship
//! `ProofBuilder`/`TheoryProofBuilder` already have to each other in
//! `builder`. There is no checker for the generic `Proof` type in this
//! crate, so [`QuantifierProofRecorder`]'s own internal validation (see
//! its methods' "# Errors" sections) is the only verification its output
//! gets.
//!
//! # Examples
//!
//! ```
//! use oxiz_proof::{Proof, QuantVar, QuantifiedFormula, QuantifierProofRecorder};
//! use oxiz_proof::QuantifierSubstitution as Substitution;
//!
//! let mut proof = Proof::new();
//! let premise = proof.add_axiom("(> 5 0)");
//!
//! let formula = QuantifiedFormula::exists(vec![QuantVar::new("x", "Int")], "(> x 0)");
//! let mut witness = Substitution::default();
//! witness.insert("x".to_string(), "5".to_string());
//!
//! let mut recorder = QuantifierProofRecorder::new();
//! // The premise (> 5 0) genuinely witnesses (exists x (> x 0)) at x = 5,
//! // so this succeeds; a premise that didn't would be rejected instead --
//! // see `QuantifierProofRecorder::record_exists_intro`'s `# Errors`.
//! recorder
//!     .record_exists_intro(&mut proof, formula, witness, premise)
//!     .expect("premise witnesses the existential");
//! ```

use crate::proof::{Proof, ProofNodeId};
use rustc_hash::FxHashMap;
use std::fmt;

/// A quantified variable.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct QuantVar {
    /// Variable name.
    pub name: String,
    /// Sort (type) of the variable.
    pub sort: String,
}

impl QuantVar {
    /// Create a new quantified variable.
    #[must_use]
    pub fn new(name: impl Into<String>, sort: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            sort: sort.into(),
        }
    }
}

impl fmt::Display for QuantVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {})", self.name, self.sort)
    }
}

/// A quantified formula.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QuantifiedFormula {
    /// Universal quantification: ∀x. φ(x)
    Forall {
        /// Bound variables.
        vars: Vec<QuantVar>,
        /// Body of the formula.
        body: String,
    },
    /// Existential quantification: ∃x. φ(x)
    Exists {
        /// Bound variables.
        vars: Vec<QuantVar>,
        /// Body of the formula.
        body: String,
    },
}

impl QuantifiedFormula {
    /// Create a universal quantification.
    #[must_use]
    pub fn forall(vars: Vec<QuantVar>, body: impl Into<String>) -> Self {
        Self::Forall {
            vars,
            body: body.into(),
        }
    }

    /// Create an existential quantification.
    #[must_use]
    pub fn exists(vars: Vec<QuantVar>, body: impl Into<String>) -> Self {
        Self::Exists {
            vars,
            body: body.into(),
        }
    }

    /// Get the bound variables.
    #[must_use]
    pub fn vars(&self) -> &[QuantVar] {
        match self {
            Self::Forall { vars, .. } | Self::Exists { vars, .. } => vars,
        }
    }

    /// Get the body of the formula.
    #[must_use]
    pub fn body(&self) -> &str {
        match self {
            Self::Forall { body, .. } | Self::Exists { body, .. } => body,
        }
    }

    /// Check if this is a universal quantification.
    #[must_use]
    pub fn is_forall(&self) -> bool {
        matches!(self, Self::Forall { .. })
    }

    /// Check if this is an existential quantification.
    #[must_use]
    pub fn is_exists(&self) -> bool {
        matches!(self, Self::Exists { .. })
    }
}

impl fmt::Display for QuantifiedFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Forall { vars, body } => {
                write!(f, "(forall (")?;
                for (i, var) in vars.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", var)?;
                }
                write!(f, ") {})", body)
            }
            Self::Exists { vars, body } => {
                write!(f, "(exists (")?;
                for (i, var) in vars.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", var)?;
                }
                write!(f, ") {})", body)
            }
        }
    }
}

/// A substitution mapping variables to terms.
pub type Substitution = FxHashMap<String, String>;

/// Apply `substitution` to `body` by simple, non-capture-aware string
/// replacement. Shared by [`Instantiation::apply_substitution`] and
/// [`QuantifierProofRecorder::record_forall_inst`] so the two can never
/// disagree about what a given substitution actually produces (see that
/// recorder method's doc comment for why that used to be possible, and
/// unsound).
fn substitute(body: &str, substitution: &Substitution) -> String {
    let mut result = body.to_string();
    for (var, term) in substitution {
        // Not semantically correct for all cases (e.g. a variable name that
        // is also a substring of another symbol); see `apply_substitution`'s
        // own doc comment, which carries the same caveat.
        result = result.replace(var, term);
    }
    result
}

/// Errors from [`QuantifierProofRecorder`]'s proof-step recording methods.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QuantifierProofError {
    /// [`QuantifierProofRecorder::record_exists_intro`]'s `premise` does not
    /// name an existing node of the `Proof` it was given.
    MissingPremise(ProofNodeId),
    /// [`QuantifierProofRecorder::record_exists_intro`]'s premise does not
    /// actually establish the witness-instantiated body of the existential
    /// being introduced, so it cannot justify it.
    WitnessMismatch {
        /// What substituting the witness into the existential's body
        /// actually produces.
        expected: String,
        /// What the premise's conclusion actually says.
        found: String,
    },
    /// [`QuantifierProofRecorder::record_skolemization`] was given a number
    /// of Skolem terms that does not match the number of the existential's
    /// bound variables, so there is no well-defined correspondence between
    /// them.
    SkolemArityMismatch {
        /// Number of bound variables in the existential formula.
        vars: usize,
        /// Number of Skolem terms supplied.
        terms: usize,
    },
}

impl fmt::Display for QuantifierProofError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingPremise(id) => {
                write!(f, "premise node {id:?} does not exist in this proof")
            }
            Self::WitnessMismatch { expected, found } => write!(
                f,
                "premise concludes {found:?}, but the witness substitution requires {expected:?}"
            ),
            Self::SkolemArityMismatch { vars, terms } => write!(
                f,
                "existential has {vars} bound variable(s) but {terms} Skolem term(s) were supplied"
            ),
        }
    }
}

impl std::error::Error for QuantifierProofError {}

/// An instantiation of a quantified formula.
#[derive(Debug, Clone)]
pub struct Instantiation {
    /// The original quantified formula.
    pub formula: QuantifiedFormula,
    /// Substitution for bound variables.
    pub substitution: Substitution,
    /// The instantiated formula (with substitution applied).
    pub instantiated: String,
}

impl Instantiation {
    /// Create a new instantiation.
    #[must_use]
    pub fn new(
        formula: QuantifiedFormula,
        substitution: Substitution,
        instantiated: impl Into<String>,
    ) -> Self {
        Self {
            formula,
            substitution,
            instantiated: instantiated.into(),
        }
    }

    /// Apply the substitution to get the instantiated formula.
    ///
    /// This is a simple string-based substitution. A real implementation
    /// would use proper term substitution.
    #[must_use]
    pub fn apply_substitution(&self) -> String {
        substitute(self.formula.body(), &self.substitution)
    }
}

/// Proof recorder for quantifier instantiation.
#[derive(Debug, Default)]
pub struct QuantifierProofRecorder {
    /// Recorded instantiations.
    instantiations: Vec<Instantiation>,
    /// Map from instantiation to proof node ID.
    inst_to_node: FxHashMap<String, ProofNodeId>,
}

impl QuantifierProofRecorder {
    /// Create a new quantifier proof recorder.
    #[must_use]
    pub fn new() -> Self {
        Self {
            instantiations: Vec::new(),
            inst_to_node: FxHashMap::default(),
        }
    }

    /// Record a forall instantiation.
    ///
    /// Given a formula ∀x. φ(x) and a substitution for `x`, records the
    /// instantiation φ(t).
    ///
    /// The instantiated conclusion is always computed *from* `substitution`
    /// (via the same logic as [`Instantiation::apply_substitution`]), not
    /// supplied separately by the caller: an earlier version of this method
    /// took the instantiated string as a second, independent argument, which
    /// meant a caller could pass a `substitution` that had nothing to do
    /// with the `instantiated` string actually recorded, and nothing
    /// checked the two agreed. Deriving it here instead makes that
    /// particular mismatch unwritable rather than merely unchecked.
    pub fn record_forall_inst(
        &mut self,
        proof: &mut Proof,
        formula: QuantifiedFormula,
        substitution: Substitution,
    ) -> ProofNodeId {
        let instantiated = substitute(formula.body(), &substitution);

        // Check if we already have this instantiation
        if let Some(&node_id) = self.inst_to_node.get(&instantiated) {
            return node_id;
        }

        let inst = Instantiation::new(formula, substitution, instantiated.clone());

        // Create a proof node for the instantiation
        let node_id = proof.add_inference(
            "forall_inst",
            Vec::new(),
            format!("(=> {} {})", inst.formula, inst.instantiated),
        );

        self.instantiations.push(inst);
        self.inst_to_node.insert(instantiated, node_id);

        node_id
    }

    /// Record an exists introduction.
    ///
    /// Given a formula ∃x. φ(x), a witness substitution for `x`, and a
    /// `premise` node establishing φ(t) for that witness, records the
    /// derivation of ∃x. φ(x) from it.
    ///
    /// # Errors
    ///
    /// Returns [`QuantifierProofError::MissingPremise`] if `premise` does
    /// not name a node of `proof`, or
    /// [`QuantifierProofError::WitnessMismatch`] if `premise`'s conclusion
    /// is not exactly the witness-instantiated body. An earlier version of
    /// this method computed the witness-instantiated body and then never
    /// used it for anything (not even to validate `premise`, let alone to
    /// record it) -- the entire point of exists-introduction is that the
    /// *specific* premise given is what licenses the conclusion, so
    /// silently accepting an unrelated premise made the rule vacuous rather
    /// than restrict what "record_exists_intro" claims to a check.
    pub fn record_exists_intro(
        &mut self,
        proof: &mut Proof,
        formula: QuantifiedFormula,
        witness: Substitution,
        premise: ProofNodeId,
    ) -> Result<ProofNodeId, QuantifierProofError> {
        let instantiated = substitute(formula.body(), &witness);

        let premise_node = proof
            .get_node(premise)
            .ok_or(QuantifierProofError::MissingPremise(premise))?;
        if premise_node.conclusion() != instantiated {
            return Err(QuantifierProofError::WitnessMismatch {
                expected: instantiated,
                found: premise_node.conclusion().to_string(),
            });
        }

        Ok(proof.add_inference(
            "exists_intro",
            vec![premise],
            format!("(=> {instantiated} {formula})"),
        ))
    }

    /// Record a skolemization step.
    ///
    /// Replaces an existential quantifier with a Skolem function/constant.
    ///
    /// # Errors
    ///
    /// Returns [`QuantifierProofError::SkolemArityMismatch`] if
    /// `skolem_terms` does not have exactly one term per bound variable of
    /// `formula` -- there is otherwise no well-defined correspondence
    /// between them, and the previous unchecked version simply embedded
    /// whichever counts were given via `{:?}` formatting.
    pub fn record_skolemization(
        &mut self,
        proof: &mut Proof,
        formula: QuantifiedFormula,
        skolem_terms: Vec<String>,
    ) -> Result<ProofNodeId, QuantifierProofError> {
        if skolem_terms.len() != formula.vars().len() {
            return Err(QuantifierProofError::SkolemArityMismatch {
                vars: formula.vars().len(),
                terms: skolem_terms.len(),
            });
        }
        Ok(proof.add_inference(
            "skolem",
            Vec::new(),
            format!("(skolem {} {:?})", formula, skolem_terms),
        ))
    }

    /// Get the number of recorded instantiations.
    #[must_use]
    pub fn len(&self) -> usize {
        self.instantiations.len()
    }

    /// Check if there are no recorded instantiations.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.instantiations.is_empty()
    }

    /// Get all recorded instantiations.
    #[must_use]
    pub fn instantiations(&self) -> &[Instantiation] {
        &self.instantiations
    }

    /// Clear all recorded instantiations.
    pub fn clear(&mut self) {
        self.instantiations.clear();
        self.inst_to_node.clear();
    }
}

/// E-matching pattern for quantifier instantiation.
///
/// E-matching is a technique for finding instantiations of quantified formulas
/// by pattern matching against the ground terms in the current context.
#[derive(Debug, Clone)]
pub struct EMatchPattern {
    /// Pattern to match (with variables).
    pub pattern: String,
    /// Variables in the pattern.
    pub vars: Vec<String>,
}

impl EMatchPattern {
    /// Create a new e-matching pattern.
    #[must_use]
    pub fn new(pattern: impl Into<String>, vars: Vec<String>) -> Self {
        Self {
            pattern: pattern.into(),
            vars,
        }
    }

    /// Check if this pattern matches a ground term.
    ///
    /// Both `self.pattern` and `term` are parsed as S-expressions (a
    /// parenthesized prefix syntax, e.g. `(f x (g y))`), and the pattern is
    /// unified against the term: pattern atoms listed in `self.vars` are
    /// treated as variables that bind to whatever subterm occupies their
    /// position (consistently -- the same variable must bind to the same
    /// subterm everywhere it occurs), non-variable atoms must match the
    /// term atom exactly, and compound terms must match functor arity
    /// (list length) and recursively unify every argument.
    ///
    /// Returns the resulting substitution if the pattern matches, or `None`
    /// if the pattern and term cannot be unified (or either fails to parse
    /// as a well-formed S-expression).
    #[must_use]
    pub fn matches(&self, term: &str) -> Option<Substitution> {
        let pattern_expr = SExpr::parse(&self.pattern)?;
        let term_expr = SExpr::parse(term)?;

        let vars: std::collections::HashSet<&str> = self.vars.iter().map(String::as_str).collect();
        let mut subst = Substitution::default();

        if Self::unify(&pattern_expr, &term_expr, &vars, &mut subst) {
            Some(subst)
        } else {
            None
        }
    }

    /// Unify `pattern` against `term`, extending `subst` with any new variable
    /// bindings. Returns `false` (leaving `subst` in an unspecified but still
    /// valid state) on a mismatch.
    ///
    /// Iterative (explicit worklist of pattern/term pairs). Patterns and terms
    /// come from caller-supplied strings whose S-expression nesting is not
    /// bounded by anything this crate controls, and this walk has no error
    /// channel to report a depth cap through -- `false` would mean "does not
    /// match", silently losing instantiations -- so the pairs still to be
    /// unified live on the heap instead of the native stack.
    ///
    /// Argument pairs are pushed in reverse so they are visited left to right,
    /// matching the short-circuiting order of the original `zip(..).all(..)`:
    /// the first mismatching argument stops the walk, and the bindings made
    /// before it are exactly the ones the recursive version would have made.
    fn unify(
        pattern: &SExpr,
        term: &SExpr,
        vars: &std::collections::HashSet<&str>,
        subst: &mut Substitution,
    ) -> bool {
        let mut worklist = vec![(pattern, term)];

        while let Some((pattern, term)) = worklist.pop() {
            match pattern {
                SExpr::Atom(name) if vars.contains(name.as_str()) => {
                    let term_repr = term.to_string_repr();
                    match subst.get(name) {
                        // Same variable bound again: must bind to the same subterm.
                        Some(existing) => {
                            if *existing != term_repr {
                                return false;
                            }
                        }
                        None => {
                            subst.insert(name.clone(), term_repr);
                        }
                    }
                }
                SExpr::Atom(name) => {
                    if !matches!(term, SExpr::Atom(other) if name == other) {
                        return false;
                    }
                }
                SExpr::List(pattern_args) => match term {
                    SExpr::List(term_args) if pattern_args.len() == term_args.len() => {
                        worklist.extend(pattern_args.iter().zip(term_args.iter()).rev());
                    }
                    _ => return false,
                },
            }
        }

        true
    }
}

/// A minimal S-expression (parenthesized prefix syntax) parser used by
/// [`EMatchPattern::matches`] for structural e-matching.
///
/// # Depth invariant
///
/// There is deliberately no bound on how deep a parsed `SExpr` may be:
/// [`SExpr::parse`] is fed caller-supplied pattern and term strings, and
/// rejecting a deep one would silently turn into "the pattern does not match",
/// losing quantifier instantiations rather than reporting anything. Every walk
/// over this type is therefore iterative -- [`SExpr::parse_tokens`],
/// [`SExpr::to_string_repr`], [`EMatchPattern::unify`] and the [`Drop`] impl
/// below.
///
/// No trait is derived for the same reason: the compiler-generated `Debug`,
/// `Clone`, `PartialEq` and `Hash` walks are all recursive, so deriving one
/// would reintroduce an unbounded native-stack walk over a value whose depth
/// is attacker-controlled. Add an iterative hand-written impl if one is ever
/// needed.
enum SExpr {
    /// A single symbol (variable, constant, or function name).
    Atom(String),
    /// A parenthesized application, e.g. `(f a b)`.
    List(Vec<SExpr>),
}

impl Drop for SExpr {
    /// Iterative drop.
    ///
    /// [`SExpr::parse`] builds one nesting level per `(` in the input, so the
    /// compiler-generated recursive `drop_in_place` would overflow the stack on
    /// a deeply nested pattern -- after [`EMatchPattern::matches`] has already
    /// returned its answer, making it an abort with no diagnostic. Each node is
    /// dismantled into a shallow shell before being released, so the drop that
    /// runs for real is never more than one level deep.
    fn drop(&mut self) {
        /// Detach a node's children, leaving a shell that drops trivially.
        fn dismantle(node: &mut SExpr, out: &mut Vec<SExpr>) {
            match node {
                SExpr::Atom(_) => {}
                SExpr::List(items) => out.append(items),
            }
        }

        let mut pending = Vec::new();
        dismantle(self, &mut pending);
        while let Some(mut node) = pending.pop() {
            dismantle(&mut node, &mut pending);
        }
    }
}

impl SExpr {
    /// Parse a whole string as a single S-expression. Returns `None` if the
    /// input is empty, unbalanced, or contains trailing tokens after the
    /// first complete expression.
    fn parse(input: &str) -> Option<Self> {
        let tokens = Self::tokenize(input);
        let mut iter = tokens.iter().peekable();
        let expr = Self::parse_tokens(&mut iter)?;
        if iter.next().is_some() {
            return None;
        }
        Some(expr)
    }

    /// Split input into `(`, `)`, and whitespace-delimited atom tokens.
    fn tokenize(input: &str) -> Vec<String> {
        let mut tokens = Vec::new();
        let mut chars = input.chars().peekable();

        while let Some(&c) = chars.peek() {
            if c == '(' || c == ')' {
                tokens.push(c.to_string());
                chars.next();
            } else if c.is_whitespace() {
                chars.next();
            } else {
                let mut atom = String::new();
                while let Some(&c) = chars.peek() {
                    if c == '(' || c == ')' || c.is_whitespace() {
                        break;
                    }
                    atom.push(c);
                    chars.next();
                }
                tokens.push(atom);
            }
        }

        tokens
    }

    /// Parse one complete S-expression off the front of `iter`.
    ///
    /// Iterative (explicit heap stack of the lists currently open): the input
    /// is caller-supplied text where every `(` costs one nesting level, so a
    /// call frame per level would overflow the native stack. Behaviour is
    /// unchanged, including both `None` cases -- an unmatched `)` and running
    /// out of tokens inside an open list.
    fn parse_tokens<'a, I>(iter: &mut std::iter::Peekable<I>) -> Option<Self>
    where
        I: Iterator<Item = &'a String>,
    {
        // Arguments accumulated for each list that is currently open.
        let mut open: Vec<Vec<Self>> = Vec::new();

        loop {
            let value = match iter.next()?.as_str() {
                "(" => {
                    open.push(Vec::new());
                    continue;
                }
                // A closing paren finishes the innermost open list; with none
                // open it is an unexpected closing paren with no matching open.
                ")" => Self::List(open.pop()?),
                atom => Self::Atom(atom.to_string()),
            };

            match open.last_mut() {
                Some(items) => items.push(value),
                None => return Some(value),
            }
        }
    }

    /// Render back to the same parenthesized textual form used by patterns
    /// and terms elsewhere in this module.
    ///
    /// Iterative (explicit heap stack). Output is byte-identical to the
    /// recursive formulation; see the type-level depth invariant.
    fn to_string_repr(&self) -> String {
        /// Work item for the iterative rendering below.
        enum Task<'a> {
            /// Render this subexpression.
            Node(&'a SExpr),
            /// Emit a structural token verbatim.
            Text(&'static str),
        }

        let mut out = String::new();
        let mut stack = vec![Task::Node(self)];

        while let Some(task) = stack.pop() {
            match task {
                Task::Text(text) => out.push_str(text),
                Task::Node(SExpr::Atom(a)) => out.push_str(a),
                Task::Node(SExpr::List(items)) => {
                    out.push('(');
                    stack.push(Task::Text(")"));
                    for (i, item) in items.iter().enumerate().rev() {
                        stack.push(Task::Node(item));
                        if i > 0 {
                            stack.push(Task::Text(" "));
                        }
                    }
                }
            }
        }

        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_quant_var_creation() {
        let var = QuantVar::new("x", "Int");
        assert_eq!(var.name, "x");
        assert_eq!(var.sort, "Int");
        assert_eq!(format!("{}", var), "(x Int)");
    }

    #[test]
    fn test_forall_formula() {
        let vars = vec![QuantVar::new("x", "Int")];
        let formula = QuantifiedFormula::forall(vars, "(> x 0)");

        assert!(formula.is_forall());
        assert!(!formula.is_exists());
        assert_eq!(formula.body(), "(> x 0)");
        assert_eq!(formula.vars().len(), 1);

        let display = format!("{}", formula);
        assert!(display.contains("forall"));
        assert!(display.contains("x Int"));
    }

    #[test]
    fn test_exists_formula() {
        let vars = vec![QuantVar::new("y", "Real")];
        let formula = QuantifiedFormula::exists(vars, "(= y 5.0)");

        assert!(!formula.is_forall());
        assert!(formula.is_exists());
        assert_eq!(formula.body(), "(= y 5.0)");

        let display = format!("{}", formula);
        assert!(display.contains("exists"));
    }

    #[test]
    fn test_instantiation_creation() {
        let vars = vec![QuantVar::new("x", "Int")];
        let formula = QuantifiedFormula::forall(vars, "(> x 0)");

        let mut sub = Substitution::default();
        sub.insert("x".to_string(), "5".to_string());

        let inst = Instantiation::new(formula, sub, "(> 5 0)");
        assert_eq!(inst.instantiated, "(> 5 0)");
    }

    #[test]
    fn test_instantiation_apply() {
        let vars = vec![QuantVar::new("x", "Int")];
        let formula = QuantifiedFormula::forall(vars, "(> x 0)");

        let mut sub = Substitution::default();
        sub.insert("x".to_string(), "42".to_string());

        let inst = Instantiation::new(formula, sub, "(> 42 0)");
        let result = inst.apply_substitution();
        assert!(result.contains("42"));
    }

    #[test]
    fn test_quantifier_recorder_forall() {
        let mut recorder = QuantifierProofRecorder::new();
        let mut proof = Proof::new();
        proof.add_axiom("true");

        let vars = vec![QuantVar::new("x", "Int")];
        let formula = QuantifiedFormula::forall(vars, "(> x 0)");

        let mut sub = Substitution::default();
        sub.insert("x".to_string(), "5".to_string());

        let node = recorder.record_forall_inst(&mut proof, formula, sub);

        assert_eq!(recorder.len(), 1);
        assert!(!recorder.is_empty());
        // The instantiated conclusion is computed from the substitution, not
        // separately supplied -- confirm it actually reflects it.
        let conclusion = proof
            .get_node(node)
            .expect("just-added node must exist")
            .conclusion();
        assert!(conclusion.contains("(> 5 0)"));
    }

    #[test]
    fn test_quantifier_recorder_exists() {
        let mut recorder = QuantifierProofRecorder::new();
        let mut proof = Proof::new();
        proof.add_axiom("(> 5 0)");
        let root = proof.root().expect("test operation should succeed");

        let vars = vec![QuantVar::new("x", "Int")];
        let formula = QuantifiedFormula::exists(vars, "(> x 0)");

        let mut witness = Substitution::default();
        witness.insert("x".to_string(), "5".to_string());

        let _node = recorder
            .record_exists_intro(&mut proof, formula, witness, root)
            .expect("premise (> 5 0) genuinely witnesses (exists x (> x 0)) at x = 5");

        assert_eq!(proof.node_count(), 2);
    }

    /// The bug this method's "# Errors" doc comment documents: a premise
    /// that does not actually establish the witness-instantiated body must
    /// be rejected, not silently accepted as if it did.
    #[test]
    fn test_quantifier_recorder_exists_rejects_mismatched_witness() {
        let mut recorder = QuantifierProofRecorder::new();
        let mut proof = Proof::new();
        // Premise establishes (> 5 0), but the witness below claims x = 7,
        // i.e. the instantiated body should be (> 7 0) -- a different
        // conclusion the premise does not actually establish.
        proof.add_axiom("(> 5 0)");
        let root = proof.root().expect("test operation should succeed");

        let vars = vec![QuantVar::new("x", "Int")];
        let formula = QuantifiedFormula::exists(vars, "(> x 0)");

        let mut witness = Substitution::default();
        witness.insert("x".to_string(), "7".to_string());

        let result = recorder.record_exists_intro(&mut proof, formula, witness, root);
        assert!(
            matches!(result, Err(QuantifierProofError::WitnessMismatch { .. })),
            "a premise that does not establish the witness-instantiated body \
             must be rejected: {result:?}"
        );
    }

    /// Companion: a `premise` that does not exist in `proof` at all must
    /// also be rejected, not (for instance) panic or fabricate a match.
    #[test]
    fn test_quantifier_recorder_exists_rejects_missing_premise() {
        let mut recorder = QuantifierProofRecorder::new();
        let mut proof = Proof::new();
        proof.add_axiom("(> 5 0)");

        let vars = vec![QuantVar::new("x", "Int")];
        let formula = QuantifiedFormula::exists(vars, "(> x 0)");
        let mut witness = Substitution::default();
        witness.insert("x".to_string(), "5".to_string());

        // A node ID from nowhere: this proof only ever had one node added,
        // at ID 0.
        let bogus_premise = ProofNodeId(9999);
        let result = recorder.record_exists_intro(&mut proof, formula, witness, bogus_premise);
        assert!(
            matches!(result, Err(QuantifierProofError::MissingPremise(_))),
            "a nonexistent premise must be rejected: {result:?}"
        );
    }

    #[test]
    fn test_quantifier_recorder_skolem() {
        let mut recorder = QuantifierProofRecorder::new();
        let mut proof = Proof::new();
        proof.add_axiom("true");

        let vars = vec![QuantVar::new("x", "Int")];
        let formula = QuantifiedFormula::exists(vars, "(> x 0)");

        let _node = recorder
            .record_skolemization(&mut proof, formula, vec!["sk_x".to_string()])
            .expect("one Skolem term for one bound variable must be accepted");

        assert_eq!(proof.node_count(), 2);
    }

    /// The bug this method's "# Errors" doc comment documents: a Skolem-term
    /// count that does not match the existential's bound-variable count
    /// must be rejected, not silently embedded via `{:?}` regardless.
    #[test]
    fn test_quantifier_recorder_skolem_rejects_arity_mismatch() {
        let mut recorder = QuantifierProofRecorder::new();
        let mut proof = Proof::new();
        proof.add_axiom("true");

        let vars = vec![QuantVar::new("x", "Int"), QuantVar::new("y", "Int")];
        let formula = QuantifiedFormula::exists(vars, "(> (+ x y) 0)");

        // Two bound variables, only one Skolem term supplied.
        let result = recorder.record_skolemization(&mut proof, formula, vec!["sk_x".to_string()]);
        assert!(
            matches!(
                result,
                Err(QuantifierProofError::SkolemArityMismatch { vars: 2, terms: 1 })
            ),
            "a Skolem-term/bound-variable arity mismatch must be rejected: {result:?}"
        );
    }

    #[test]
    fn test_quantifier_recorder_dedup() {
        let mut recorder = QuantifierProofRecorder::new();
        let mut proof = Proof::new();
        proof.add_axiom("true");

        let vars = vec![QuantVar::new("x", "Int")];
        let formula = QuantifiedFormula::forall(vars.clone(), "(> x 0)");

        let mut sub = Substitution::default();
        sub.insert("x".to_string(), "5".to_string());

        let node1 = recorder.record_forall_inst(&mut proof, formula.clone(), sub.clone());
        let formula2 = QuantifiedFormula::forall(vars, "(> x 0)");
        let node2 = recorder.record_forall_inst(&mut proof, formula2, sub);

        assert_eq!(node1, node2);
        assert_eq!(recorder.len(), 1);
    }

    #[test]
    fn test_quantifier_recorder_clear() {
        let mut recorder = QuantifierProofRecorder::new();
        let mut proof = Proof::new();
        proof.add_axiom("true");

        let vars = vec![QuantVar::new("x", "Int")];
        let formula = QuantifiedFormula::forall(vars, "(> x 0)");

        let mut sub = Substitution::default();
        sub.insert("x".to_string(), "5".to_string());

        recorder.record_forall_inst(&mut proof, formula, sub);
        assert_eq!(recorder.len(), 1);

        recorder.clear();
        assert_eq!(recorder.len(), 0);
        assert!(recorder.is_empty());
    }

    #[test]
    fn test_ematch_pattern_creation() {
        let pattern = EMatchPattern::new("(f x)", vec!["x".to_string()]);
        assert_eq!(pattern.pattern, "(f x)");
        assert_eq!(pattern.vars.len(), 1);
    }

    #[test]
    fn test_ematch_simple_var_binding() {
        // PF-05 regression: e-matching must actually unify, not always
        // return None.
        let pattern = EMatchPattern::new("(f x)", vec!["x".to_string()]);
        let subst = pattern
            .matches("(f a)")
            .expect("pattern (f x) should match ground term (f a)");
        assert_eq!(subst.get("x").map(String::as_str), Some("a"));
    }

    #[test]
    fn test_ematch_nested_term() {
        let pattern = EMatchPattern::new("(f x)", vec!["x".to_string()]);
        let subst = pattern
            .matches("(f (g a b))")
            .expect("pattern (f x) should match a compound argument");
        assert_eq!(subst.get("x").map(String::as_str), Some("(g a b)"));
    }

    #[test]
    fn test_ematch_functor_mismatch_fails() {
        let pattern = EMatchPattern::new("(f x)", vec!["x".to_string()]);
        assert!(pattern.matches("(g a)").is_none());
    }

    #[test]
    fn test_ematch_arity_mismatch_fails() {
        let pattern = EMatchPattern::new("(f x)", vec!["x".to_string()]);
        assert!(pattern.matches("(f a b)").is_none());
    }

    #[test]
    fn test_ematch_repeated_var_must_be_consistent() {
        // (f x x) only matches ground terms whose two arguments are equal.
        let pattern = EMatchPattern::new("(f x x)", vec!["x".to_string()]);
        assert!(pattern.matches("(f a a)").is_some());
        assert!(pattern.matches("(f a b)").is_none());
    }

    #[test]
    fn test_ematch_multiple_vars_and_constants() {
        let pattern = EMatchPattern::new("(h x c y)", vec!["x".to_string(), "y".to_string()]);
        let subst = pattern
            .matches("(h a c b)")
            .expect("constants must match literally while x, y bind");
        assert_eq!(subst.get("x").map(String::as_str), Some("a"));
        assert_eq!(subst.get("y").map(String::as_str), Some("b"));

        // A mismatched literal constant position must fail.
        assert!(pattern.matches("(h a d b)").is_none());
    }

    #[test]
    fn test_ematch_malformed_input_fails_gracefully() {
        let pattern = EMatchPattern::new("(f x)", vec!["x".to_string()]);
        assert!(pattern.matches("(f a").is_none());
        assert!(pattern.matches("f a)").is_none());
    }

    /// Build `(f (f ... (f a) ...))` nested `depth` levels deep.
    #[cfg(test)]
    fn nested_sexpr(depth: usize, leaf: &str) -> String {
        let mut s = String::with_capacity(depth * 4 + leaf.len() + 1);
        for _ in 0..depth {
            s.push_str("(f ");
        }
        s.push_str(leaf);
        for _ in 0..depth {
            s.push(')');
        }
        s
    }

    /// A deeply nested pattern/term pair must unify without overflowing the
    /// native stack: `SExpr::parse_tokens`, `EMatchPattern::unify`,
    /// `SExpr::to_string_repr` and `SExpr`'s `Drop` are all iterative.
    ///
    /// Running on a deliberately small (128 KiB) stack: returning at all is the
    /// proof. Every one of those four walks used to be recursive, so this
    /// covers all of them at once -- the binding for `x` is produced by
    /// `to_string_repr`, and both parsed trees are dropped on the way out.
    ///
    /// The stack size and `DEPTH` are scaled together on purpose: what is
    /// pinned is the ratio, ~21 bytes per frame, which no real call frame fits
    /// into. Never raise one without raising the other.
    #[test]
    fn test_ematch_deeply_nested_does_not_overflow() {
        const DEPTH: usize = 6_250;

        let handle = std::thread::Builder::new()
            .stack_size(1 << 17)
            .spawn(|| {
                let pattern = EMatchPattern::new(nested_sexpr(DEPTH, "x"), vec!["x".to_string()]);
                let term = nested_sexpr(DEPTH, "a");

                let subst = pattern
                    .matches(&term)
                    .expect("a deeply nested term should match its own shape");
                assert_eq!(subst.get("x").map(String::as_str), Some("a"));

                // A mismatch buried at the bottom must be reported, not lost.
                let mismatch = nested_sexpr(DEPTH, "(g a)");
                let unbound = EMatchPattern::new(nested_sexpr(DEPTH, "b"), Vec::new());
                assert!(unbound.matches(&mismatch).is_none());
            })
            .expect("thread spawn should succeed");

        handle.join().expect("worker thread should not panic");
    }

    /// A deeply nested *binding* exercises `to_string_repr` on a big subterm:
    /// the variable binds to the whole nested tail, which must be rendered
    /// iteratively.
    ///
    /// Same 128 KiB / `DEPTH` pairing as above: the ~21 bytes-per-frame ratio is
    /// what makes a surviving native recursion impossible.
    #[test]
    fn test_ematch_deep_binding_is_rendered_iteratively() {
        const DEPTH: usize = 6_250;

        let handle = std::thread::Builder::new()
            .stack_size(1 << 17)
            .spawn(|| {
                let pattern = EMatchPattern::new("(f x)", vec!["x".to_string()]);
                let term = format!("(f {})", nested_sexpr(DEPTH, "a"));

                let subst = pattern.matches(&term).expect("pattern should match");
                let bound = subst.get("x").cloned().unwrap_or_default();
                assert_eq!(bound, nested_sexpr(DEPTH, "a"));
            })
            .expect("thread spawn should succeed");

        handle.join().expect("worker thread should not panic");
    }

    /// Repeated variables must still be checked for consistency after the
    /// conversion to a worklist, including when the second occurrence is
    /// reached only after other arguments have already bound.
    #[test]
    fn test_ematch_worklist_preserves_left_to_right_binding() {
        let pattern = EMatchPattern::new("(f x (g x) y)", vec!["x".to_string(), "y".to_string()]);

        let subst = pattern
            .matches("(f a (g a) (h b))")
            .expect("consistent bindings should unify");
        assert_eq!(subst.get("x").map(String::as_str), Some("a"));
        assert_eq!(subst.get("y").map(String::as_str), Some("(h b)"));

        // Inconsistent second occurrence of `x`.
        assert!(pattern.matches("(f a (g c) (h b))").is_none());
    }

    #[test]
    fn test_multiple_vars() {
        let vars = vec![QuantVar::new("x", "Int"), QuantVar::new("y", "Int")];
        let formula = QuantifiedFormula::forall(vars, "(> (+ x y) 0)");

        assert_eq!(formula.vars().len(), 2);

        let display = format!("{}", formula);
        assert!(display.contains("(x Int)"));
        assert!(display.contains("(y Int)"));
    }
}
