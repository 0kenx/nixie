//! Proof rule definitions and validators.
//!
//! This module provides validation logic for standard proof rules used in SMT solving,
//! including resolution, unit propagation, CNF transformation, and theory-specific rules.

use std::collections::{HashMap, HashSet};
use std::fmt;

/// A literal in a clause (variable index with sign)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Literal {
    /// Variable index
    pub var: u32,
    /// True if positive, false if negated
    pub sign: bool,
}

impl Literal {
    /// Create a positive literal
    #[must_use]
    pub const fn pos(var: u32) -> Self {
        Self { var, sign: true }
    }

    /// Create a negative literal
    #[must_use]
    pub const fn neg(var: u32) -> Self {
        Self { var, sign: false }
    }

    /// Negate this literal
    #[must_use]
    pub const fn negate(self) -> Self {
        Self {
            var: self.var,
            sign: !self.sign,
        }
    }

    /// Check if two literals are complementary
    #[must_use]
    pub const fn is_complementary(self, other: Self) -> bool {
        self.var == other.var && self.sign != other.sign
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.sign {
            write!(f, "{}", self.var)
        } else {
            write!(f, "-{}", self.var)
        }
    }
}

/// A clause (disjunction of literals)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clause {
    /// Literals in the clause
    pub literals: Vec<Literal>,
}

impl Clause {
    /// Create a new clause
    #[must_use]
    pub fn new(literals: Vec<Literal>) -> Self {
        Self { literals }
    }

    /// Create an empty clause (false)
    #[must_use]
    pub const fn empty() -> Self {
        Self {
            literals: Vec::new(),
        }
    }

    /// Create a unit clause
    #[must_use]
    pub fn unit(lit: Literal) -> Self {
        Self {
            literals: vec![lit],
        }
    }

    /// Check if the clause is empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.literals.is_empty()
    }

    /// Check if the clause is a unit clause
    #[must_use]
    pub fn is_unit(&self) -> bool {
        self.literals.len() == 1
    }

    /// Get the unit literal (if this is a unit clause)
    #[must_use]
    pub fn unit_literal(&self) -> Option<Literal> {
        if self.is_unit() {
            self.literals.first().copied()
        } else {
            None
        }
    }

    /// Check if the clause is a tautology
    #[must_use]
    pub fn is_tautology(&self) -> bool {
        let mut seen = HashSet::new();
        for &lit in &self.literals {
            if seen.contains(&lit.negate()) {
                return true;
            }
            seen.insert(lit);
        }
        false
    }

    /// Remove duplicate literals
    pub fn normalize(&mut self) {
        let mut seen = HashSet::new();
        self.literals.retain(|&lit| seen.insert(lit));
        self.literals.sort_by_key(|l| (l.var, !l.sign));
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for (i, lit) in self.literals.iter().enumerate() {
            if i > 0 {
                write!(f, " ∨ ")?;
            }
            write!(f, "{}", lit)?;
        }
        write!(f, "]")
    }
}

/// Result of rule validation
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuleValidation {
    /// Rule application is valid
    Valid,
    /// Rule application is invalid (with a reason)
    Invalid(String),
    /// The validator could not determine validity, e.g. because its inputs
    /// could not be parsed into the structure it knows how to check. This is
    /// distinct from `Invalid`: it means "not certified", not "certified
    /// wrong" -- callers must not treat it as proof of either validity or
    /// invalidity.
    Unchecked(String),
}

impl RuleValidation {
    /// Check if the validation is successful
    #[must_use]
    pub const fn is_valid(&self) -> bool {
        matches!(self, Self::Valid)
    }

    /// Check if the validation determined the rule application is invalid.
    #[must_use]
    pub const fn is_invalid(&self) -> bool {
        matches!(self, Self::Invalid(_))
    }

    /// Check if the validator could not determine validity.
    #[must_use]
    pub const fn is_unchecked(&self) -> bool {
        matches!(self, Self::Unchecked(_))
    }

    /// Get the error/explanation message (if not `Valid`)
    #[must_use]
    pub fn error(&self) -> Option<&str> {
        match self {
            Self::Invalid(msg) | Self::Unchecked(msg) => Some(msg),
            Self::Valid => None,
        }
    }
}

/// Resolution rule validator
pub struct ResolutionValidator;

impl ResolutionValidator {
    /// Validate a resolution step
    ///
    /// Resolution: C1 ∨ x, C2 ∨ ¬x ⊢ C1 ∨ C2
    #[must_use]
    pub fn validate(c1: &Clause, c2: &Clause, pivot: Literal, result: &Clause) -> RuleValidation {
        // Find the pivot literal in c1 and its negation in c2
        let has_pivot_in_c1 = c1.literals.contains(&pivot);
        let has_neg_pivot_in_c2 = c2.literals.contains(&pivot.negate());

        if !has_pivot_in_c1 {
            return RuleValidation::Invalid(format!("Pivot {} not found in first clause", pivot));
        }

        if !has_neg_pivot_in_c2 {
            return RuleValidation::Invalid(format!(
                "Negated pivot {} not found in second clause",
                pivot.negate()
            ));
        }

        // Build expected resolvent
        let mut expected = Vec::new();
        for &lit in &c1.literals {
            if lit != pivot {
                expected.push(lit);
            }
        }
        for &lit in &c2.literals {
            if lit != pivot.negate() {
                expected.push(lit);
            }
        }

        // Normalize and compare
        let mut expected_clause = Clause::new(expected);
        expected_clause.normalize();

        let mut result_normalized = result.clone();
        result_normalized.normalize();

        if expected_clause == result_normalized {
            RuleValidation::Valid
        } else {
            RuleValidation::Invalid(format!(
                "Expected resolvent {}, got {}",
                expected_clause, result_normalized
            ))
        }
    }
}

/// Unit propagation validator
pub struct UnitPropagationValidator;

impl UnitPropagationValidator {
    /// Validate a unit propagation step
    ///
    /// Unit propagation: C ∨ x, ¬x ⊢ C
    #[must_use]
    pub fn validate(clause: &Clause, unit: Literal, result: &Clause) -> RuleValidation {
        // Check that unit is indeed a literal
        let neg_unit = unit.negate();

        // Build expected result (clause with neg_unit removed)
        let expected: Vec<Literal> = clause
            .literals
            .iter()
            .copied()
            .filter(|&lit| lit != neg_unit)
            .collect();

        if expected.len() == clause.literals.len() {
            return RuleValidation::Invalid(format!(
                "Unit literal {} not found in clause",
                neg_unit
            ));
        }

        let mut expected_clause = Clause::new(expected);
        expected_clause.normalize();

        let mut result_normalized = result.clone();
        result_normalized.normalize();

        if expected_clause == result_normalized {
            RuleValidation::Valid
        } else {
            RuleValidation::Invalid(format!(
                "Expected {}, got {}",
                expected_clause, result_normalized
            ))
        }
    }
}

// ============================================================================
// Minimal propositional formula parser (shared by the CNF validators below)
// ============================================================================

/// A tiny propositional formula, parsed from the `¬`/`∧`/`∨` textual notation
/// used by this crate's CNF transformation validators.
///
/// # Depth invariant
///
/// There is deliberately no bound on how deep a `Formula` may be:
/// [`parse_formula`] is iterative and adds one nesting level per leading `¬` in
/// its (untrusted, caller-supplied) input, so depth is attacker-controlled and
/// rejecting deep input would just turn a validator verdict into `Unchecked`.
/// Every walk over this type is therefore iterative -- [`parse_formula`],
/// [`Clone`], [`Drop`], [`fmt::Display`] and [`formula_equiv`].
///
/// `PartialEq`/`Eq` are deliberately *not* derived: the derived comparison is
/// recursive, and [`formula_equiv`] is the iterative comparison this module
/// actually uses. Only the derived [`fmt::Debug`] is still recursive; it is
/// used solely for diagnostics on small values.
#[derive(Debug)]
enum Formula {
    Atom(String),
    Not(Box<Formula>),
    And(Vec<Formula>),
    Or(Vec<Formula>),
}

impl Drop for Formula {
    /// Iterative drop.
    ///
    /// [`parse_formula`] is iterative, so it happily builds a `¬`-chain one
    /// level deep per input character. The compiler-generated recursive
    /// `drop_in_place` would then overflow the stack when that formula goes out
    /// of scope — after the validator has already returned its verdict, which
    /// makes it a process abort with no diagnostic at all. Each node is
    /// dismantled into a shallow shell before being released, so the drop that
    /// runs for real is never more than a couple of levels deep.
    fn drop(&mut self) {
        /// Detach a node's children, leaving a shell that drops trivially.
        fn dismantle(node: &mut Formula, out: &mut Vec<Formula>) {
            match node {
                Formula::Atom(_) => {}
                Formula::Not(inner) => {
                    out.push(std::mem::replace(
                        inner.as_mut(),
                        Formula::Atom(String::new()),
                    ));
                }
                Formula::And(xs) | Formula::Or(xs) => out.append(xs),
            }
        }

        let mut pending = Vec::new();
        dismantle(self, &mut pending);
        while let Some(mut node) = pending.pop() {
            dismantle(&mut node, &mut pending);
        }
    }
}

/// One in-progress node in the iterative [`Clone`] impl for [`Formula`].
enum FormulaCloneFrame<'a> {
    /// A `¬` whose operand is being cloned.
    Not,
    /// An `∧`/`∨` whose operands are being cloned.
    List {
        /// `true` for `And`, `false` for `Or`.
        is_and: bool,
        /// Operands still to be cloned, in source order.
        rest: std::slice::Iter<'a, Formula>,
        /// Operands cloned so far, in source order.
        done: Vec<Formula>,
    },
}

impl Clone for Formula {
    /// Iterative clone.
    ///
    /// The CNF validators clone whole subformulas while building the formula
    /// they expect (`validate_demorgan_and`, `validate_distributivity`, ...),
    /// and a `Formula` gains one nesting level per leading `¬` in its untrusted
    /// input, so the derived recursive `Clone` could overflow the stack on
    /// exactly the input these validators exist to reject. The result is
    /// structurally identical.
    fn clone(&self) -> Self {
        /// Rebuild a finished `∧`/`∨` node.
        fn finish(is_and: bool, parts: Vec<Formula>) -> Formula {
            if is_and {
                Formula::And(parts)
            } else {
                Formula::Or(parts)
            }
        }

        let mut stack: Vec<FormulaCloneFrame<'_>> = Vec::new();
        let mut node: &Formula = self;

        loop {
            // Descend to the next leaf, opening a frame per compound node.
            let mut value = 'descend: loop {
                match node {
                    Self::Atom(s) => break 'descend Self::Atom(s.clone()),
                    Self::Not(inner) => {
                        stack.push(FormulaCloneFrame::Not);
                        node = inner.as_ref();
                        continue 'descend;
                    }
                    Self::And(parts) | Self::Or(parts) => {
                        let is_and = matches!(node, Self::And(_));
                        let mut rest = parts.iter();
                        match rest.next() {
                            Some(first) => {
                                stack.push(FormulaCloneFrame::List {
                                    is_and,
                                    rest,
                                    done: Vec::new(),
                                });
                                node = first;
                                continue 'descend;
                            }
                            None => break 'descend finish(is_and, Vec::new()),
                        }
                    }
                }
            };

            // Unwind: hand the cloned operand to its parent frame.
            loop {
                let Some(frame) = stack.pop() else {
                    return value;
                };
                match frame {
                    FormulaCloneFrame::Not => value = Self::Not(Box::new(value)),
                    FormulaCloneFrame::List {
                        is_and,
                        mut rest,
                        mut done,
                    } => {
                        done.push(value);
                        match rest.next() {
                            Some(next) => {
                                node = next;
                                stack.push(FormulaCloneFrame::List { is_and, rest, done });
                                break;
                            }
                            None => value = finish(is_and, done),
                        }
                    }
                }
            }
        }
    }
}

/// Work item for the iterative [`fmt::Display`] impl for [`Formula`].
enum FormulaFmtTask<'a> {
    /// Render this subformula.
    Node(&'a Formula),
    /// Emit a structural token verbatim.
    Text(&'static str),
}

impl fmt::Display for Formula {
    /// Iterative (explicit heap stack) rendering.
    ///
    /// `Formula` is parsed from untrusted text where `¬` nesting costs one level
    /// per character, so rendering it recursively would overflow on exactly the
    /// inputs the CNF validators are meant to reject. Output is byte-identical
    /// to the recursive formulation.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut stack = vec![FormulaFmtTask::Node(self)];

        while let Some(task) = stack.pop() {
            let node = match task {
                FormulaFmtTask::Text(text) => {
                    f.write_str(text)?;
                    continue;
                }
                FormulaFmtTask::Node(node) => node,
            };

            match node {
                Self::Atom(s) => write!(f, "{s}")?,
                Self::Not(inner) => {
                    f.write_str("¬")?;
                    stack.push(FormulaFmtTask::Node(inner));
                }
                Self::And(xs) | Self::Or(xs) => {
                    let separator = if matches!(node, Self::And(_)) {
                        " ∧ "
                    } else {
                        " ∨ "
                    };
                    f.write_str("(")?;
                    stack.push(FormulaFmtTask::Text(")"));
                    for (i, x) in xs.iter().enumerate().rev() {
                        stack.push(FormulaFmtTask::Node(x));
                        if i > 0 {
                            stack.push(FormulaFmtTask::Text(separator));
                        }
                    }
                }
            }
        }

        Ok(())
    }
}

/// Parse a formula in `¬`/`(A ∧ B ∧ ...)`/`(A ∨ B ∨ ...)` notation.
///
/// Returns `None` on any syntax this minimal parser does not understand --
/// callers must treat that as "cannot certify", not as a parse of `false`.
fn parse_formula(s: &str) -> Option<Formula> {
    let chars: Vec<char> = s.trim().chars().collect();
    let mut pos = 0usize;
    let formula = parse_formula_tokens(&chars, &mut pos)?;
    skip_ws(&chars, &mut pos);
    if pos == chars.len() {
        Some(formula)
    } else {
        None
    }
}

fn skip_ws(chars: &[char], pos: &mut usize) {
    while *pos < chars.len() && chars[*pos].is_whitespace() {
        *pos += 1;
    }
}

/// Pending construction while [`parse_formula_tokens`] descends.
enum ParseFrame {
    /// A `¬` awaiting its operand.
    Negation,
    /// An open `(` group: the parts read so far and the operator seen (if any).
    Group {
        /// Operands parsed so far.
        parts: Vec<Formula>,
        /// The single connective used inside this group.
        op: Option<char>,
    },
}

/// Parse one formula token, leaving `pos` just past it.
///
/// Iterative: `¬¬¬…` and `(((…)))` in untrusted validator input each cost one
/// call frame per character in the recursive formulation. The pending `¬`s and
/// open groups live on an explicit heap stack instead; `None` still means
/// exactly "this minimal parser does not understand the input".
fn parse_formula_tokens(chars: &[char], pos: &mut usize) -> Option<Formula> {
    let mut stack: Vec<ParseFrame> = Vec::new();

    'descend: loop {
        // Consume prefix operators until an atom or a closing group yields a value.
        let mut value = loop {
            skip_ws(chars, pos);
            if *pos >= chars.len() {
                return None;
            }
            match chars[*pos] {
                '¬' => {
                    *pos += 1;
                    stack.push(ParseFrame::Negation);
                }
                '(' => {
                    *pos += 1;
                    stack.push(ParseFrame::Group {
                        parts: Vec::new(),
                        op: None,
                    });
                }
                c if c.is_alphanumeric() || c == '_' => {
                    let start = *pos;
                    while *pos < chars.len()
                        && (chars[*pos].is_alphanumeric() || chars[*pos] == '_')
                    {
                        *pos += 1;
                    }
                    break Formula::Atom(chars[start..*pos].iter().collect());
                }
                _ => return None,
            }
        };

        // Fold the completed value into the enclosing pending frames.
        loop {
            match stack.last_mut() {
                None => return Some(value),
                Some(ParseFrame::Negation) => {
                    stack.pop();
                    value = Formula::Not(Box::new(value));
                }
                Some(ParseFrame::Group { parts, op }) => {
                    parts.push(value);

                    skip_ws(chars, pos);
                    if *pos < chars.len() && (chars[*pos] == '∧' || chars[*pos] == '∨') {
                        let this_op = chars[*pos];
                        match *op {
                            Some(existing) if existing != this_op => return None,
                            _ => *op = Some(this_op),
                        }
                        *pos += 1;
                        continue 'descend;
                    }

                    if *pos >= chars.len() || chars[*pos] != ')' {
                        return None;
                    }
                    *pos += 1;

                    let Some(ParseFrame::Group { parts, op }) = stack.pop() else {
                        return None;
                    };
                    value = match op {
                        None => parts.into_iter().next()?,
                        Some('∧') => Formula::And(parts),
                        Some('∨') => Formula::Or(parts),
                        _ => return None,
                    };
                }
            }
        }
    }
}

/// Structural equivalence under associativity/commutativity of `∧`/`∨` (i.e.
/// treating the argument lists of `And`/`Or` as multisets rather than
/// sequences). This is a syntactic check, not a full semantic equivalence
/// (e.g. it will not recognize `A` as equivalent to `A ∧ A`).
/// Work item for the iterative [`formula_equiv`] machine.
enum EquivFrame<'a> {
    /// Compare two subformulas.
    Compare(&'a Formula, &'a Formula),
    /// Greedy first-fit multiset matching, resumable mid-search.
    Match {
        /// Left-hand operand list.
        xs: &'a [Formula],
        /// Right-hand operand list.
        ys: &'a [Formula],
        /// Which entries of `ys` are already matched.
        used: Vec<bool>,
        /// Index of the `xs` entry currently being matched.
        xi: usize,
        /// Candidate index in `ys` being tried for `xs[xi]`.
        yi: usize,
        /// Whether a `Compare(xs[xi], ys[yi])` result is pending.
        probing: bool,
    },
}

/// Iterative (explicit heap stack) equivalence check.
///
/// `-> bool` has no error channel, so a depth cap here could only produce a
/// silently wrong "equivalent"/"not equivalent" verdict on a proof-rule check.
/// The greedy first-fit matching of the recursive `multiset_equiv` is preserved
/// exactly, with its search position carried in the `Match` frame.
fn formula_equiv(a: &Formula, b: &Formula) -> bool {
    let mut stack = vec![EquivFrame::Compare(a, b)];
    // Result of the most recently completed frame.
    let mut result = false;

    while let Some(frame) = stack.pop() {
        match frame {
            EquivFrame::Compare(x, y) => match (x, y) {
                (Formula::Atom(p), Formula::Atom(q)) => result = p == q,
                (Formula::Not(p), Formula::Not(q)) => stack.push(EquivFrame::Compare(p, q)),
                (Formula::And(xs), Formula::And(ys)) | (Formula::Or(xs), Formula::Or(ys)) => {
                    if xs.len() == ys.len() {
                        stack.push(EquivFrame::Match {
                            xs,
                            ys,
                            used: vec![false; ys.len()],
                            xi: 0,
                            yi: 0,
                            probing: false,
                        });
                    } else {
                        result = false;
                    }
                }
                _ => result = false,
            },
            EquivFrame::Match {
                xs,
                ys,
                mut used,
                mut xi,
                mut yi,
                probing,
            } => {
                if probing {
                    if result {
                        if let Some(slot) = used.get_mut(yi) {
                            *slot = true;
                        }
                        // The recursive version restarted its scan from 0 for
                        // each new x, so do the same here.
                        xi += 1;
                        yi = 0;
                    } else {
                        yi += 1;
                    }
                }

                if xi >= xs.len() {
                    result = true;
                    continue;
                }
                while yi < ys.len() && used.get(yi).copied().unwrap_or(true) {
                    yi += 1;
                }
                if yi >= ys.len() {
                    result = false;
                    continue;
                }

                let x_item = &xs[xi];
                let y_item = &ys[yi];
                stack.push(EquivFrame::Match {
                    xs,
                    ys,
                    used,
                    xi,
                    yi,
                    probing: true,
                });
                stack.push(EquivFrame::Compare(x_item, y_item));
            }
        }
    }

    result
}

/// CNF transformation validator
pub struct CnfValidator;

impl CnfValidator {
    /// Validate negation normal form transformation
    ///
    /// ¬(¬A) ⟺ A
    #[must_use]
    pub fn validate_not_not(input: &str, output: &str) -> RuleValidation {
        if input.starts_with("¬¬") && output == &input[4..] {
            RuleValidation::Valid
        } else {
            RuleValidation::Invalid("Invalid ¬¬ elimination".to_string())
        }
    }

    /// Validate De Morgan's law (AND)
    ///
    /// ¬(A ∧ B) ⟺ ¬A ∨ ¬B
    #[must_use]
    pub fn validate_demorgan_and(input: &str, output: &str) -> RuleValidation {
        let (Some(fi), Some(fo)) = (parse_formula(input), parse_formula(output)) else {
            return RuleValidation::Unchecked(format!(
                "Could not parse formulas for De Morgan (AND) check: {input:?} -> {output:?}"
            ));
        };
        let Formula::Not(inner) = &fi else {
            return RuleValidation::Invalid(format!("Expected a negation as input, got {input}"));
        };
        let Formula::And(conjuncts) = inner.as_ref() else {
            return RuleValidation::Invalid(format!("Expected a negated conjunction, got {input}"));
        };
        let expected = Formula::Or(
            conjuncts
                .iter()
                .cloned()
                .map(|c| Formula::Not(Box::new(c)))
                .collect(),
        );
        if formula_equiv(&expected, &fo) {
            RuleValidation::Valid
        } else {
            RuleValidation::Invalid(format!(
                "De Morgan (AND) mismatch: expected {expected}, got {fo}"
            ))
        }
    }

    /// Validate De Morgan's law (OR)
    ///
    /// ¬(A ∨ B) ⟺ ¬A ∧ ¬B
    #[must_use]
    pub fn validate_demorgan_or(input: &str, output: &str) -> RuleValidation {
        let (Some(fi), Some(fo)) = (parse_formula(input), parse_formula(output)) else {
            return RuleValidation::Unchecked(format!(
                "Could not parse formulas for De Morgan (OR) check: {input:?} -> {output:?}"
            ));
        };
        let Formula::Not(inner) = &fi else {
            return RuleValidation::Invalid(format!("Expected a negation as input, got {input}"));
        };
        let Formula::Or(disjuncts) = inner.as_ref() else {
            return RuleValidation::Invalid(format!("Expected a negated disjunction, got {input}"));
        };
        let expected = Formula::And(
            disjuncts
                .iter()
                .cloned()
                .map(|c| Formula::Not(Box::new(c)))
                .collect(),
        );
        if formula_equiv(&expected, &fo) {
            RuleValidation::Valid
        } else {
            RuleValidation::Invalid(format!(
                "De Morgan (OR) mismatch: expected {expected}, got {fo}"
            ))
        }
    }

    /// Validate distributivity
    ///
    /// A ∨ (B ∧ C) ⟺ (A ∨ B) ∧ (A ∨ C)  (and the symmetric `(B ∧ C) ∨ A` input form)
    #[must_use]
    pub fn validate_distributivity(input: &str, output: &str) -> RuleValidation {
        let (Some(fi), Some(fo)) = (parse_formula(input), parse_formula(output)) else {
            return RuleValidation::Unchecked(format!(
                "Could not parse formulas for distributivity check: {input:?} -> {output:?}"
            ));
        };
        let Formula::Or(disjuncts) = &fi else {
            return RuleValidation::Unchecked(format!(
                "Distributivity check only supports `A ∨ (B ∧ C)` input form; got {input}"
            ));
        };
        if disjuncts.len() != 2 {
            return RuleValidation::Unchecked(format!(
                "Distributivity check only supports binary disjunction input; got {input}"
            ));
        }

        let (other, conjuncts) = match (&disjuncts[0], &disjuncts[1]) {
            (Formula::And(cs), other) | (other, Formula::And(cs)) => (other.clone(), cs.clone()),
            _ => {
                return RuleValidation::Invalid(format!(
                    "Expected `A ∨ (B ∧ C)` form, got {input}"
                ));
            }
        };

        let expected = Formula::And(
            conjuncts
                .into_iter()
                .map(|c| Formula::Or(vec![other.clone(), c]))
                .collect(),
        );

        if formula_equiv(&expected, &fo) {
            RuleValidation::Valid
        } else {
            RuleValidation::Invalid(format!(
                "Distributivity mismatch: expected {expected}, got {fo}"
            ))
        }
    }
}

// ============================================================================
// Minimal linear-arithmetic parser (shared by the Farkas validator)
// ============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CmpOp {
    Le,
    Lt,
    Eq,
    Ge,
    Gt,
}

/// A linear expression `Σ coeff_i * var_i + constant`.
#[derive(Debug, Clone)]
struct LinearExpr {
    coeffs: HashMap<String, f64>,
    constant: f64,
}

/// Parse a flat linear expression such as `x + 2*y - 5` or `3*x - y`.
///
/// Supports terms of the form `[+|-] [coeff '*'] var` or a bare numeric
/// constant. Does not support parentheses or non-linear terms (products of
/// two variables) -- such input causes parsing to fail, returning `None`.
fn parse_linear_expr(s: &str) -> Option<LinearExpr> {
    let s = s.trim();
    if s.is_empty() {
        return None;
    }

    let mut terms: Vec<(f64, String)> = Vec::new();
    let mut current = String::new();
    let mut sign = 1.0f64;
    let mut chars = s.chars().peekable();

    if let Some(&c) = chars.peek() {
        if c == '-' {
            sign = -1.0;
            chars.next();
        } else if c == '+' {
            chars.next();
        }
    }

    for c in chars {
        if c == '+' || c == '-' {
            terms.push((sign, current.trim().to_string()));
            current = String::new();
            sign = if c == '-' { -1.0 } else { 1.0 };
        } else {
            current.push(c);
        }
    }
    terms.push((sign, current.trim().to_string()));

    let mut coeffs: HashMap<String, f64> = HashMap::new();
    let mut constant = 0.0;

    for (term_sign, term) in terms {
        if term.is_empty() {
            continue;
        }
        if term.contains('*') {
            let (coeff_str, var) = term.split_once('*')?;
            let coeff: f64 = coeff_str.trim().parse().ok()?;
            let var = var.trim();
            if var.is_empty() || !var.chars().all(|c| c.is_alphanumeric() || c == '_') {
                return None;
            }
            *coeffs.entry(var.to_string()).or_insert(0.0) += term_sign * coeff;
        } else if let Ok(num) = term.parse::<f64>() {
            constant += term_sign * num;
        } else if term.chars().all(|c| c.is_alphanumeric() || c == '_') {
            *coeffs.entry(term).or_insert(0.0) += term_sign;
        } else {
            return None;
        }
    }

    Some(LinearExpr { coeffs, constant })
}

/// Parse `<linear-expr> <op> <linear-expr>` and normalize to `expr <op> 0`.
fn parse_inequality(s: &str) -> Option<(LinearExpr, CmpOp)> {
    let s = s.trim();
    let (op, op_str) = if s.contains("<=") {
        (CmpOp::Le, "<=")
    } else if s.contains(">=") {
        (CmpOp::Ge, ">=")
    } else if s.contains('<') {
        (CmpOp::Lt, "<")
    } else if s.contains('>') {
        (CmpOp::Gt, ">")
    } else if s.contains('=') {
        (CmpOp::Eq, "=")
    } else {
        return None;
    };

    let idx = s.find(op_str)?;
    let lhs = parse_linear_expr(&s[..idx])?;
    let rhs = parse_linear_expr(&s[idx + op_str.len()..])?;

    let mut combined = lhs;
    for (var, c) in rhs.coeffs {
        *combined.coeffs.entry(var).or_insert(0.0) -= c;
    }
    combined.constant -= rhs.constant;
    Some((combined, op))
}

/// Theory lemma validator
pub struct TheoryLemmaValidator;

impl TheoryLemmaValidator {
    /// Validate an arithmetic Farkas lemma.
    ///
    /// Given inequalities `e_i <op_i> 0` and non-negative multipliers
    /// `coefficients[i]` (unconstrained in sign for equality premises), checks
    /// that the weighted combination `Σ coefficients[i] * e_i` cancels every
    /// variable and leaves a constant that makes the combined inequality
    /// `<combined-op> 0` false -- i.e. a genuine numeric contradiction,
    /// certifying that the original system of inequalities is infeasible.
    #[must_use]
    pub fn validate_farkas(
        inequalities: &[String],
        coefficients: &[f64],
        result: &str,
    ) -> RuleValidation {
        if inequalities.is_empty() {
            return RuleValidation::Invalid(
                "Farkas combination requires at least one inequality".to_string(),
            );
        }
        if inequalities.len() != coefficients.len() {
            return RuleValidation::Invalid(format!(
                "Farkas combination requires one coefficient per inequality: {} inequalities, {} coefficients",
                inequalities.len(),
                coefficients.len()
            ));
        }

        let mut parsed = Vec::with_capacity(inequalities.len());
        for ineq in inequalities {
            match parse_inequality(ineq) {
                Some(p) => parsed.push(p),
                None => {
                    return RuleValidation::Unchecked(format!(
                        "Could not parse linear inequality for Farkas check: {ineq:?}"
                    ));
                }
            }
        }

        for (&c, (_, op)) in coefficients.iter().zip(parsed.iter()) {
            if *op != CmpOp::Eq && c < 0.0 {
                return RuleValidation::Invalid(format!(
                    "Farkas multiplier {c} for an inequality constraint must be non-negative"
                ));
            }
        }

        const EPS: f64 = 1e-9;
        let mut combined_coeffs: HashMap<String, f64> = HashMap::new();
        let mut combined_constant = 0.0;
        let mut combined_strict = false;

        for (&raw_coeff, (expr, op)) in coefficients.iter().zip(parsed.iter()) {
            // Normalize every constraint to `expr <= 0` (or `< 0`, or `= 0`)
            // before combining; `>=`/`>` flip to `<=`/`<` by negation.
            let (coeff, normalized_strict) = match op {
                CmpOp::Le | CmpOp::Eq => (raw_coeff, false),
                CmpOp::Lt => (raw_coeff, true),
                CmpOp::Ge => (-raw_coeff, false),
                CmpOp::Gt => (-raw_coeff, true),
            };
            if normalized_strict && coeff.abs() > EPS {
                combined_strict = true;
            }
            for (var, c) in &expr.coeffs {
                *combined_coeffs.entry(var.clone()).or_insert(0.0) += coeff * c;
            }
            combined_constant += coeff * expr.constant;
        }

        let residual_vars: Vec<_> = combined_coeffs
            .iter()
            .filter(|&(_, &c)| c.abs() > EPS)
            .map(|(v, _)| v.clone())
            .collect();
        if !residual_vars.is_empty() {
            return RuleValidation::Invalid(format!(
                "Farkas combination does not eliminate all variables: residual terms {residual_vars:?}"
            ));
        }

        let is_contradiction = if combined_strict {
            combined_constant >= -EPS
        } else {
            combined_constant > EPS
        };
        if !is_contradiction {
            return RuleValidation::Invalid(format!(
                "Farkas combination does not derive a contradiction: combined constant {combined_constant}"
            ));
        }

        let result_norm = result.trim().to_ascii_lowercase();
        if result_norm != "false" && result_norm != "⊥" && !result_norm.contains("unsat") {
            return RuleValidation::Invalid(format!(
                "Farkas certificate derives a contradiction but result {result:?} does not denote `false`"
            ));
        }

        RuleValidation::Valid
    }

    /// Validate congruence closure.
    ///
    /// Given established equalities and a proposed conclusion
    /// `f(x1, .., xn) = f(y1, .., yn)`, checks that each `xi`/`yi` pair is
    /// either syntactically identical or connected by the transitive closure
    /// of the given equalities.
    #[must_use]
    pub fn validate_congruence(equalities: &[String], result: &str) -> RuleValidation {
        let Some((f_lhs, args_lhs, f_rhs, args_rhs)) = parse_congruence_result(result) else {
            return RuleValidation::Unchecked(format!(
                "Could not parse congruence conclusion as `f(..) = f(..)`: {result:?}"
            ));
        };
        if f_lhs != f_rhs {
            return RuleValidation::Invalid(format!(
                "Congruence conclusion uses different function symbols: {f_lhs} vs {f_rhs}"
            ));
        }
        if args_lhs.len() != args_rhs.len() {
            return RuleValidation::Invalid(format!(
                "Congruence conclusion arity mismatch: {} vs {} arguments",
                args_lhs.len(),
                args_rhs.len()
            ));
        }

        let mut uf = UnionFind::new();
        for eq in equalities {
            let Some((l, r)) = parse_equality(eq) else {
                return RuleValidation::Unchecked(format!(
                    "Could not parse equality premise for congruence check: {eq:?}"
                ));
            };
            uf.union(&l, &r);
        }

        for (x, y) in args_lhs.iter().zip(args_rhs.iter()) {
            if x == y {
                continue;
            }
            if !uf.same_set(x, y) {
                return RuleValidation::Invalid(format!(
                    "Congruence argument mismatch: {x} and {y} are not established equal"
                ));
            }
        }

        RuleValidation::Valid
    }

    /// Validate transitivity of equality.
    ///
    /// `a = b`, `b = c` ⊢ `a = c` (allowing either orientation of each
    /// equality, since `=` is symmetric).
    #[must_use]
    pub fn validate_transitivity(eq1: &str, eq2: &str, result: &str) -> RuleValidation {
        let (Some((a1, b1)), Some((a2, b2)), Some((ar, cr))) = (
            parse_equality(eq1),
            parse_equality(eq2),
            parse_equality(result),
        ) else {
            return RuleValidation::Unchecked(format!(
                "Could not parse equalities for transitivity check: {eq1:?}, {eq2:?}, {result:?}"
            ));
        };

        let candidates = [
            (a1.clone(), b1.clone(), a2.clone(), b2.clone()),
            (a1.clone(), b1.clone(), b2.clone(), a2.clone()),
            (b1.clone(), a1.clone(), a2.clone(), b2.clone()),
            (b1.clone(), a1.clone(), b2.clone(), a2.clone()),
        ];

        for (outer1, mid1, mid2, outer2) in candidates {
            if mid1 != mid2 {
                continue;
            }
            let forward = ar == outer1 && cr == outer2;
            let backward = ar == outer2 && cr == outer1;
            if forward || backward {
                return RuleValidation::Valid;
            }
        }

        RuleValidation::Invalid(format!(
            "Transitivity does not connect {eq1} and {eq2} into {result}"
        ))
    }
}

/// Parse `lhs = rhs`, trimming whitespace on both sides.
fn parse_equality(s: &str) -> Option<(String, String)> {
    let s = s.trim();
    let idx = s.find('=')?;
    let lhs = s[..idx].trim().to_string();
    let rhs = s[idx + 1..].trim().to_string();
    if lhs.is_empty() || rhs.is_empty() {
        return None;
    }
    Some((lhs, rhs))
}

/// Parse `name(arg1, arg2, ...)` or a bare `name` (arity 0).
fn parse_app(s: &str) -> Option<(String, Vec<String>)> {
    let s = s.trim();
    let Some(open) = s.find('(') else {
        if s.is_empty() {
            return None;
        }
        return Some((s.to_string(), Vec::new()));
    };
    if !s.ends_with(')') {
        return None;
    }
    let name = s[..open].trim().to_string();
    if name.is_empty() {
        return None;
    }
    let inner = s[open + 1..s.len() - 1].trim();
    let args: Vec<String> = if inner.is_empty() {
        Vec::new()
    } else {
        split_top_level_commas(inner)
            .into_iter()
            .map(|a| a.trim().to_string())
            .collect()
    };
    if args.iter().any(String::is_empty) {
        return None;
    }
    Some((name, args))
}

fn split_top_level_commas(s: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut start = 0usize;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => depth -= 1,
            ',' if depth == 0 => {
                out.push(&s[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    out.push(&s[start..]);
    out
}

fn parse_congruence_result(s: &str) -> Option<(String, Vec<String>, String, Vec<String>)> {
    let (lhs, rhs) = parse_equality(s)?;
    let (f_lhs, args_lhs) = parse_app(&lhs)?;
    let (f_rhs, args_rhs) = parse_app(&rhs)?;
    Some((f_lhs, args_lhs, f_rhs, args_rhs))
}

/// A minimal union-find over term names, used to compute the transitive
/// closure of a set of equalities for congruence checking.
struct UnionFind {
    parent: HashMap<String, String>,
}

impl UnionFind {
    fn new() -> Self {
        Self {
            parent: HashMap::new(),
        }
    }

    /// Find the representative of `x`, compressing the path on the way back.
    ///
    /// Iterative: `union` inserts without rank, so a chain can grow linearly in
    /// the number of terms, and the first `find` over such a chain recursed once
    /// per link with a `String` clone in every frame. `-> String` gives a depth
    /// cap nowhere to report a truncated walk, and a truncated walk here means a
    /// wrong congruence verdict.
    fn find(&mut self, x: &str) -> String {
        if !self.parent.contains_key(x) {
            self.parent.insert(x.to_string(), x.to_string());
            return x.to_string();
        }

        // Walk to the root, remembering the nodes passed through.
        let mut path: Vec<String> = Vec::new();
        let mut current = x.to_string();
        loop {
            let parent = match self.parent.get(&current) {
                Some(parent) => parent.clone(),
                None => {
                    // Matches the recursive version, which materialized a
                    // self-parent entry for any node it reached.
                    self.parent.insert(current.clone(), current.clone());
                    current.clone()
                }
            };
            if parent == current {
                break;
            }
            path.push(current);
            current = parent;
        }

        // Path compression: every node on the path now points straight at the root.
        for node in path {
            self.parent.insert(node, current.clone());
        }

        current
    }

    fn union(&mut self, a: &str, b: &str) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra != rb {
            self.parent.insert(ra, rb);
        }
    }

    fn same_set(&mut self, a: &str, b: &str) -> bool {
        self.find(a) == self.find(b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_literal_creation() {
        let lit = Literal::pos(5);
        assert_eq!(lit.var, 5);
        assert!(lit.sign);

        let neg_lit = Literal::neg(5);
        assert_eq!(neg_lit.var, 5);
        assert!(!neg_lit.sign);
    }

    #[test]
    fn test_literal_negate() {
        let lit = Literal::pos(3);
        let neg = lit.negate();
        assert_eq!(neg.var, 3);
        assert!(!neg.sign);
    }

    #[test]
    fn test_literal_complementary() {
        let lit1 = Literal::pos(5);
        let lit2 = Literal::neg(5);
        assert!(lit1.is_complementary(lit2));
        assert!(lit2.is_complementary(lit1));

        let lit3 = Literal::pos(6);
        assert!(!lit1.is_complementary(lit3));
    }

    #[test]
    fn test_clause_empty() {
        let clause = Clause::empty();
        assert!(clause.is_empty());
        assert!(!clause.is_unit());
    }

    #[test]
    fn test_clause_unit() {
        let clause = Clause::unit(Literal::pos(1));
        assert!(clause.is_unit());
        assert_eq!(clause.unit_literal(), Some(Literal::pos(1)));
    }

    #[test]
    fn test_clause_tautology() {
        let clause = Clause::new(vec![Literal::pos(1), Literal::neg(1)]);
        assert!(clause.is_tautology());

        let non_taut = Clause::new(vec![Literal::pos(1), Literal::pos(2)]);
        assert!(!non_taut.is_tautology());
    }

    #[test]
    fn test_clause_normalize() {
        let mut clause = Clause::new(vec![
            Literal::pos(2),
            Literal::pos(1),
            Literal::pos(2), // duplicate
        ]);

        clause.normalize();
        assert_eq!(clause.literals.len(), 2);
    }

    #[test]
    fn test_resolution_valid() {
        // (p ∨ q) ∧ (¬p ∨ r) ⊢ (q ∨ r)
        let c1 = Clause::new(vec![Literal::pos(1), Literal::pos(2)]); // p ∨ q
        let c2 = Clause::new(vec![Literal::neg(1), Literal::pos(3)]); // ¬p ∨ r
        let result = Clause::new(vec![Literal::pos(2), Literal::pos(3)]); // q ∨ r
        let pivot = Literal::pos(1); // p

        let validation = ResolutionValidator::validate(&c1, &c2, pivot, &result);
        assert!(validation.is_valid());
    }

    #[test]
    fn test_resolution_invalid_pivot() {
        let c1 = Clause::new(vec![Literal::pos(1), Literal::pos(2)]);
        let c2 = Clause::new(vec![Literal::neg(3), Literal::pos(4)]); // Wrong pivot
        let result = Clause::new(vec![Literal::pos(2), Literal::pos(4)]);
        let pivot = Literal::pos(1);

        let validation = ResolutionValidator::validate(&c1, &c2, pivot, &result);
        assert!(!validation.is_valid());
    }

    #[test]
    fn test_unit_propagation_valid() {
        // (p ∨ q ∨ r) with unit ¬p ⊢ (q ∨ r)
        let clause = Clause::new(vec![Literal::pos(1), Literal::pos(2), Literal::pos(3)]);
        let unit = Literal::neg(1);
        let result = Clause::new(vec![Literal::pos(2), Literal::pos(3)]);

        let validation = UnitPropagationValidator::validate(&clause, unit, &result);
        assert!(validation.is_valid());
    }

    #[test]
    fn test_unit_propagation_invalid() {
        let clause = Clause::new(vec![Literal::pos(1), Literal::pos(2)]);
        let unit = Literal::neg(3); // Not in clause
        let result = Clause::new(vec![Literal::pos(1), Literal::pos(2)]);

        let validation = UnitPropagationValidator::validate(&clause, unit, &result);
        assert!(!validation.is_valid());
    }

    #[test]
    fn test_cnf_not_not() {
        let validation = CnfValidator::validate_not_not("¬¬A", "A");
        assert!(validation.is_valid());

        let invalid = CnfValidator::validate_not_not("¬A", "A");
        assert!(!invalid.is_valid());
    }

    #[test]
    fn test_literal_display() {
        assert_eq!(format!("{}", Literal::pos(5)), "5");
        assert_eq!(format!("{}", Literal::neg(5)), "-5");
    }

    #[test]
    fn test_clause_display() {
        let clause = Clause::new(vec![Literal::pos(1), Literal::neg(2), Literal::pos(3)]);
        let display = format!("{}", clause);
        assert!(display.contains("1"));
        assert!(display.contains("-2"));
        assert!(display.contains("3"));
    }

    // ------------------------------------------------------------------
    // De Morgan / distributivity: real structural validation
    // ------------------------------------------------------------------

    #[test]
    fn test_demorgan_and_valid() {
        let v = CnfValidator::validate_demorgan_and("¬(A ∧ B)", "(¬A ∨ ¬B)");
        assert!(v.is_valid(), "{v:?}");
    }

    #[test]
    fn test_demorgan_and_valid_reordered() {
        // ∧/∨ are commutative -- a reordered but equivalent output is still valid.
        let v = CnfValidator::validate_demorgan_and("¬(A ∧ B)", "(¬B ∨ ¬A)");
        assert!(v.is_valid(), "{v:?}");
    }

    #[test]
    fn test_demorgan_and_wrong_operator_is_invalid() {
        // Using ∧ instead of ∨ on the output is a real error, not "valid".
        let v = CnfValidator::validate_demorgan_and("¬(A ∧ B)", "(¬A ∧ ¬B)");
        assert!(v.is_invalid(), "{v:?}");
    }

    #[test]
    fn test_demorgan_and_missing_negation_is_invalid() {
        let v = CnfValidator::validate_demorgan_and("¬(A ∧ B)", "(A ∨ ¬B)");
        assert!(v.is_invalid(), "{v:?}");
    }

    #[test]
    fn test_demorgan_and_unparseable_is_unchecked() {
        let v = CnfValidator::validate_demorgan_and("not even close to valid {{{", "???");
        assert!(v.is_unchecked(), "{v:?}");
    }

    #[test]
    fn test_demorgan_or_valid() {
        let v = CnfValidator::validate_demorgan_or("¬(A ∨ B)", "(¬A ∧ ¬B)");
        assert!(v.is_valid(), "{v:?}");
    }

    #[test]
    fn test_demorgan_or_invalid() {
        let v = CnfValidator::validate_demorgan_or("¬(A ∨ B)", "(¬A ∨ ¬B)");
        assert!(v.is_invalid(), "{v:?}");
    }

    #[test]
    fn test_distributivity_valid() {
        let v = CnfValidator::validate_distributivity("(A ∨ (B ∧ C))", "((A ∨ B) ∧ (A ∨ C))");
        assert!(v.is_valid(), "{v:?}");
    }

    #[test]
    fn test_distributivity_valid_symmetric_input() {
        let v = CnfValidator::validate_distributivity("((B ∧ C) ∨ A)", "((A ∨ B) ∧ (A ∨ C))");
        assert!(v.is_valid(), "{v:?}");
    }

    #[test]
    fn test_distributivity_invalid() {
        let v = CnfValidator::validate_distributivity("(A ∨ (B ∧ C))", "((A ∧ B) ∨ (A ∧ C))");
        assert!(v.is_invalid(), "{v:?}");
    }

    #[test]
    fn test_distributivity_unsupported_shape_is_unchecked() {
        let v = CnfValidator::validate_distributivity("(A ∧ B)", "(A ∧ B)");
        assert!(v.is_unchecked(), "{v:?}");
    }

    // ------------------------------------------------------------------
    // Farkas certificate: real linear-combination arithmetic
    // ------------------------------------------------------------------

    #[test]
    fn test_farkas_valid_contradiction() {
        // x <= 1  and  x >= 2  are jointly infeasible: 1*(x - 1 <= 0) + 1*(-x + 2 <= 0) -> 1 <= 0.
        let inequalities = vec!["x <= 1".to_string(), "x >= 2".to_string()];
        let coefficients = vec![1.0, 1.0];
        let v = TheoryLemmaValidator::validate_farkas(&inequalities, &coefficients, "false");
        assert!(v.is_valid(), "{v:?}");
    }

    #[test]
    fn test_farkas_negative_multiplier_is_invalid() {
        let inequalities = vec!["x <= 1".to_string(), "x >= 2".to_string()];
        let coefficients = vec![-1.0, 1.0];
        let v = TheoryLemmaValidator::validate_farkas(&inequalities, &coefficients, "false");
        assert!(v.is_invalid(), "{v:?}");
    }

    #[test]
    fn test_farkas_residual_variable_is_invalid() {
        // Coefficients don't cancel the variable -- not a valid certificate.
        let inequalities = vec!["x <= 1".to_string(), "y >= 2".to_string()];
        let coefficients = vec![1.0, 1.0];
        let v = TheoryLemmaValidator::validate_farkas(&inequalities, &coefficients, "false");
        assert!(v.is_invalid(), "{v:?}");
    }

    #[test]
    fn test_farkas_non_contradiction_is_invalid() {
        // x <= 5 and x >= 2 are satisfiable; combining them proves nothing.
        let inequalities = vec!["x <= 5".to_string(), "x >= 2".to_string()];
        let coefficients = vec![1.0, 1.0];
        let v = TheoryLemmaValidator::validate_farkas(&inequalities, &coefficients, "false");
        assert!(v.is_invalid(), "{v:?}");
    }

    #[test]
    fn test_farkas_unparseable_is_unchecked() {
        let inequalities = vec!["x * y <= 1".to_string()];
        let coefficients = vec![1.0];
        let v = TheoryLemmaValidator::validate_farkas(&inequalities, &coefficients, "false");
        assert!(v.is_unchecked(), "{v:?}");
    }

    #[test]
    fn test_farkas_mismatched_lengths_is_invalid() {
        let inequalities = vec!["x <= 1".to_string()];
        let coefficients = vec![1.0, 2.0];
        let v = TheoryLemmaValidator::validate_farkas(&inequalities, &coefficients, "false");
        assert!(v.is_invalid(), "{v:?}");
    }

    // ------------------------------------------------------------------
    // Congruence: real union-find over the given equalities
    // ------------------------------------------------------------------

    #[test]
    fn test_congruence_valid_direct() {
        let equalities = vec!["a = b".to_string()];
        let v = TheoryLemmaValidator::validate_congruence(&equalities, "f(a) = f(b)");
        assert!(v.is_valid(), "{v:?}");
    }

    #[test]
    fn test_congruence_valid_transitive() {
        let equalities = vec!["a = b".to_string(), "b = c".to_string()];
        let v = TheoryLemmaValidator::validate_congruence(&equalities, "f(a) = f(c)");
        assert!(v.is_valid(), "{v:?}");
    }

    #[test]
    fn test_congruence_unrelated_args_is_invalid() {
        let equalities = vec!["a = b".to_string()];
        let v = TheoryLemmaValidator::validate_congruence(&equalities, "f(a) = f(c)");
        assert!(v.is_invalid(), "{v:?}");
    }

    #[test]
    fn test_congruence_different_function_symbols_is_invalid() {
        let equalities = vec!["a = b".to_string()];
        let v = TheoryLemmaValidator::validate_congruence(&equalities, "f(a) = g(b)");
        assert!(v.is_invalid(), "{v:?}");
    }

    #[test]
    fn test_congruence_arity_mismatch_is_invalid() {
        let equalities = vec!["a = b".to_string()];
        let v = TheoryLemmaValidator::validate_congruence(&equalities, "f(a) = f(b, c)");
        assert!(v.is_invalid(), "{v:?}");
    }

    #[test]
    fn test_congruence_multi_arg() {
        let equalities = vec!["a = c".to_string(), "b = d".to_string()];
        let v = TheoryLemmaValidator::validate_congruence(&equalities, "f(a, b) = f(c, d)");
        assert!(v.is_valid(), "{v:?}");
    }

    // ------------------------------------------------------------------
    // Transitivity: real bridging-term check
    // ------------------------------------------------------------------

    #[test]
    fn test_transitivity_valid() {
        let v = TheoryLemmaValidator::validate_transitivity("a = b", "b = c", "a = c");
        assert!(v.is_valid(), "{v:?}");
    }

    #[test]
    fn test_transitivity_valid_reversed_orientation() {
        let v = TheoryLemmaValidator::validate_transitivity("b = a", "c = b", "a = c");
        assert!(v.is_valid(), "{v:?}");
    }

    #[test]
    fn test_transitivity_unrelated_equalities_is_invalid() {
        let v = TheoryLemmaValidator::validate_transitivity("a = b", "c = d", "a = d");
        assert!(v.is_invalid(), "{v:?}");
    }

    #[test]
    fn test_transitivity_wrong_conclusion_is_invalid() {
        let v = TheoryLemmaValidator::validate_transitivity("a = b", "b = c", "a = d");
        assert!(v.is_invalid(), "{v:?}");
    }

    /// `Formula` is parsed from untrusted text where each leading `¬` costs one
    /// nesting level, and the CNF validators clone whole subformulas while
    /// building the formula they expect. `Clone` used to be a compiler-generated
    /// recursive walk.
    ///
    /// Running on a deliberately small (128 KiB) stack: returning at all is the
    /// proof. The `Drop`s at the end of the closure are part of the test.
    ///
    /// The stack size and `DEPTH` are scaled together on purpose: what is
    /// pinned is the ratio, ~21 bytes per frame, which no real call frame fits
    /// into. Never raise one without raising the other.
    #[test]
    fn test_deep_formula_clone_does_not_overflow() {
        const DEPTH: usize = 6_250;

        let handle = std::thread::Builder::new()
            .stack_size(1 << 17)
            .spawn(|| {
                let text = format!("{}a", "¬".repeat(DEPTH));
                let formula = parse_formula(&text).expect("negation chain should parse");

                let copy = formula.clone();
                assert!(formula_equiv(&copy, &formula));

                // Cloning through a `Vec<Formula>` (as the validators do) must
                // be iterative too.
                let wrapped = Formula::And(vec![formula]);
                let wrapped_copy = wrapped.clone();
                assert!(formula_equiv(&wrapped_copy, &wrapped));

                // The clone must render identically to the original.
                assert_eq!(copy.to_string(), text);
            })
            .expect("thread spawn should succeed");

        handle.join().expect("worker thread should not panic");
    }

    /// The hand-written `Clone` must reproduce every variant exactly.
    #[test]
    fn test_formula_clone_covers_every_variant() {
        let samples = [
            "a",
            "¬a",
            "¬¬a",
            "(a ∧ b)",
            "(a ∨ b)",
            "¬(a ∧ b)",
            "((a ∨ b) ∧ (¬c ∨ d))",
        ];

        for text in samples {
            let formula = parse_formula(text).unwrap_or_else(|| panic!("{text:?} should parse"));
            let copy = formula.clone();
            assert!(formula_equiv(&copy, &formula), "{text:?}");
            assert_eq!(copy.to_string(), formula.to_string(), "{text:?}");
        }

        // Empty operand lists survive the round trip.
        let empty_and = Formula::And(Vec::new());
        assert!(formula_equiv(&empty_and.clone(), &empty_and));
        let empty_or = Formula::Or(Vec::new());
        assert!(formula_equiv(&empty_or.clone(), &empty_or));
    }
}
