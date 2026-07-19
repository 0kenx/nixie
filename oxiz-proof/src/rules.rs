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
#[derive(Debug, Clone, PartialEq, Eq)]
enum Formula {
    Atom(String),
    Not(Box<Formula>),
    And(Vec<Formula>),
    Or(Vec<Formula>),
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Atom(s) => write!(f, "{s}"),
            Self::Not(inner) => write!(f, "¬{inner}"),
            Self::And(xs) => {
                write!(f, "(")?;
                for (i, x) in xs.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ∧ ")?;
                    }
                    write!(f, "{x}")?;
                }
                write!(f, ")")
            }
            Self::Or(xs) => {
                write!(f, "(")?;
                for (i, x) in xs.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ∨ ")?;
                    }
                    write!(f, "{x}")?;
                }
                write!(f, ")")
            }
        }
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

fn parse_formula_tokens(chars: &[char], pos: &mut usize) -> Option<Formula> {
    skip_ws(chars, pos);
    if *pos >= chars.len() {
        return None;
    }
    match chars[*pos] {
        '¬' => {
            *pos += 1;
            let inner = parse_formula_tokens(chars, pos)?;
            Some(Formula::Not(Box::new(inner)))
        }
        '(' => {
            *pos += 1;
            let mut parts = vec![parse_formula_tokens(chars, pos)?];
            let mut op: Option<char> = None;
            loop {
                skip_ws(chars, pos);
                if *pos < chars.len() && (chars[*pos] == '∧' || chars[*pos] == '∨') {
                    let this_op = chars[*pos];
                    match op {
                        Some(existing) if existing != this_op => return None,
                        _ => op = Some(this_op),
                    }
                    *pos += 1;
                    parts.push(parse_formula_tokens(chars, pos)?);
                } else {
                    break;
                }
            }
            skip_ws(chars, pos);
            if *pos >= chars.len() || chars[*pos] != ')' {
                return None;
            }
            *pos += 1;
            match op {
                None => parts.into_iter().next(),
                Some('∧') => Some(Formula::And(parts)),
                Some('∨') => Some(Formula::Or(parts)),
                _ => None,
            }
        }
        c if c.is_alphanumeric() || c == '_' => {
            let start = *pos;
            while *pos < chars.len() && (chars[*pos].is_alphanumeric() || chars[*pos] == '_') {
                *pos += 1;
            }
            Some(Formula::Atom(chars[start..*pos].iter().collect()))
        }
        _ => None,
    }
}

/// Structural equivalence under associativity/commutativity of `∧`/`∨` (i.e.
/// treating the argument lists of `And`/`Or` as multisets rather than
/// sequences). This is a syntactic check, not a full semantic equivalence
/// (e.g. it will not recognize `A` as equivalent to `A ∧ A`).
fn formula_equiv(a: &Formula, b: &Formula) -> bool {
    match (a, b) {
        (Formula::Atom(x), Formula::Atom(y)) => x == y,
        (Formula::Not(x), Formula::Not(y)) => formula_equiv(x, y),
        (Formula::And(xs), Formula::And(ys)) | (Formula::Or(xs), Formula::Or(ys)) => {
            multiset_equiv(xs, ys)
        }
        _ => false,
    }
}

fn multiset_equiv(xs: &[Formula], ys: &[Formula]) -> bool {
    if xs.len() != ys.len() {
        return false;
    }
    let mut used = vec![false; ys.len()];
    for x in xs {
        let Some(slot) = used
            .iter()
            .enumerate()
            .find(|(i, used)| !**used && formula_equiv(x, &ys[*i]))
            .map(|(i, _)| i)
        else {
            return false;
        };
        used[slot] = true;
    }
    true
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

    fn find(&mut self, x: &str) -> String {
        if !self.parent.contains_key(x) {
            self.parent.insert(x.to_string(), x.to_string());
            return x.to_string();
        }
        let p = self.parent.get(x).cloned().unwrap_or_else(|| x.to_string());
        if p == x {
            x.to_string()
        } else {
            let root = self.find(&p);
            self.parent.insert(x.to_string(), root.clone());
            root
        }
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
}
