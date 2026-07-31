//! Constraint Logic Programming (CLP) integration for Datalog
//!
//! Extends Datalog with constraint solving capabilities for numeric
//! and symbolic constraints.

use crate::prelude::HashMap;
#[allow(unused_imports)]
use crate::prelude::*;
use core::cmp::Ordering;
use core::mem::discriminant;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;

use super::rule::Variable;
use super::tuple::Value;

/// Three-valued outcome of checking a constraint against an assignment
///
/// The CLP checker previously answered `bool`, which forced every case it
/// could not decide into "satisfied" — and `solve` turns "all satisfied" into
/// `Sat`. `Unknown` keeps the undecided case distinguishable so it can be
/// reported as `ClpResult::Unknown` instead of a wrong `Sat`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CheckResult {
    /// The assignment provably satisfies the constraint
    Satisfied,
    /// The assignment provably violates the constraint
    Violated,
    /// Not determined: operands unassigned, or of a kind this checker cannot
    /// interpret for the constraint at hand
    Unknown,
}

impl CheckResult {
    /// Lift a decided check into a [`CheckResult`]
    const fn from_bool(satisfied: bool) -> Self {
        if satisfied {
            CheckResult::Satisfied
        } else {
            CheckResult::Violated
        }
    }
}

/// Interpret a value as a rational number, if it denotes one
fn numeric_value(value: &Value) -> Option<BigRational> {
    match value {
        Value::Int64(n) => Some(BigRational::from(BigInt::from(*n))),
        Value::UInt64(n) => Some(BigRational::from(BigInt::from(*n))),
        Value::Rational(r) => Some(r.clone()),
        _ => None,
    }
}

/// Order two values for an ordering constraint
///
/// Numeric values are compared numerically even across `Int64`/`UInt64`/
/// `Rational`. Two values of the same non-numeric variant fall back to
/// `Value`'s total order. Anything else — a `Null`, or a comparison between
/// different variants — has no meaningful order and yields `None`, which the
/// caller turns into `Unknown` rather than a fabricated verdict from the
/// variant-rank tiebreak.
fn compare_values(lhs: &Value, rhs: &Value) -> Option<Ordering> {
    if let (Some(a), Some(b)) = (numeric_value(lhs), numeric_value(rhs)) {
        return Some(a.cmp(&b));
    }
    if matches!(lhs, Value::Null) || discriminant(lhs) != discriminant(rhs) {
        return None;
    }
    Some(lhs.cmp(rhs))
}

/// Check a binary ordering constraint (`<`, `<=`, `>`, `>=`)
///
/// Handles both the variable-variable form and the variable-constant form.
fn check_ordering(
    values: &[&Value],
    constraint: &Constraint,
    accept: impl Fn(Ordering) -> bool,
) -> CheckResult {
    let ordering = match values {
        [a, b] => compare_values(a, b),
        [single] => match constraint.constant() {
            Some(c) => compare_values(single, c),
            None => None,
        },
        _ => None,
    };
    match ordering {
        Some(order) => CheckResult::from_bool(accept(order)),
        None => CheckResult::Unknown,
    }
}

/// Check a linear constraint `sum(coeff_i * x_i) = constant`
///
/// Yields `Unknown` for a malformed constraint (coefficient/variable arity
/// mismatch, missing or non-numeric constant) or a non-numeric operand,
/// rather than the unconditional "satisfied" this check used to return.
fn check_linear(values: &[&Value], constraint: &Constraint) -> CheckResult {
    let coefficients = constraint.coefficients();
    if coefficients.len() != values.len() {
        return CheckResult::Unknown;
    }
    let Some(target) = constraint.constant().and_then(numeric_value) else {
        return CheckResult::Unknown;
    };

    let mut sum = BigRational::zero();
    for (coefficient, value) in coefficients.iter().zip(values.iter()) {
        let Some(numeric) = numeric_value(value) else {
            return CheckResult::Unknown;
        };
        sum += coefficient * numeric;
    }

    CheckResult::from_bool(sum == target)
}

/// Kind of constraint
#[derive(Debug, Clone, PartialEq)]
pub enum ConstraintKind {
    /// Equality: x = y or x = c
    Equal,
    /// Disequality: x != y or x != c
    NotEqual,
    /// Less than: x < y or x < c
    LessThan,
    /// Less than or equal: x <= y or x <= c
    LessEqual,
    /// Greater than: x > y or x > c
    GreaterThan,
    /// Greater than or equal: x >= y or x >= c
    GreaterEqual,
    /// Membership: x in {c1, c2, ...}
    Member,
    /// Not member: x not in {c1, c2, ...}
    NotMember,
    /// Linear arithmetic: a1*x1 + a2*x2 + ... = c
    Linear,
}

/// A constraint in CLP
#[derive(Debug, Clone)]
pub struct Constraint {
    /// Kind of constraint
    kind: ConstraintKind,
    /// Variables involved
    variables: Vec<Variable>,
    /// Coefficients (for linear constraints)
    coefficients: Vec<BigRational>,
    /// Constant term
    constant: Option<Value>,
    /// Set of values (for member/not member)
    value_set: Vec<Value>,
}

impl Constraint {
    /// Create an equality constraint
    pub fn equal(x: Variable, y: Variable) -> Self {
        Self {
            kind: ConstraintKind::Equal,
            variables: vec![x, y],
            coefficients: Vec::new(),
            constant: None,
            value_set: Vec::new(),
        }
    }

    /// Create an equality with constant
    pub fn equal_const(x: Variable, c: Value) -> Self {
        Self {
            kind: ConstraintKind::Equal,
            variables: vec![x],
            coefficients: Vec::new(),
            constant: Some(c),
            value_set: Vec::new(),
        }
    }

    /// Create a disequality constraint
    pub fn not_equal(x: Variable, y: Variable) -> Self {
        Self {
            kind: ConstraintKind::NotEqual,
            variables: vec![x, y],
            coefficients: Vec::new(),
            constant: None,
            value_set: Vec::new(),
        }
    }

    /// Create a less-than constraint
    pub fn less_than(x: Variable, y: Variable) -> Self {
        Self {
            kind: ConstraintKind::LessThan,
            variables: vec![x, y],
            coefficients: Vec::new(),
            constant: None,
            value_set: Vec::new(),
        }
    }

    /// Create a less-equal constraint
    pub fn less_equal(x: Variable, y: Variable) -> Self {
        Self {
            kind: ConstraintKind::LessEqual,
            variables: vec![x, y],
            coefficients: Vec::new(),
            constant: None,
            value_set: Vec::new(),
        }
    }

    /// Create a greater-than constraint
    pub fn greater_than(x: Variable, y: Variable) -> Self {
        Self {
            kind: ConstraintKind::GreaterThan,
            variables: vec![x, y],
            coefficients: Vec::new(),
            constant: None,
            value_set: Vec::new(),
        }
    }

    /// Create a greater-equal constraint
    pub fn greater_equal(x: Variable, y: Variable) -> Self {
        Self {
            kind: ConstraintKind::GreaterEqual,
            variables: vec![x, y],
            coefficients: Vec::new(),
            constant: None,
            value_set: Vec::new(),
        }
    }

    /// Create an ordering constraint against a constant: `x <kind> c`
    ///
    /// `kind` must be one of the four ordering kinds; any other kind would
    /// describe a different constraint shape, so it is rejected.
    pub fn compare_const(x: Variable, kind: ConstraintKind, c: Value) -> Option<Self> {
        match kind {
            ConstraintKind::LessThan
            | ConstraintKind::LessEqual
            | ConstraintKind::GreaterThan
            | ConstraintKind::GreaterEqual => Some(Self {
                kind,
                variables: vec![x],
                coefficients: Vec::new(),
                constant: Some(c),
                value_set: Vec::new(),
            }),
            ConstraintKind::Equal
            | ConstraintKind::NotEqual
            | ConstraintKind::Member
            | ConstraintKind::NotMember
            | ConstraintKind::Linear => None,
        }
    }

    /// Create a membership constraint
    pub fn member(x: Variable, values: Vec<Value>) -> Self {
        Self {
            kind: ConstraintKind::Member,
            variables: vec![x],
            coefficients: Vec::new(),
            constant: None,
            value_set: values,
        }
    }

    /// Create a non-membership constraint
    pub fn not_member(x: Variable, values: Vec<Value>) -> Self {
        Self {
            kind: ConstraintKind::NotMember,
            variables: vec![x],
            coefficients: Vec::new(),
            constant: None,
            value_set: values,
        }
    }

    /// Create a linear constraint: sum(coeffs * vars) = constant
    pub fn linear(vars: Vec<Variable>, coeffs: Vec<BigRational>, constant: BigRational) -> Self {
        Self {
            kind: ConstraintKind::Linear,
            variables: vars,
            coefficients: coeffs,
            constant: Some(Value::Rational(constant)),
            value_set: Vec::new(),
        }
    }

    /// Get constraint kind
    pub fn kind(&self) -> &ConstraintKind {
        &self.kind
    }

    /// Get variables
    pub fn variables(&self) -> &[Variable] {
        &self.variables
    }

    /// Get coefficients
    pub fn coefficients(&self) -> &[BigRational] {
        &self.coefficients
    }

    /// Get constant
    pub fn constant(&self) -> Option<&Value> {
        self.constant.as_ref()
    }

    /// Get value set
    pub fn value_set(&self) -> &[Value] {
        &self.value_set
    }

    /// Check if constraint involves variable
    pub fn involves(&self, var: Variable) -> bool {
        self.variables.contains(&var)
    }
}

/// Constraint store for CLP solver
#[derive(Debug)]
pub struct ConstraintStore {
    /// All constraints
    constraints: Vec<Constraint>,
    /// Constraints indexed by variable
    var_constraints: HashMap<Variable, Vec<usize>>,
    /// Variable domains
    domains: HashMap<Variable, Domain>,
}

/// Domain of a variable
#[derive(Debug, Clone)]
pub enum Domain {
    /// Unrestricted
    Any,
    /// Boolean domain
    Bool,
    /// Integer domain with bounds
    Integer { min: Option<i64>, max: Option<i64> },
    /// Rational domain with bounds
    Rational {
        min: Option<BigRational>,
        max: Option<BigRational>,
    },
    /// Finite set of values
    Finite(Vec<Value>),
    /// Empty (unsatisfiable)
    Empty,
}

impl Domain {
    /// Create an integer domain
    pub fn integer() -> Self {
        Domain::Integer {
            min: None,
            max: None,
        }
    }

    /// Create a bounded integer domain
    pub fn integer_range(min: i64, max: i64) -> Self {
        Domain::Integer {
            min: Some(min),
            max: Some(max),
        }
    }

    /// Create a finite domain
    pub fn finite(values: Vec<Value>) -> Self {
        if values.is_empty() {
            Domain::Empty
        } else {
            Domain::Finite(values)
        }
    }

    /// Check if domain is empty
    pub fn is_empty(&self) -> bool {
        matches!(self, Domain::Empty)
    }

    /// Check if domain is singleton
    pub fn is_singleton(&self) -> bool {
        match self {
            Domain::Finite(v) => v.len() == 1,
            _ => false,
        }
    }

    /// Get singleton value
    pub fn singleton_value(&self) -> Option<&Value> {
        match self {
            Domain::Finite(v) if v.len() == 1 => v.first(),
            _ => None,
        }
    }

    /// Intersect with another domain
    pub fn intersect(&self, other: &Domain) -> Domain {
        match (self, other) {
            (Domain::Empty, _) | (_, Domain::Empty) => Domain::Empty,
            (Domain::Any, d) | (d, Domain::Any) => d.clone(),
            (Domain::Finite(a), Domain::Finite(b)) => {
                let intersection: Vec<_> = a.iter().filter(|v| b.contains(v)).cloned().collect();
                Domain::finite(intersection)
            }
            (
                Domain::Integer {
                    min: min1,
                    max: max1,
                },
                Domain::Integer {
                    min: min2,
                    max: max2,
                },
            ) => {
                let new_min = match (min1, min2) {
                    (Some(a), Some(b)) => Some(*a.max(b)),
                    (Some(a), None) => Some(*a),
                    (None, Some(b)) => Some(*b),
                    (None, None) => None,
                };
                let new_max = match (max1, max2) {
                    (Some(a), Some(b)) => Some(*a.min(b)),
                    (Some(a), None) => Some(*a),
                    (None, Some(b)) => Some(*b),
                    (None, None) => None,
                };
                if let (Some(min), Some(max)) = (new_min, new_max)
                    && min > max
                {
                    return Domain::Empty;
                }
                Domain::Integer {
                    min: new_min,
                    max: new_max,
                }
            }
            _ => Domain::Any, // Simplified
        }
    }

    /// Remove a value from domain
    pub fn remove(&mut self, value: &Value) {
        if let Domain::Finite(values) = self {
            values.retain(|v| v != value);
            if values.is_empty() {
                *self = Domain::Empty;
            }
        }
    }
}

impl ConstraintStore {
    /// Create a new constraint store
    pub fn new() -> Self {
        Self {
            constraints: Vec::new(),
            var_constraints: HashMap::new(),
            domains: HashMap::new(),
        }
    }

    /// Add a constraint
    pub fn add(&mut self, constraint: Constraint) {
        let idx = self.constraints.len();
        for var in constraint.variables() {
            self.var_constraints.entry(*var).or_default().push(idx);
        }
        self.constraints.push(constraint);
    }

    /// Set domain for variable
    pub fn set_domain(&mut self, var: Variable, domain: Domain) {
        self.domains.insert(var, domain);
    }

    /// Get domain for variable
    pub fn domain(&self, var: Variable) -> Option<&Domain> {
        self.domains.get(&var)
    }

    /// Get constraints involving variable
    pub fn constraints_for(&self, var: Variable) -> Vec<&Constraint> {
        self.var_constraints
            .get(&var)
            .map(|indices| {
                indices
                    .iter()
                    .filter_map(|&i| self.constraints.get(i))
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Get all constraints
    pub fn constraints(&self) -> &[Constraint] {
        &self.constraints
    }

    /// Check if store is empty
    pub fn is_empty(&self) -> bool {
        self.constraints.is_empty()
    }

    /// Clear all constraints
    pub fn clear(&mut self) {
        self.constraints.clear();
        self.var_constraints.clear();
        self.domains.clear();
    }
}

impl Default for ConstraintStore {
    fn default() -> Self {
        Self::new()
    }
}

/// CLP solver result
#[derive(Debug)]
pub enum ClpResult {
    /// Satisfiable with variable assignment
    Sat(HashMap<Variable, Value>),
    /// Unsatisfiable
    Unsat,
    /// Unknown (timeout or resource limit)
    Unknown,
}

/// CLP solver
#[derive(Debug)]
pub struct ClpSolver {
    /// Constraint store
    store: ConstraintStore,
    /// Current assignment
    assignment: HashMap<Variable, Value>,
    /// Propagation queue
    prop_queue: Vec<Variable>,
    /// Solver configuration
    config: ClpConfig,
}

/// CLP solver configuration
#[derive(Debug, Clone)]
pub struct ClpConfig {
    /// Maximum propagation iterations
    pub max_propagations: usize,
    /// Enable arc consistency
    pub arc_consistency: bool,
    /// Enable bound propagation
    pub bound_propagation: bool,
}

impl Default for ClpConfig {
    fn default() -> Self {
        Self {
            max_propagations: 10000,
            arc_consistency: true,
            bound_propagation: true,
        }
    }
}

impl ClpSolver {
    /// Create a new CLP solver
    pub fn new() -> Self {
        Self {
            store: ConstraintStore::new(),
            assignment: HashMap::new(),
            prop_queue: Vec::new(),
            config: ClpConfig::default(),
        }
    }

    /// Create with configuration
    pub fn with_config(config: ClpConfig) -> Self {
        Self {
            store: ConstraintStore::new(),
            assignment: HashMap::new(),
            prop_queue: Vec::new(),
            config,
        }
    }

    /// Add a constraint
    pub fn add_constraint(&mut self, constraint: Constraint) {
        // Queue variables for propagation
        for var in constraint.variables() {
            if !self.prop_queue.contains(var) {
                self.prop_queue.push(*var);
            }
        }
        self.store.add(constraint);
    }

    /// Set variable domain
    pub fn set_domain(&mut self, var: Variable, domain: Domain) {
        self.store.set_domain(var, domain);
        if !self.prop_queue.contains(&var) {
            self.prop_queue.push(var);
        }
    }

    /// Assign a value to a variable
    pub fn assign(&mut self, var: Variable, value: Value) {
        self.assignment.insert(var, value);
        if !self.prop_queue.contains(&var) {
            self.prop_queue.push(var);
        }
    }

    /// Get current assignment
    pub fn get_assignment(&self, var: Variable) -> Option<&Value> {
        self.assignment.get(&var)
    }

    /// Solve the constraint system
    ///
    /// A `Sat` answer is only produced when every constraint is *proven*
    /// satisfied by the assignment; a constraint the checker cannot decide
    /// (non-numeric operands, malformed linear constraint, ...) downgrades
    /// the answer to `Unknown` instead of being waved through.
    pub fn solve(&mut self) -> ClpResult {
        // Propagate constraints
        if !self.propagate() {
            return ClpResult::Unsat;
        }

        // Check if all variables are assigned
        let unassigned: Vec<_> = self
            .store
            .domains
            .keys()
            .filter(|v| !self.assignment.contains_key(v))
            .copied()
            .collect();

        if unassigned.is_empty() {
            // All assigned - verify constraints
            return match self.verify_all() {
                CheckResult::Satisfied => ClpResult::Sat(self.assignment.clone()),
                CheckResult::Violated => ClpResult::Unsat,
                CheckResult::Unknown => ClpResult::Unknown,
            };
        }

        // Try to assign unassigned variables from singleton domains
        for var in &unassigned {
            if let Some(domain) = self.store.domain(*var)
                && let Some(value) = domain.singleton_value()
            {
                self.assignment.insert(*var, value.clone());
            }
        }

        // Re-check
        match self.verify_all() {
            CheckResult::Satisfied => ClpResult::Sat(self.assignment.clone()),
            // Variables remain unassigned, so a violation here is only a
            // violation of this partial assignment, not of the system.
            CheckResult::Violated | CheckResult::Unknown => ClpResult::Unknown,
        }
    }

    /// Propagate constraints
    fn propagate(&mut self) -> bool {
        let mut iterations = 0;

        while !self.prop_queue.is_empty() && iterations < self.config.max_propagations {
            iterations += 1;

            let Some(var) = self.prop_queue.pop() else {
                // The loop condition already established non-emptiness; this
                // arm exists so the invariant is expressed as control flow
                // rather than a panic.
                break;
            };

            // Propagate constraints involving this variable
            let constraint_indices: Vec<_> = self
                .store
                .var_constraints
                .get(&var)
                .cloned()
                .unwrap_or_default();

            for idx in constraint_indices {
                if let Some(constraint) = self.store.constraints.get(idx)
                    && !self.propagate_constraint(constraint.clone())
                {
                    return false;
                }
            }
        }

        true
    }

    /// Propagate a single constraint
    ///
    /// Returns `false` only when the constraint is *proven* violated by the
    /// current assignment. Every kind is handled explicitly: the ordering,
    /// `NotMember` and `Linear` kinds used to fall into a catch-all that
    /// reported "no conflict" for constraints the assignment already
    /// falsified, so `propagate` never detected those conflicts.
    fn propagate_constraint(&mut self, constraint: Constraint) -> bool {
        match constraint.kind() {
            ConstraintKind::Equal => self.propagate_equality(&constraint),
            ConstraintKind::NotEqual => self.propagate_disequality(&constraint),
            ConstraintKind::Member => self.propagate_membership(&constraint),
            ConstraintKind::NotMember => self.propagate_non_membership(&constraint),
            ConstraintKind::LessThan
            | ConstraintKind::LessEqual
            | ConstraintKind::GreaterThan
            | ConstraintKind::GreaterEqual
            | ConstraintKind::Linear => {
                // Fully-assigned instances are decidable right here; a partial
                // assignment yields `Unknown`, which is not a conflict.
                self.check_constraint(&constraint) != CheckResult::Violated
            }
        }
    }

    /// Propagate a non-membership constraint
    ///
    /// Detects the conflict when the variable is already assigned a forbidden
    /// value, and otherwise removes the forbidden values from a finite domain.
    fn propagate_non_membership(&mut self, constraint: &Constraint) -> bool {
        let vars = constraint.variables();

        let [var] = vars else {
            return true;
        };
        let forbidden = constraint.value_set();

        if let Some(assigned) = self.assignment.get(var) {
            return !forbidden.contains(assigned);
        }

        // Restrict a finite domain by removing the forbidden values.
        let restricted = match self.store.domains.get(var) {
            Some(Domain::Finite(values)) => {
                let remaining: Vec<Value> = values
                    .iter()
                    .filter(|v| !forbidden.contains(v))
                    .cloned()
                    .collect();
                (remaining.len() != values.len()).then_some(remaining)
            }
            _ => None,
        };
        if let Some(remaining) = restricted {
            if remaining.is_empty() {
                return false;
            }
            self.store.set_domain(*var, Domain::finite(remaining));
        }

        true
    }

    /// Propagate equality constraint
    fn propagate_equality(&mut self, constraint: &Constraint) -> bool {
        let vars = constraint.variables();

        if vars.len() == 1 {
            // x = c
            let var = vars[0];
            if let Some(constant) = constraint.constant() {
                if let Some(existing) = self.assignment.get(&var) {
                    return existing == constant;
                }
                self.assignment.insert(var, constant.clone());
            }
        } else if vars.len() == 2 {
            // x = y
            let x = vars[0];
            let y = vars[1];

            match (
                self.assignment.get(&x).cloned(),
                self.assignment.get(&y).cloned(),
            ) {
                (Some(vx), Some(vy)) => return vx == vy,
                (Some(vx), None) => {
                    self.assignment.insert(y, vx);
                }
                (None, Some(vy)) => {
                    self.assignment.insert(x, vy);
                }
                (None, None) => {}
            }
        }

        true
    }

    /// Propagate disequality constraint
    fn propagate_disequality(&mut self, constraint: &Constraint) -> bool {
        let vars = constraint.variables();

        if vars.len() == 2 {
            let x = vars[0];
            let y = vars[1];

            if let (Some(vx), Some(vy)) = (self.assignment.get(&x), self.assignment.get(&y)) {
                return vx != vy;
            }
        }

        true
    }

    /// Propagate membership constraint
    fn propagate_membership(&mut self, constraint: &Constraint) -> bool {
        let vars = constraint.variables();

        if vars.len() == 1 {
            let var = vars[0];
            let values = constraint.value_set();

            if let Some(assigned) = self.assignment.get(&var) {
                return values.contains(assigned);
            }

            // Restrict domain
            let new_domain = Domain::finite(values.to_vec());
            if let Some(existing) = self.store.domains.get(&var) {
                let intersected = existing.intersect(&new_domain);
                if intersected.is_empty() {
                    return false;
                }
                self.store.set_domain(var, intersected);
            } else {
                self.store.set_domain(var, new_domain);
            }
        }

        true
    }

    /// Verify all constraints
    ///
    /// A single undecidable constraint makes the whole verdict `Unknown`; a
    /// single violated one makes it `Violated`, which wins over `Unknown`.
    fn verify_all(&self) -> CheckResult {
        let mut verdict = CheckResult::Satisfied;
        for constraint in &self.store.constraints {
            match self.check_constraint(constraint) {
                CheckResult::Satisfied => {}
                CheckResult::Violated => return CheckResult::Violated,
                CheckResult::Unknown => verdict = CheckResult::Unknown,
            }
        }
        verdict
    }

    /// Check a single constraint against the current assignment
    ///
    /// Returns [`CheckResult::Unknown`] whenever the constraint's truth value
    /// is not determined — either because an operand is still unassigned, or
    /// because the operands are not of a kind this checker can interpret
    /// (e.g. a `Linear` constraint over symbols). `Linear` in particular used
    /// to be hard-coded to "satisfied", so `solve` could answer `Sat` with an
    /// assignment that violates it.
    fn check_constraint(&self, constraint: &Constraint) -> CheckResult {
        let vars = constraint.variables();

        // Get assigned values
        let values: Vec<_> = vars.iter().filter_map(|v| self.assignment.get(v)).collect();

        // If not all variables are assigned, nothing is decided yet.
        if values.len() != vars.len() {
            return CheckResult::Unknown;
        }

        match constraint.kind() {
            ConstraintKind::Equal => match (values.as_slice(), constraint.constant()) {
                ([single], Some(c)) => CheckResult::from_bool(*single == c),
                ([_], None) => CheckResult::Unknown,
                ([], _) => CheckResult::Unknown,
                (many, _) => CheckResult::from_bool(many.windows(2).all(|w| w[0] == w[1])),
            },
            ConstraintKind::NotEqual => match values.as_slice() {
                [a, b] => CheckResult::from_bool(a != b),
                [single] => match constraint.constant() {
                    Some(c) => CheckResult::from_bool(*single != c),
                    None => CheckResult::Unknown,
                },
                _ => CheckResult::Unknown,
            },
            ConstraintKind::LessThan => {
                check_ordering(&values, constraint, |o| o == Ordering::Less)
            }
            ConstraintKind::LessEqual => {
                check_ordering(&values, constraint, |o| o != Ordering::Greater)
            }
            ConstraintKind::GreaterThan => {
                check_ordering(&values, constraint, |o| o == Ordering::Greater)
            }
            ConstraintKind::GreaterEqual => {
                check_ordering(&values, constraint, |o| o != Ordering::Less)
            }
            ConstraintKind::Member => match values.first() {
                Some(v) => CheckResult::from_bool(constraint.value_set().contains(v)),
                None => CheckResult::Unknown,
            },
            ConstraintKind::NotMember => match values.first() {
                Some(v) => CheckResult::from_bool(!constraint.value_set().contains(v)),
                None => CheckResult::Unknown,
            },
            ConstraintKind::Linear => check_linear(&values, constraint),
        }
    }

    /// Reset solver state
    pub fn reset(&mut self) {
        self.assignment.clear();
        self.prop_queue.clear();
    }

    /// Clear all constraints and state
    pub fn clear(&mut self) {
        self.store.clear();
        self.assignment.clear();
        self.prop_queue.clear();
    }
}

impl Default for ClpSolver {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lasso::ThreadedRodeo;

    #[test]
    fn test_equality_constraint() {
        let interner = ThreadedRodeo::default();
        let x = Variable::new(interner.get_or_intern("x"));

        let mut solver = ClpSolver::new();
        solver.add_constraint(Constraint::equal_const(x, Value::Int64(42)));

        let result = solver.solve();
        match result {
            ClpResult::Sat(assignment) => {
                assert_eq!(assignment.get(&x), Some(&Value::Int64(42)));
            }
            _ => panic!("Expected SAT"),
        }
    }

    #[test]
    fn test_variable_equality() {
        let interner = ThreadedRodeo::default();
        let x = Variable::new(interner.get_or_intern("x"));
        let y = Variable::new(interner.get_or_intern("y"));

        let mut solver = ClpSolver::new();
        solver.add_constraint(Constraint::equal(x, y));
        solver.assign(x, Value::Int64(10));

        let result = solver.solve();
        match result {
            ClpResult::Sat(assignment) => {
                assert_eq!(assignment.get(&x), assignment.get(&y));
            }
            _ => panic!("Expected SAT"),
        }
    }

    #[test]
    fn test_disequality_unsat() {
        let interner = ThreadedRodeo::default();
        let x = Variable::new(interner.get_or_intern("x"));
        let y = Variable::new(interner.get_or_intern("y"));

        let mut solver = ClpSolver::new();
        solver.add_constraint(Constraint::equal(x, y));
        solver.add_constraint(Constraint::not_equal(x, y));
        solver.assign(x, Value::Int64(5));

        let result = solver.solve();
        assert!(matches!(result, ClpResult::Unsat));
    }

    #[test]
    fn test_membership_constraint() {
        let interner = ThreadedRodeo::default();
        let x = Variable::new(interner.get_or_intern("x"));

        let mut solver = ClpSolver::new();
        solver.add_constraint(Constraint::member(
            x,
            vec![Value::Int64(1), Value::Int64(2), Value::Int64(3)],
        ));
        solver.assign(x, Value::Int64(2));

        let result = solver.solve();
        assert!(matches!(result, ClpResult::Sat(_)));
    }

    #[test]
    fn test_domain_intersection() {
        let d1 = Domain::finite(vec![Value::Int64(1), Value::Int64(2), Value::Int64(3)]);
        let d2 = Domain::finite(vec![Value::Int64(2), Value::Int64(3), Value::Int64(4)]);

        let intersected = d1.intersect(&d2);
        if let Domain::Finite(values) = intersected {
            assert_eq!(values.len(), 2);
            assert!(values.contains(&Value::Int64(2)));
            assert!(values.contains(&Value::Int64(3)));
        } else {
            panic!("Expected finite domain");
        }
    }

    #[test]
    fn test_domain_empty() {
        let d1 = Domain::finite(vec![Value::Int64(1)]);
        let d2 = Domain::finite(vec![Value::Int64(2)]);

        let intersected = d1.intersect(&d2);
        assert!(intersected.is_empty());
    }

    /// Assign `x` a value and give it a domain so `solve` treats it as a
    /// fully-assigned system rather than stopping at the unassigned branch.
    fn solver_with(constraint: Constraint, var: Variable, value: Value) -> ClpSolver {
        let mut solver = ClpSolver::new();
        solver.add_constraint(constraint);
        solver.set_domain(var, Domain::finite(vec![value.clone()]));
        solver.assign(var, value);
        solver
    }

    #[test]
    fn test_ordering_constraint_violation_is_unsat() {
        let interner = ThreadedRodeo::default();
        let x = Variable::new(interner.get_or_intern("x"));
        let y = Variable::new(interner.get_or_intern("y"));

        // x < y with x = 5, y = 1 was previously reported SAT: the ordering
        // kinds fell into `propagate_constraint`'s catch-all ("no conflict")
        // and nothing else rechecked them before answering.
        let mut solver = ClpSolver::new();
        solver.add_constraint(Constraint::less_than(x, y));
        solver.set_domain(x, Domain::finite(vec![Value::Int64(5)]));
        solver.set_domain(y, Domain::finite(vec![Value::Int64(1)]));
        solver.assign(x, Value::Int64(5));
        solver.assign(y, Value::Int64(1));

        assert!(matches!(solver.solve(), ClpResult::Unsat));
    }

    #[test]
    fn test_ordering_constraint_satisfied_is_sat() {
        let interner = ThreadedRodeo::default();
        let x = Variable::new(interner.get_or_intern("x"));
        let y = Variable::new(interner.get_or_intern("y"));

        let mut solver = ClpSolver::new();
        solver.add_constraint(Constraint::greater_than(y, x));
        solver.set_domain(x, Domain::finite(vec![Value::Int64(1)]));
        solver.set_domain(y, Domain::finite(vec![Value::Int64(5)]));
        solver.assign(x, Value::Int64(1));
        solver.assign(y, Value::Int64(5));

        assert!(matches!(solver.solve(), ClpResult::Sat(_)));
    }

    #[test]
    fn test_ordering_against_constant_is_checked() {
        let interner = ThreadedRodeo::default();
        let x = Variable::new(interner.get_or_intern("x"));

        let constraint = Constraint::compare_const(x, ConstraintKind::LessEqual, Value::Int64(3))
            .expect("LessEqual is an ordering kind");
        let mut solver = solver_with(constraint, x, Value::Int64(4));
        assert!(matches!(solver.solve(), ClpResult::Unsat));

        let constraint = Constraint::compare_const(x, ConstraintKind::LessEqual, Value::Int64(3))
            .expect("LessEqual is an ordering kind");
        let mut solver = solver_with(constraint, x, Value::Int64(3));
        assert!(matches!(solver.solve(), ClpResult::Sat(_)));
    }

    #[test]
    fn test_compare_const_rejects_non_ordering_kinds() {
        let interner = ThreadedRodeo::default();
        let x = Variable::new(interner.get_or_intern("x"));
        assert!(
            Constraint::compare_const(x, ConstraintKind::Equal, Value::Int64(1)).is_none(),
            "an equality is not an ordering constraint"
        );
        assert!(Constraint::compare_const(x, ConstraintKind::Linear, Value::Int64(1)).is_none());
    }

    #[test]
    fn test_ordering_across_numeric_kinds() {
        let interner = ThreadedRodeo::default();
        let x = Variable::new(interner.get_or_intern("x"));

        // `UInt64(2) < Int64(3)` must compare numerically, not by variant rank
        // (which would place every `UInt64` above every `Int64`).
        let constraint = Constraint::compare_const(x, ConstraintKind::LessThan, Value::Int64(3))
            .expect("LessThan is an ordering kind");
        let mut solver = solver_with(constraint, x, Value::UInt64(2));
        assert!(matches!(solver.solve(), ClpResult::Sat(_)));
    }

    #[test]
    fn test_uncomparable_ordering_is_unknown_not_sat() {
        let interner = ThreadedRodeo::default();
        let x = Variable::new(interner.get_or_intern("x"));

        // A symbol has no order relative to an integer; the honest answer is
        // "unknown", never a `Sat` that certifies an unchecked constraint.
        let constraint = Constraint::compare_const(x, ConstraintKind::LessThan, Value::Int64(3))
            .expect("LessThan is an ordering kind");
        let mut solver = solver_with(
            constraint,
            x,
            Value::Symbol(interner.get_or_intern("apple")),
        );
        assert!(matches!(solver.solve(), ClpResult::Unknown));
    }

    #[test]
    fn test_linear_constraint_violation_is_unsat() {
        let interner = ThreadedRodeo::default();
        let x = Variable::new(interner.get_or_intern("x"));
        let y = Variable::new(interner.get_or_intern("y"));

        // 2x + 3y = 12, with x = 1, y = 1 (sum 5). `verify_constraint` used to
        // return an unconditional `true` for `Linear`, so this was reported
        // SAT with a violating assignment.
        let constraint = Constraint::linear(
            vec![x, y],
            vec![
                BigRational::from(BigInt::from(2)),
                BigRational::from(BigInt::from(3)),
            ],
            BigRational::from(BigInt::from(12)),
        );

        let mut solver = ClpSolver::new();
        solver.add_constraint(constraint);
        solver.set_domain(x, Domain::finite(vec![Value::Int64(1)]));
        solver.set_domain(y, Domain::finite(vec![Value::Int64(1)]));
        solver.assign(x, Value::Int64(1));
        solver.assign(y, Value::Int64(1));

        assert!(matches!(solver.solve(), ClpResult::Unsat));
    }

    #[test]
    fn test_linear_constraint_satisfied_is_sat() {
        let interner = ThreadedRodeo::default();
        let x = Variable::new(interner.get_or_intern("x"));
        let y = Variable::new(interner.get_or_intern("y"));

        // 2*3 + 3*2 = 12
        let constraint = Constraint::linear(
            vec![x, y],
            vec![
                BigRational::from(BigInt::from(2)),
                BigRational::from(BigInt::from(3)),
            ],
            BigRational::from(BigInt::from(12)),
        );

        let mut solver = ClpSolver::new();
        solver.add_constraint(constraint);
        solver.set_domain(x, Domain::finite(vec![Value::Int64(3)]));
        solver.set_domain(y, Domain::finite(vec![Value::Int64(2)]));
        solver.assign(x, Value::Int64(3));
        solver.assign(y, Value::Int64(2));

        assert!(matches!(solver.solve(), ClpResult::Sat(_)));
    }

    #[test]
    fn test_linear_constraint_with_non_numeric_value_is_unknown() {
        let interner = ThreadedRodeo::default();
        let x = Variable::new(interner.get_or_intern("x"));

        let constraint = Constraint::linear(
            vec![x],
            vec![BigRational::from(BigInt::from(1))],
            BigRational::from(BigInt::from(1)),
        );
        let mut solver = solver_with(constraint, x, Value::Symbol(interner.get_or_intern("s")));
        assert!(matches!(solver.solve(), ClpResult::Unknown));
    }

    #[test]
    fn test_not_member_violation_is_unsat() {
        let interner = ThreadedRodeo::default();
        let x = Variable::new(interner.get_or_intern("x"));

        let constraint = Constraint::not_member(x, vec![Value::Int64(1), Value::Int64(2)]);
        let mut solver = solver_with(constraint, x, Value::Int64(2));
        assert!(matches!(solver.solve(), ClpResult::Unsat));

        let constraint = Constraint::not_member(x, vec![Value::Int64(1), Value::Int64(2)]);
        let mut solver = solver_with(constraint, x, Value::Int64(3));
        assert!(matches!(solver.solve(), ClpResult::Sat(_)));
    }

    #[test]
    fn test_not_member_empties_finite_domain() {
        let interner = ThreadedRodeo::default();
        let x = Variable::new(interner.get_or_intern("x"));

        let mut solver = ClpSolver::new();
        solver.add_constraint(Constraint::not_member(
            x,
            vec![Value::Int64(1), Value::Int64(2)],
        ));
        // Every candidate is forbidden, so the system is unsatisfiable even
        // before any value is assigned.
        solver.set_domain(x, Domain::finite(vec![Value::Int64(1), Value::Int64(2)]));

        assert!(matches!(solver.solve(), ClpResult::Unsat));
    }

    #[test]
    fn test_not_member_prunes_finite_domain() {
        let interner = ThreadedRodeo::default();
        let x = Variable::new(interner.get_or_intern("x"));

        let mut solver = ClpSolver::new();
        solver.add_constraint(Constraint::not_member(x, vec![Value::Int64(1)]));
        solver.set_domain(x, Domain::finite(vec![Value::Int64(1), Value::Int64(7)]));

        match solver.solve() {
            ClpResult::Sat(assignment) => {
                assert_eq!(assignment.get(&x), Some(&Value::Int64(7)));
            }
            other => panic!("expected SAT with the pruned singleton, got {other:?}"),
        }
    }
}
