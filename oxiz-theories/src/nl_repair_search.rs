//! Model-based satisfiability search for nonlinear integer arithmetic.
//!
//! Cylindrical algebraic decomposition decides QF_NIA-shaped problems by
//! *describing every solution region*, which is exactly the work that makes it
//! expensive: the projection phase is doubly exponential in the variable count
//! and pays that price whether the answer is `sat` or `unsat`. But a `sat`
//! answer does not need a description of the solution set — it needs one point
//! in it. This module is the point-finder.
//!
//! It maintains a single candidate integer assignment and *repairs* it: pick a
//! constraint the current assignment violates, pick a variable that occurs in
//! it, freeze every other variable at its current value (which collapses the
//! multivariate polynomial to a univariate one), and compute the integer values
//! of that variable which would satisfy the constraint. Moving there fixes the
//! chosen constraint and may break others; the move is scored by how many
//! constraints end up violated, and the search keeps the best. That is the
//! model-repair idea behind Z3's model-based arithmetic search and the
//! stochastic-local-search SMT literature (Fröhlich, Biere, Wintersteiger &
//! Hamadi, *Stochastic Local Search for Satisfiability Modulo Theories*, AAAI
//! 2015), specialised here to integer polynomial constraints.
//!
//! ## What it may and may not conclude
//!
//! **Only `sat`.** A repair search that runs out of budget has learned nothing
//! about unsatisfiability — it has only failed to find a point — so this module
//! returns `None` (the caller answers `unknown`) and never `unsat`. Even the
//! `sat` it does return is not taken on trust: the candidate is checked against
//! the *original, unmodified* assertions by [`crate::nl_eval::holds_under`],
//! in exact arithmetic, before it is handed back. Constraints the parser could
//! not turn into polynomial atoms (a disjunction, a `div`, an `ite`) are
//! therefore still enforced — they are simply invisible to the repair
//! heuristic, which costs search power, not soundness.
//!
//! ## Determinism
//!
//! Tie-breaking and noise moves are driven by a fixed-seed xorshift generator
//! carried in the search state, so the same input always produces the same
//! answer. No wall-clock or thread-local state participates.

use crate::nl_eval::{Interpretation, holds_under};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};
use oxiz_core::ast::{TermId, TermKind, TermManager};
use std::collections::HashMap;

/// How much work a search may spend before conceding.
#[derive(Debug, Clone, Copy)]
pub struct Effort {
    /// Repair moves across all restarts.
    pub moves: u64,
    /// Times the assignment may be re-seeded after stalling.
    pub restarts: u32,
    /// Candidate values considered per `(constraint, variable)` pair.
    pub candidates_per_move: usize,
}

impl Default for Effort {
    fn default() -> Self {
        // Sized so a failed search costs a few milliseconds on the shapes this
        // path sees: the per-move cost is dominated by re-scoring every atom,
        // which is linear in the (small) atom count for the ground nonlinear
        // fragment.
        Self {
            moves: 20_000,
            restarts: 24,
            candidates_per_move: 12,
        }
    }
}

/// The relation a normalised atom asserts between its polynomial and zero.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Relation {
    /// `p = 0`
    Zero,
    /// `p ≠ 0`
    Nonzero,
    /// `p ≥ 0`
    AtLeastZero,
    /// `p > 0`
    AboveZero,
}

impl Relation {
    /// Whether a polynomial value satisfies this relation.
    fn accepts(self, value: &BigRational) -> bool {
        match self {
            Relation::Zero => value.is_zero(),
            Relation::Nonzero => !value.is_zero(),
            Relation::AtLeastZero => !value.is_negative(),
            Relation::AboveZero => value.is_positive(),
        }
    }

    /// The relation asserted by this one's negation.
    fn negated(self) -> Self {
        match self {
            Relation::Zero => Relation::Nonzero,
            Relation::Nonzero => Relation::Zero,
            // `not (p ≥ 0)` is `-p > 0`; the sign flip is applied by the
            // caller, which owns the polynomial.
            Relation::AtLeastZero => Relation::AboveZero,
            Relation::AboveZero => Relation::AtLeastZero,
        }
    }
}

/// A product of variables with multiplicities, sorted by term id.
type Monomial = Vec<(TermId, u32)>;

/// A polynomial as a list of `(coefficient, monomial)` terms, each monomial
/// appearing at most once.
#[derive(Debug, Clone, Default)]
struct Poly {
    terms: Vec<(BigInt, Monomial)>,
}

impl Poly {
    fn constant(value: BigInt) -> Self {
        if value.is_zero() {
            return Self::default();
        }
        Self {
            terms: vec![(value, Vec::new())],
        }
    }

    fn variable(term: TermId) -> Self {
        Self {
            terms: vec![(BigInt::one(), vec![(term, 1)])],
        }
    }

    fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    fn add_assign(&mut self, other: &Poly) {
        for (coefficient, monomial) in &other.terms {
            match self.terms.iter_mut().find(|(_, m)| m == monomial) {
                Some(slot) => slot.0 += coefficient,
                None => self.terms.push((coefficient.clone(), monomial.clone())),
            }
        }
        self.terms.retain(|(c, _)| !c.is_zero());
    }

    fn negate(&mut self) {
        for (coefficient, _) in &mut self.terms {
            *coefficient = -core::mem::take(coefficient);
        }
    }

    fn multiply(&self, other: &Poly) -> Poly {
        let mut product = Poly::default();
        for (left_coefficient, left_monomial) in &self.terms {
            for (right_coefficient, right_monomial) in &other.terms {
                let mut monomial = left_monomial.clone();
                for &(term, power) in right_monomial {
                    match monomial.iter_mut().find(|(t, _)| *t == term) {
                        Some(slot) => slot.1 += power,
                        None => monomial.push((term, power)),
                    }
                }
                monomial.sort_unstable_by_key(|&(t, _)| t);
                let coefficient = left_coefficient * right_coefficient;
                match product.terms.iter_mut().find(|(_, m)| *m == monomial) {
                    Some(slot) => slot.0 += &coefficient,
                    None => product.terms.push((coefficient, monomial)),
                }
            }
        }
        product.terms.retain(|(c, _)| !c.is_zero());
        product
    }

    /// Every variable this polynomial mentions, without duplicates.
    fn variables(&self, out: &mut Vec<TermId>) {
        for (_, monomial) in &self.terms {
            for &(term, _) in monomial {
                if !out.contains(&term) {
                    out.push(term);
                }
            }
        }
    }

    /// Value under `assignment`; `None` if some variable is unassigned.
    fn evaluate(&self, assignment: &HashMap<TermId, BigInt>) -> Option<BigInt> {
        let mut total = BigInt::zero();
        for (coefficient, monomial) in &self.terms {
            let mut factor = coefficient.clone();
            for &(term, power) in monomial {
                let value = assignment.get(&term)?;
                for _ in 0..power {
                    factor *= value;
                }
            }
            total += factor;
        }
        Some(total)
    }

    /// Coefficients of this polynomial viewed as a univariate polynomial in
    /// `target`, with every other variable frozen at its assigned value.
    /// Index `d` of the result is the coefficient of `target^d`.
    fn univariate_in(
        &self,
        target: TermId,
        assignment: &HashMap<TermId, BigInt>,
    ) -> Option<Vec<BigInt>> {
        let mut coefficients: Vec<BigInt> = Vec::new();
        for (coefficient, monomial) in &self.terms {
            let mut factor = coefficient.clone();
            let mut degree = 0usize;
            for &(term, power) in monomial {
                if term == target {
                    degree += power as usize;
                    continue;
                }
                let value = assignment.get(&term)?;
                for _ in 0..power {
                    factor *= value;
                }
            }
            if coefficients.len() <= degree {
                coefficients.resize(degree + 1, BigInt::zero());
            }
            coefficients[degree] += factor;
        }
        while coefficients.last().is_some_and(BigInt::is_zero) {
            coefficients.pop();
        }
        Some(coefficients)
    }
}

/// One normalised constraint the repair loop tries to satisfy.
#[derive(Debug, Clone)]
struct Constraint {
    poly: Poly,
    relation: Relation,
}

impl Constraint {
    fn satisfied_by(&self, assignment: &HashMap<TermId, BigInt>) -> bool {
        match self.poly.evaluate(assignment) {
            Some(value) => self.relation.accepts(&BigRational::from_integer(value)),
            // An unevaluable constraint is treated as violated so the search
            // does not mistake an incomplete assignment for a solution; the
            // final verification is what actually decides.
            None => false,
        }
    }
}

/// Turns a raw variable assignment into the interpretation that will be
/// checked against the original assertions.
///
/// The default ([`PlainWitness`]) simply pins each variable to its value, but
/// a caller whose unknowns stand for something structured needs more: the
/// array reduction, for instance, has to turn a value assigned to a `select`
/// term into a *cell* of the underlying array symbol, because that is what the
/// evaluator will consult when it recomputes the assertion. Returning `None`
/// rejects the assignment outright — used when the values cannot form a
/// coherent interpretation at all (two reads of the same cell disagreeing, say).
pub trait WitnessBuilder {
    /// Build the interpretation for `assignment`, or reject it.
    fn build(
        &self,
        assignment: &HashMap<TermId, BigInt>,
        manager: &TermManager,
    ) -> Option<Interpretation>;
}

/// The default witness builder: every unknown is a leaf, pinned to its value.
#[derive(Debug, Clone, Copy, Default)]
pub struct PlainWitness;

impl WitnessBuilder for PlainWitness {
    fn build(
        &self,
        assignment: &HashMap<TermId, BigInt>,
        _manager: &TermManager,
    ) -> Option<Interpretation> {
        let mut interp = Interpretation::empty();
        for (&term, value) in assignment {
            interp.pin_int(term, value.clone());
        }
        Some(interp)
    }
}

/// Extra terms the search may treat as polynomial unknowns even though their
/// head is not a variable — array reads, for example.
pub type Unknowns = std::collections::HashSet<TermId>;

/// Search for an integer assignment satisfying `assertions`.
///
/// Returns a *verified* interpretation, or `None` when the search could not
/// find one within `effort`. `None` never means unsatisfiable.
#[must_use]
pub fn find_integer_model(
    assertions: &[TermId],
    manager: &TermManager,
    effort: Effort,
) -> Option<Interpretation> {
    search(
        assertions,
        assertions,
        manager,
        effort,
        &Unknowns::new(),
        &[],
        &PlainWitness,
    )
}

/// The general form of [`find_integer_model`].
///
/// `search_over` is what the repair heuristic reads constraints from;
/// `verify_against` is what a candidate must satisfy before it is returned.
/// They differ whenever a caller has rewritten the problem into a form the
/// polynomial grammar can drive — the rewrite then needs no trust at all,
/// because the answer is still checked against the untouched original.
///
/// `also_assign` names variables the search must give values to even though no
/// constraint mentions them. That is not a convenience: an array read's
/// *index* disappears from the constraints once the read itself is abstracted
/// into an unknown, yet the witness cannot be built without knowing which cell
/// was read — so the index has to be part of the assignment even though the
/// repair heuristic has nothing to say about it.
#[must_use]
pub fn search(
    search_over: &[TermId],
    verify_against: &[TermId],
    manager: &TermManager,
    effort: Effort,
    unknowns: &Unknowns,
    also_assign: &[TermId],
    witness: &dyn WitnessBuilder,
) -> Option<Interpretation> {
    let assertions = search_over;
    let mut parser = PolyParser::new(manager, unknowns);
    let mut constraints: Vec<Constraint> = Vec::new();
    for &assertion in assertions {
        parser.collect_constraints(assertion, &mut constraints);
    }
    if constraints.is_empty() {
        return None;
    }

    let mut variables: Vec<TermId> = Vec::new();
    for constraint in &constraints {
        constraint.poly.variables(&mut variables);
    }
    for &extra in also_assign {
        if !variables.contains(&extra) {
            variables.push(extra);
        }
    }
    if variables.is_empty() || variables.len() > MAX_VARIABLES {
        return None;
    }
    // Integer search only: a Real-sorted unknown has a continuum of repair
    // targets this module does not model, so it declines rather than round.
    let int_sort = manager.sorts.int_sort;
    if variables
        .iter()
        .any(|&v| manager.get(v).is_none_or(|t| t.sort != int_sort))
    {
        return None;
    }
    variables.sort_unstable();

    let hints = BoundHints::derive(&constraints, &variables);
    let mut repairer = Repairer {
        constraints,
        variables,
        hints,
        assignment: HashMap::new(),
        entropy: 0x9E37_79B9_7F4A_7C15,
        effort,
    };
    repairer.run(verify_against, manager, witness)
}

/// Variables beyond which a repair search is not a good use of the budget:
/// each move re-scores every constraint over every candidate value, so the
/// per-move cost grows with the variable count while the chance of a lucky
/// repair falls.
const MAX_VARIABLES: usize = 64;

/// Per-variable bounds and seed values read off unit constraints.
#[derive(Debug, Default)]
struct BoundHints {
    lower: HashMap<TermId, BigInt>,
    upper: HashMap<TermId, BigInt>,
}

impl BoundHints {
    /// Read `v ≥ c` / `v ≤ c` / `v = c` style unit constraints, which is where
    /// most benchmark problems state the region a solution lives in. Only
    /// constraints that are univariate *and* linear contribute; anything else
    /// is left to the repair loop.
    fn derive(constraints: &[Constraint], variables: &[TermId]) -> Self {
        let mut hints = Self::default();
        for constraint in constraints {
            let mut mentioned: Vec<TermId> = Vec::new();
            constraint.poly.variables(&mut mentioned);
            let [variable] = mentioned[..] else { continue };
            let empty = HashMap::new();
            let Some(coefficients) = constraint.poly.univariate_in(variable, &empty) else {
                continue;
            };
            if coefficients.len() != 2 {
                continue;
            }
            let slope = &coefficients[1];
            let offset = &coefficients[0];
            if slope.is_zero() {
                continue;
            }
            // slope·v + offset  REL  0
            match constraint.relation {
                Relation::Zero => {
                    if let Some(value) = exact_quotient(&-offset.clone(), slope) {
                        hints.lower.insert(variable, value.clone());
                        hints.upper.insert(variable, value);
                    }
                }
                Relation::AtLeastZero | Relation::AboveZero => {
                    let strict = constraint.relation == Relation::AboveZero;
                    if slope.is_positive() {
                        let mut bound = ceil_quotient(&-offset.clone(), slope);
                        if strict && (&bound * slope + offset).is_zero() {
                            bound += BigInt::one();
                        }
                        raise(&mut hints.lower, variable, bound);
                    } else {
                        let mut bound = floor_quotient(&-offset.clone(), slope);
                        if strict && (&bound * slope + offset).is_zero() {
                            bound -= BigInt::one();
                        }
                        lower_to(&mut hints.upper, variable, bound);
                    }
                }
                Relation::Nonzero => {}
            }
        }
        for &variable in variables {
            hints.lower.entry(variable).or_default();
            hints.lower.remove(&variable);
        }
        hints
    }

    /// A starting value for `variable`: inside its known box, as close to zero
    /// as the box allows.
    fn seed(&self, variable: TermId) -> BigInt {
        let low = self.lower.get(&variable);
        let high = self.upper.get(&variable);
        match (low, high) {
            (Some(low), _) if low.is_positive() => low.clone(),
            (_, Some(high)) if high.is_negative() => high.clone(),
            _ => BigInt::zero(),
        }
    }

    /// Clamp `value` into `variable`'s known box.
    fn clamp(&self, variable: TermId, value: BigInt) -> BigInt {
        let mut value = value;
        if let Some(low) = self.lower.get(&variable)
            && value < *low
        {
            value = low.clone();
        }
        if let Some(high) = self.upper.get(&variable)
            && value > *high
        {
            value = high.clone();
        }
        value
    }
}

fn raise(map: &mut HashMap<TermId, BigInt>, key: TermId, value: BigInt) {
    match map.get(&key) {
        Some(existing) if *existing >= value => {}
        _ => {
            map.insert(key, value);
        }
    }
}

fn lower_to(map: &mut HashMap<TermId, BigInt>, key: TermId, value: BigInt) {
    match map.get(&key) {
        Some(existing) if *existing <= value => {}
        _ => {
            map.insert(key, value);
        }
    }
}

/// The repair loop's mutable state.
struct Repairer {
    constraints: Vec<Constraint>,
    variables: Vec<TermId>,
    hints: BoundHints,
    assignment: HashMap<TermId, BigInt>,
    entropy: u64,
    effort: Effort,
}

impl Repairer {
    /// A deterministic pseudo-random `u64` (xorshift64*).
    fn next_entropy(&mut self) -> u64 {
        let mut x = self.entropy;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.entropy = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn pick(&mut self, len: usize) -> usize {
        if len <= 1 {
            return 0;
        }
        (self.next_entropy() % len as u64) as usize
    }

    /// Seed the assignment. `spread` widens the random offset applied to each
    /// variable, so successive restarts explore further from the hinted box.
    fn seed_assignment(&mut self, spread: u32) {
        let variables = self.variables.clone();
        for variable in variables {
            let mut value = self.hints.seed(variable);
            if spread > 0 {
                let magnitude = i64::from(spread).saturating_mul(2).saturating_add(1);
                let offset = (self.next_entropy() % (magnitude as u64 * 2 + 1)) as i64 - magnitude;
                value += BigInt::from(offset);
                value = self.hints.clamp(variable, value);
            }
            self.assignment.insert(variable, value);
        }
    }

    /// Indices of the constraints the current assignment violates.
    fn violations(&self) -> Vec<usize> {
        self.constraints
            .iter()
            .enumerate()
            .filter(|(_, c)| !c.satisfied_by(&self.assignment))
            .map(|(i, _)| i)
            .collect()
    }

    /// How many constraints the current assignment violates.
    fn violation_count(&self) -> usize {
        self.constraints
            .iter()
            .filter(|c| !c.satisfied_by(&self.assignment))
            .count()
    }

    fn run(
        &mut self,
        assertions: &[TermId],
        manager: &TermManager,
        witness: &dyn WitnessBuilder,
    ) -> Option<Interpretation> {
        let mut moves_left = self.effort.moves;
        for restart in 0..=self.effort.restarts {
            self.seed_assignment(restart);
            let mut stalls = 0u32;
            while moves_left > 0 {
                moves_left -= 1;
                let violated = self.violations();
                if violated.is_empty() {
                    if let Some(interp) = self.verified(assertions, manager, witness) {
                        return Some(interp);
                    }
                    // Every polynomial constraint holds yet the formula as a
                    // whole does not (a disjunction or an operator outside the
                    // polynomial grammar). Nudge and keep looking.
                    self.perturb();
                    stalls += 1;
                    if stalls > STALL_LIMIT {
                        break;
                    }
                    continue;
                }
                if self.repair_step(&violated) {
                    stalls = 0;
                } else {
                    self.perturb();
                    stalls += 1;
                    if stalls > STALL_LIMIT {
                        break;
                    }
                }
            }
            if moves_left == 0 {
                break;
            }
        }
        None
    }

    /// Build an interpretation from the current assignment and check it
    /// against the original assertions.
    fn verified(
        &self,
        assertions: &[TermId],
        manager: &TermManager,
        witness: &dyn WitnessBuilder,
    ) -> Option<Interpretation> {
        let interp = witness.build(&self.assignment, manager)?;
        holds_under(assertions, manager, &interp).then_some(interp)
    }

    /// Try one repair move. `true` if the move strictly reduced the number of
    /// violated constraints.
    fn repair_step(&mut self, violated: &[usize]) -> bool {
        let before = violated.len();
        let choice = self.pick(violated.len());
        let Some(&target_constraint) = violated.get(choice) else {
            return false;
        };

        let mut mentioned: Vec<TermId> = Vec::new();
        self.constraints[target_constraint]
            .poly
            .variables(&mut mentioned);
        if mentioned.is_empty() {
            // A violated ground constraint cannot be repaired by any move;
            // the whole polynomial system is refuted for this assignment, but
            // that says nothing about satisfiability, so just report no gain.
            return false;
        }
        mentioned.sort_unstable();

        let mut best: Option<(usize, TermId, BigInt)> = None;
        for &variable in &mentioned {
            let candidates = self.candidate_values(target_constraint, variable);
            for candidate in candidates {
                let Some(previous) = self.assignment.insert(variable, candidate.clone()) else {
                    continue;
                };
                let score = self.violation_count();
                self.assignment.insert(variable, previous);
                let improves = match &best {
                    Some((best_score, _, _)) => score < *best_score,
                    None => true,
                };
                if improves {
                    best = Some((score, variable, candidate));
                }
            }
        }

        let Some((score, variable, value)) = best else {
            return false;
        };
        // Accept an improving move outright; accept a sideways or worsening one
        // only occasionally, which is what lets the search leave a local
        // minimum instead of oscillating in it.
        let accept = score < before || self.next_entropy() % 100 < NOISE_PERCENT;
        if accept {
            self.assignment.insert(variable, value);
        }
        score < before && accept
    }

    /// Randomly displace one variable.
    fn perturb(&mut self) {
        if self.variables.is_empty() {
            return;
        }
        let index = self.pick(self.variables.len());
        let Some(&variable) = self.variables.get(index) else {
            return;
        };
        let delta = (self.next_entropy() % 9) as i64 - 4;
        let current = self.assignment.get(&variable).cloned().unwrap_or_default();
        let moved = self.hints.clamp(variable, current + BigInt::from(delta));
        self.assignment.insert(variable, moved);
    }

    /// Integer values of `variable` worth trying for constraint `index`, with
    /// every other variable frozen.
    ///
    /// The list always contains a small neighbourhood of the current value
    /// (cheap, and often enough for a linear constraint), plus the exact
    /// solutions of the collapsed univariate polynomial when its degree makes
    /// those computable.
    fn candidate_values(&mut self, index: usize, variable: TermId) -> Vec<BigInt> {
        let Some(constraint) = self.constraints.get(index) else {
            return Vec::new();
        };
        let Some(coefficients) = constraint.poly.univariate_in(variable, &self.assignment) else {
            return Vec::new();
        };
        let relation = constraint.relation;
        let current = self.assignment.get(&variable).cloned().unwrap_or_default();

        let mut candidates: Vec<BigInt> = Vec::new();
        let mut offer = |value: BigInt| {
            if !candidates.contains(&value) {
                candidates.push(value);
            }
        };

        match coefficients.len() {
            // Constant in `variable`: moving it cannot help this constraint.
            0 | 1 => return Vec::new(),
            2 => {
                let slope = &coefficients[1];
                let offset = &coefficients[0];
                for value in linear_targets(slope, offset, relation) {
                    offer(value);
                }
            }
            3 => {
                let a = &coefficients[2];
                let b = &coefficients[1];
                let c = &coefficients[0];
                for root in quadratic_roots(a, b, c) {
                    offer(root.clone());
                    offer(root.clone() + BigInt::one());
                    offer(root - BigInt::one());
                }
            }
            _ => {
                // Degree three or more: the rational-root theorem bounds the
                // integer roots of `p = 0` to the divisors of its constant
                // term, which is a short list for the coefficient sizes these
                // problems produce.
                if let Some(constant) = coefficients.first()
                    && !constant.is_zero()
                {
                    for divisor in small_divisors(constant) {
                        offer(divisor.clone());
                        offer(-divisor);
                    }
                } else {
                    offer(BigInt::zero());
                }
            }
        }

        for step in 1..=3i64 {
            offer(current.clone() + BigInt::from(step));
            offer(current.clone() - BigInt::from(step));
        }
        offer(BigInt::zero());
        if let Some(low) = self.hints.lower.get(&variable) {
            offer(low.clone());
        }
        if let Some(high) = self.hints.upper.get(&variable) {
            offer(high.clone());
        }

        let limit = self.effort.candidates_per_move;
        candidates
            .into_iter()
            .map(|value| self.hints.clamp(variable, value))
            .filter(|value| {
                // Keep only values that actually satisfy the target constraint;
                // a move that does not fix what it was chosen for is wasted.
                evaluate_univariate(&coefficients, value)
                    .is_some_and(|v| relation.accepts(&BigRational::from_integer(v)))
            })
            .take(limit)
            .collect()
    }
}

/// Repair moves without progress before a restart.
const STALL_LIMIT: u32 = 40;
/// Percentage chance of accepting a non-improving move.
const NOISE_PERCENT: u64 = 12;

/// Values satisfying `slope·v + offset REL 0`.
fn linear_targets(slope: &BigInt, offset: &BigInt, relation: Relation) -> Vec<BigInt> {
    if slope.is_zero() {
        return Vec::new();
    }
    let numerator = -offset.clone();
    match relation {
        Relation::Zero => exact_quotient(&numerator, slope).into_iter().collect(),
        Relation::Nonzero => match exact_quotient(&numerator, slope) {
            Some(root) => vec![root.clone() + BigInt::one(), root - BigInt::one()],
            None => vec![BigInt::zero()],
        },
        Relation::AtLeastZero | Relation::AboveZero => {
            let strict = relation == Relation::AboveZero;
            if slope.is_positive() {
                let mut bound = ceil_quotient(&numerator, slope);
                if strict && (&bound * slope + offset).is_zero() {
                    bound += BigInt::one();
                }
                vec![bound.clone(), bound + BigInt::one()]
            } else {
                let mut bound = floor_quotient(&numerator, slope);
                if strict && (&bound * slope + offset).is_zero() {
                    bound -= BigInt::one();
                }
                vec![bound.clone(), bound - BigInt::one()]
            }
        }
    }
}

/// Integer roots of `a·v² + b·v + c`, when the discriminant is a perfect
/// square. An empty result only means "no integer root was computable"; the
/// caller still offers neighbourhood values.
fn quadratic_roots(a: &BigInt, b: &BigInt, c: &BigInt) -> Vec<BigInt> {
    if a.is_zero() {
        return exact_quotient(&-c.clone(), b).into_iter().collect();
    }
    let discriminant = b * b - BigInt::from(4) * a * c;
    if discriminant.is_negative() {
        return Vec::new();
    }
    let Some(root) = integer_sqrt(&discriminant) else {
        return Vec::new();
    };
    let two_a = BigInt::from(2) * a;
    let mut out = Vec::new();
    for numerator in [-b.clone() + &root, -b.clone() - &root] {
        if let Some(value) = exact_quotient(&numerator, &two_a)
            && !out.contains(&value)
        {
            out.push(value);
        }
    }
    // Also offer the vertex, which is where an inequality flips sign even when
    // the roots are not integral.
    let vertex = floor_quotient(&-b.clone(), &two_a);
    if !out.contains(&vertex) {
        out.push(vertex);
    }
    out
}

/// Exact integer square root of a non-negative value, or `None` if `value` is
/// not a perfect square. Newton's method on integers, so exact for any size.
fn integer_sqrt(value: &BigInt) -> Option<BigInt> {
    if value.is_negative() {
        return None;
    }
    if value.is_zero() {
        return Some(BigInt::zero());
    }
    let mut guess = BigInt::one() << ((value.bits() / 2) + 1);
    loop {
        let next = (&guess + value / &guess) >> 1;
        if next >= guess {
            break;
        }
        guess = next;
    }
    (&guess * &guess == *value).then_some(guess)
}

/// `numerator / divisor` when the division is exact.
fn exact_quotient(numerator: &BigInt, divisor: &BigInt) -> Option<BigInt> {
    if divisor.is_zero() {
        return None;
    }
    let quotient = numerator / divisor;
    (&quotient * divisor == *numerator).then_some(quotient)
}

/// `ceil(numerator / divisor)` for a nonzero divisor.
fn ceil_quotient(numerator: &BigInt, divisor: &BigInt) -> BigInt {
    let quotient = numerator / divisor;
    let remainder = numerator - &quotient * divisor;
    if remainder.is_zero() {
        return quotient;
    }
    if (remainder.is_positive()) == (divisor.is_positive()) {
        quotient + BigInt::one()
    } else {
        quotient
    }
}

/// `floor(numerator / divisor)` for a nonzero divisor.
fn floor_quotient(numerator: &BigInt, divisor: &BigInt) -> BigInt {
    let quotient = numerator / divisor;
    let remainder = numerator - &quotient * divisor;
    if remainder.is_zero() {
        return quotient;
    }
    if (remainder.is_positive()) == (divisor.is_positive()) {
        quotient
    } else {
        quotient - BigInt::one()
    }
}

/// Positive divisors of `value`, capped so a large constant term cannot turn
/// candidate generation into a factorisation problem.
fn small_divisors(value: &BigInt) -> Vec<BigInt> {
    let mut out = vec![BigInt::one()];
    let Some(magnitude) = value.abs().to_u64() else {
        return out;
    };
    if magnitude > DIVISOR_SCAN_LIMIT {
        return out;
    }
    let mut d = 1u64;
    while d * d <= magnitude && out.len() < MAX_DIVISORS {
        if magnitude % d == 0 {
            let quotient = magnitude / d;
            for found in [d, quotient] {
                let found = BigInt::from(found);
                if !out.contains(&found) {
                    out.push(found);
                }
            }
        }
        d += 1;
    }
    out
}

/// Above this magnitude, trial division of the constant term is not worth the
/// budget it would consume.
const DIVISOR_SCAN_LIMIT: u64 = 1 << 20;
/// Divisors kept from one constant term.
const MAX_DIVISORS: usize = 32;

/// Horner evaluation of a univariate polynomial given by ascending
/// coefficients.
fn evaluate_univariate(coefficients: &[BigInt], at: &BigInt) -> Option<BigInt> {
    let mut total = BigInt::zero();
    for coefficient in coefficients.iter().rev() {
        total = total * at + coefficient;
    }
    Some(total)
}

/// Turns assertion terms into normalised polynomial constraints.
struct PolyParser<'a> {
    manager: &'a TermManager,
    /// Memo over the hash-consed DAG, so a shared sub-term is translated once.
    memo: HashMap<TermId, Option<Poly>>,
    /// Terms the caller has declared to be unknowns in their own right; see
    /// [`Unknowns`].
    unknowns: &'a Unknowns,
}

impl<'a> PolyParser<'a> {
    fn new(manager: &'a TermManager, unknowns: &'a Unknowns) -> Self {
        Self {
            manager,
            memo: HashMap::new(),
            unknowns,
        }
    }

    /// Add every polynomial constraint `term` asserts.
    ///
    /// Descends the conjunctive spine (`and`, and `not` over comparisons)
    /// iteratively; anything else contributes no constraint and is left to the
    /// final verification.
    fn collect_constraints(&mut self, term: TermId, out: &mut Vec<Constraint>) {
        let mut work: Vec<(TermId, bool)> = vec![(term, true)];
        let mut seen: std::collections::HashSet<(TermId, bool)> = std::collections::HashSet::new();
        while let Some((current, positive)) = work.pop() {
            if !seen.insert((current, positive)) {
                continue;
            }
            let Some(node) = self.manager.get(current) else {
                continue;
            };
            let kind = node.kind.clone();
            match &kind {
                TermKind::Not(inner) => work.push((*inner, !positive)),
                TermKind::And(args) if positive => {
                    work.extend(args.iter().map(|&a| (a, true)));
                }
                TermKind::Or(args) if !positive => {
                    work.extend(args.iter().map(|&a| (a, false)));
                }
                TermKind::Eq(lhs, rhs) => {
                    if let Some(poly) = self.difference(*lhs, *rhs) {
                        let relation = if positive {
                            Relation::Zero
                        } else {
                            Relation::Nonzero
                        };
                        out.push(Constraint { poly, relation });
                    }
                }
                TermKind::Ge(lhs, rhs) => self.push_comparison(*lhs, *rhs, false, positive, out),
                TermKind::Gt(lhs, rhs) => self.push_comparison(*lhs, *rhs, true, positive, out),
                TermKind::Le(lhs, rhs) => self.push_comparison(*rhs, *lhs, false, positive, out),
                TermKind::Lt(lhs, rhs) => self.push_comparison(*rhs, *lhs, true, positive, out),
                _ => {}
            }
        }
    }

    /// Record `lhs - rhs ≥ 0` (or `> 0`), negating it when `positive` is false.
    fn push_comparison(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        strict: bool,
        positive: bool,
        out: &mut Vec<Constraint>,
    ) {
        let Some(mut poly) = self.difference(lhs, rhs) else {
            return;
        };
        let base = if strict {
            Relation::AboveZero
        } else {
            Relation::AtLeastZero
        };
        let relation = if positive {
            base
        } else {
            // `not (p ≥ 0)` is `-p > 0`; `not (p > 0)` is `-p ≥ 0`.
            poly.negate();
            base.negated()
        };
        out.push(Constraint { poly, relation });
    }

    /// `lhs - rhs` as a polynomial, or `None` when either side is outside the
    /// polynomial grammar.
    fn difference(&mut self, lhs: TermId, rhs: TermId) -> Option<Poly> {
        let left = self.translate(lhs)?;
        let mut right = self.translate(rhs)?;
        right.negate();
        let mut result = left;
        result.add_assign(&right);
        Some(result)
    }

    /// Translate an arithmetic term to a polynomial.
    ///
    /// Iterative post-order over the DAG with memoisation, so nesting depth
    /// costs heap rather than native stack and a shared sub-term is translated
    /// once. `Var` and numeric uninterpreted applications become polynomial
    /// unknowns; every other head (`div`, `mod`, `ite`, `select`, a non-numeric
    /// sort) makes the whole translation `None`.
    fn translate(&mut self, root: TermId) -> Option<Poly> {
        enum Task {
            Open(TermId),
            Close(TermId),
        }
        let mut work = vec![Task::Open(root)];
        while let Some(task) = work.pop() {
            match task {
                Task::Open(id) => {
                    if self.memo.contains_key(&id) {
                        continue;
                    }
                    if self.unknowns.contains(&id) {
                        // A declared unknown is a leaf whatever its head is;
                        // descending into it would translate its internals as
                        // if they were arithmetic.
                        self.memo.insert(id, Some(Poly::variable(id)));
                        continue;
                    }
                    let kind = self.manager.get(id).map(|t| t.kind.clone())?;
                    let mut operands: Vec<TermId> = Vec::new();
                    match &kind {
                        TermKind::Neg(a) => operands.push(*a),
                        TermKind::Add(args) | TermKind::Mul(args) => {
                            operands.extend(args.iter().copied());
                        }
                        TermKind::Sub(a, b) => {
                            operands.push(*a);
                            operands.push(*b);
                        }
                        _ => {}
                    }
                    work.push(Task::Close(id));
                    for operand in operands {
                        work.push(Task::Open(operand));
                    }
                }
                Task::Close(id) => {
                    if self.memo.contains_key(&id) {
                        continue;
                    }
                    let value = self.fold(id);
                    self.memo.insert(id, value);
                }
            }
        }
        self.memo.get(&root).cloned().flatten()
    }

    /// Combine a node's already-translated operands.
    fn fold(&self, id: TermId) -> Option<Poly> {
        let node = self.manager.get(id)?;
        let operand = |t: TermId| self.memo.get(&t).cloned().flatten();
        match &node.kind {
            TermKind::IntConst(n) => Some(Poly::constant(n.clone())),
            TermKind::Neg(a) => {
                let mut poly = operand(*a)?;
                poly.negate();
                Some(poly)
            }
            TermKind::Add(args) => {
                let mut total = Poly::default();
                for &a in args {
                    total.add_assign(&operand(a)?);
                }
                Some(total)
            }
            TermKind::Sub(a, b) => {
                let mut total = operand(*a)?;
                let mut negated = operand(*b)?;
                negated.negate();
                total.add_assign(&negated);
                Some(total)
            }
            TermKind::Mul(args) => {
                let mut product = Poly::constant(BigInt::one());
                for &a in args {
                    product = product.multiply(&operand(a)?);
                    if product.is_zero() {
                        return Some(product);
                    }
                    if product.terms.len() > MAX_POLY_TERMS {
                        return None;
                    }
                }
                Some(product)
            }
            // An Int-sorted `Var` is a polynomial unknown. Everything else —
            // including a `Real` variable, a `select`, an application, `div`,
            // `mod` and `ite` — is outside this grammar; the containing atom
            // is dropped from the repair set and enforced by verification.
            TermKind::Var(_) if node.sort == self.manager.sorts.int_sort => {
                Some(Poly::variable(id))
            }
            _ if self.unknowns.contains(&id) => Some(Poly::variable(id)),
            _ => None,
        }
    }
}

/// Ceiling on the size of an expanded product, so a chain of multiplied sums
/// cannot blow the term list up before the search even starts.
const MAX_POLY_TERMS: usize = 4_096;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nl_eval::holds_under;

    fn int_var(tm: &mut TermManager, name: &str) -> TermId {
        let sort = tm.sorts.int_sort;
        tm.mk_var(name, sort)
    }

    #[test]
    fn test_pr31_repair_finds_product_witness() {
        let mut tm = TermManager::new();
        let x = int_var(&mut tm, "px");
        let y = int_var(&mut tm, "py");
        let two = tm.mk_int(2);
        let twelve = tm.mk_int(12);
        let product = tm.mk_mul(vec![x, y]);
        let assertions = vec![
            tm.mk_eq(product, twelve),
            tm.mk_ge(x, two),
            tm.mk_ge(y, two),
        ];
        let interp = find_integer_model(&assertions, &tm, Effort::default())
            .expect("x*y = 12 with both factors at least 2 has a witness");
        assert!(holds_under(&assertions, &tm, &interp));
    }

    #[test]
    fn test_pr31_repair_finds_negative_square_root() {
        let mut tm = TermManager::new();
        let x = int_var(&mut tm, "sx");
        let square = tm.mk_mul(vec![x, x]);
        let forty_nine = tm.mk_int(49);
        let zero = tm.mk_int(0);
        let assertions = vec![tm.mk_eq(square, forty_nine), tm.mk_lt(x, zero)];
        let interp = find_integer_model(&assertions, &tm, Effort::default())
            .expect("x*x = 49 with x < 0 is solved by x = -7");
        assert!(holds_under(&assertions, &tm, &interp));
        assert_eq!(
            interp.num_of(x).map(|v| v.to_integer()),
            Some(BigInt::from(-7))
        );
    }

    #[test]
    fn test_pr31_repair_finds_mixed_sign_quadratic() {
        let mut tm = TermManager::new();
        let x = int_var(&mut tm, "qx");
        let square = tm.mk_mul(vec![x, x]);
        let three = tm.mk_int(3);
        let three_x = tm.mk_mul(vec![three, x]);
        let sum = tm.mk_add(vec![square, three_x]);
        let target = tm.mk_int(-2);
        let assertions = vec![tm.mk_eq(sum, target)];
        let interp = find_integer_model(&assertions, &tm, Effort::default())
            .expect("x^2 + 3x = -2 is solved by x = -1 and x = -2");
        assert!(holds_under(&assertions, &tm, &interp));
    }

    #[test]
    fn test_pr31_repair_never_claims_unsatisfiable() {
        // An unsatisfiable system: the search must simply fail to find a
        // model, and its only failure signal is `None`.
        let mut tm = TermManager::new();
        let x = int_var(&mut tm, "ux");
        let square = tm.mk_mul(vec![x, x]);
        let target = tm.mk_int(-1);
        let assertions = vec![tm.mk_eq(square, target)];
        let effort = Effort {
            moves: 400,
            restarts: 2,
            candidates_per_move: 8,
        };
        assert!(find_integer_model(&assertions, &tm, effort).is_none());
    }

    #[test]
    fn test_pr31_repair_rejects_real_sorted_unknowns() {
        let mut tm = TermManager::new();
        let real_sort = tm.sorts.real_sort;
        let x = tm.mk_var("rx", real_sort);
        let square = tm.mk_mul(vec![x, x]);
        let four = tm.mk_int(4);
        let assertions = vec![tm.mk_eq(square, four)];
        assert!(find_integer_model(&assertions, &tm, Effort::default()).is_none());
    }

    #[test]
    fn test_pr31_repair_respects_unmodelled_conjunct() {
        // `x*y = 6` is in the polynomial grammar; the `div` conjunct is not.
        // The search may only report success once the *whole* assertion set
        // verifies, so a witness it returns satisfies the `div` too.
        let mut tm = TermManager::new();
        let x = int_var(&mut tm, "dx");
        let y = int_var(&mut tm, "dy");
        let six = tm.mk_int(6);
        let three = tm.mk_int(3);
        let product = tm.mk_mul(vec![x, y]);
        let quotient = tm.mk_div(x, three);
        let one = tm.mk_int(1);
        let assertions = vec![
            tm.mk_eq(product, six),
            tm.mk_eq(quotient, one),
            tm.mk_ge(x, one),
        ];
        if let Some(interp) = find_integer_model(&assertions, &tm, Effort::default()) {
            assert!(holds_under(&assertions, &tm, &interp));
        }
    }
}
