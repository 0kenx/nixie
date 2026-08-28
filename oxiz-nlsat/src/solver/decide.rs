//! Decision making and feasibility region computation for the NLSAT solver.
//!
//! Implements variable ordering, decision heuristics (VSIDS), phase saving,
//! and cylindrical algebraic decomposition (CAD) projection for feasibility.

use super::NlsatSolver;
use super::witness_algebraic::AlgebraicWitness;
use crate::cad::SturmSequence;
use crate::interval_set::IntervalSet;
use crate::types::{Atom, AtomKind, BoolVar, IneqAtom, Literal};
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use oxiz_math::interval::Interval;
use oxiz_math::polynomial::{Polynomial, Var};
use rustc_hash::{FxHashMap, FxHashSet};

/// Outcome of trying to pick a value for an arithmetic variable.
///
/// The NLSAT search assigns arithmetic variables to concrete rational sample
/// points taken from sign-invariant cells. When no rational witness exists we
/// must distinguish *why* so that the caller never reports a silently wrong
/// answer:
///
/// * `Value` – a rational witness that provably lies inside the true feasible
///   region of every currently-assigned constraint on the variable.
/// * `ProvedEmpty` – the constraints on this variable that mention *only* this
///   variable are jointly infeasible over the reals (verified exactly via Sturm
///   root isolation). The attached literals form a valid theory lemma
///   (`¬l_1 ∨ … ∨ ¬l_k`) that can be learned and back-jumped over.
/// * `AlgebraicValue` – the true real feasible region is non-empty but contains
///   no rational point (e.g. `x^2 = 2`), and an exact real-algebraic witness
///   for it *was* found. See `solver/witness_algebraic.rs`.
/// * `IrrationalOnly` – as above, but no algebraic witness could be produced
///   *and* emptiness could not be proved either: the exact sign machinery ran
///   out of refinement budget, or a second algebraic value would have been
///   needed. The honest answer is `Unknown` rather than a fabricated model or
///   a wrong `Unsat`.
/// * `GreedyEmpty` – the intersection is empty but involves a constraint that
///   couples this variable with earlier-assigned variables, so emptiness is
///   conditional on those (greedy) choices and cannot be turned into a valid
///   variable-local lemma.
pub(super) enum ArithDecision {
    /// A concrete rational witness inside the feasible region.
    Value(BigRational),
    /// An exact real-algebraic witness (defining polynomial + isolating
    /// interval), committed for a variable whose feasible set holds no
    /// rational point. (Ported from upstream v0.3.3.)
    AlgebraicValue { point: crate::cad::CadPoint },
    /// Provably infeasible over the reals; carries a valid conflict lemma.
    ProvedEmpty(Vec<Literal>),
    /// Feasible over the reals but with no rational witness (algebraic only).
    IrrationalOnly,
    /// Empty under the current greedy assignment; not provably a global lemma.
    GreedyEmpty,
}

/// Feasible-region information for a single arithmetic variable, accumulated
/// across all currently-assigned constraints that mention it.
pub(super) struct ArithRegions {
    /// Rational witnesses guaranteed to be a subset of the true feasible set.
    pub(super) inner: IntervalSet,
    /// A superset of the true feasible set (used only to certify emptiness).
    pub(super) outer: IntervalSet,
    /// Literals (already negated) of the constraints that were intersected.
    pub(super) blame: Vec<Literal>,
    /// True iff every intersected constraint mentions *only* this variable.
    pub(super) pure: bool,
    /// True iff emptiness of `outer` can be trusted (roots fully isolated).
    pub(super) reliable: bool,
    /// Every arithmetic variable mentioned by an intersected (blame)
    /// constraint.  On a greedy cell failure these are the only variables
    /// whose re-sampling can possibly fix the cell, so the chronological
    /// resampler jumps straight to the newest of them.
    pub(super) blame_vars: Vec<Var>,
}

impl NlsatSolver {
    /// Make a decision.
    pub(super) fn decide(&mut self) -> Option<Literal> {
        // Random decision
        if self.config.random_decisions
            && self.random() < self.config.random_freq
            && let Some(lit) = self.random_decision()
        {
            return Some(lit);
        }

        // VSIDS-like decision: pick the unassigned variable with highest activity
        let mut best_var: Option<BoolVar> = None;
        let mut best_activity = f64::NEG_INFINITY;

        for var in 0..self.num_bool_vars {
            if self.assignment.is_bool_assigned(var) {
                continue;
            }

            let activity = self.var_activity.get(var as usize).copied().unwrap_or(0.0);
            if activity > best_activity {
                best_activity = activity;
                best_var = Some(var);
            }
        }

        best_var.map(|var| {
            // Use saved phase (phase saving heuristic)
            let polarity = self.saved_phase.get(var as usize).copied().unwrap_or(true);
            Literal::new(var, polarity)
        })
    }

    /// Save the phase (polarity) of a literal assignment.
    pub(super) fn save_phase(&mut self, lit: Literal) {
        let var = lit.var();
        let polarity = !lit.is_negated();
        if (var as usize) < self.saved_phase.len() {
            self.saved_phase[var as usize] = polarity;
        }
    }

    /// Make a random decision.
    pub(super) fn random_decision(&mut self) -> Option<Literal> {
        let mut unassigned = Vec::new();
        for var in 0..self.num_bool_vars {
            if !self.assignment.is_bool_assigned(var) {
                unassigned.push(var);
            }
        }

        if unassigned.is_empty() {
            return None;
        }

        let idx = (self.random_int() as usize) % unassigned.len();
        let var = unassigned[idx];
        let positive = self.random_int().is_multiple_of(2);

        Some(if positive {
            Literal::positive(var)
        } else {
            Literal::negative(var)
        })
    }

    /// Get the next arithmetic variable to assign.
    pub(super) fn next_arith_var(&self) -> Option<Var> {
        // Return the first unassigned variable in the ordering
        self.var_order
            .iter()
            .find(|&&var| !self.assignment.is_arith_assigned(var))
            .copied()
    }

    /// Commit a rational sample for `var`, recording it on the arithmetic trail
    /// so a later cell failure can re-sample this variable.
    pub(super) fn commit_arith_sample(&mut self, var: Var, value: BigRational) {
        let regions = self.compute_arith_regions(var);
        let forced = regions.inner.as_singleton().is_some();
        if let Some(frame) = self.arith_trail.last_mut()
            && frame.var == var
        {
            if !frame.tried.iter().any(|t| t == &value) {
                frame.tried.push(value.clone());
            }
            self.assignment.set_arith(var, value);
            self.eval_cache.clear();
            return;
        }
        self.arith_trail.push(super::ArithTrailFrame {
            var,
            region: regions.inner,
            tried: vec![value.clone()],
            forced,
        });
        self.assignment.set_arith(var, value);
        self.eval_cache.clear();
    }

    /// Undo the latest greedy arithmetic sample and try another point from the
    /// same feasible region. Returns `true` if a fresh sample was committed.
    ///
    /// Walks up the arithmetic trail when a frame's region is exhausted. Does
    /// **not** report global unsat: running out of rational samples is
    /// incompleteness, not a proof.
    pub(super) fn resample_previous_arith(&mut self) -> bool {
        // Conflict-directed backjumping: the failing cell can only be
        // repaired by re-sampling a variable that appears in one of its
        // blame constraints (`last_blame_vars`).  Skip trail frames whose
        // variable is unrelated instead of unwinding them one by one –
        // with the VeryMax coupled-monomial goals, chronological unwinding
        // burns the whole resample budget before reaching the culprit
        // (observed: 10 001 identical `GreedyEmpty` escapes).
        let blame = std::mem::take(&mut self.last_blame_vars);
        while !self.arith_trail.is_empty() {
            if self.arith_resample_budget == 0 {
                self.last_blame_vars = blame;
                return false;
            }
            let frame = self.arith_trail.last_mut().expect("trail non-empty");
            let var = frame.var;
            // When blame information is available, only stop at a blamable
            // frame (or when the trail is exhausted).  Without blame info,
            // keep the original chronological behaviour.
            //
            // A frame that has already been re-sampled several times without
            // resolving the failure is also skipped: unbounded regions
            // (`sample_excluding` enumerates 0, 1, 2, … forever on a ray)
            // would otherwise pin the resampler to the newest blamable
            // variable indefinitely, and the *older* blame variables – often
            // the real culprits – are never revisited.
            const MAX_FRAME_RETRIES: usize = 6;
            if !blame.is_empty()
                && (!blame.contains(&var) || frame.tried.len() >= MAX_FRAME_RETRIES)
            {
                self.assignment.unset_arith(var);
                self.eval_cache.clear();
                self.arith_trail.pop();
                continue;
            }
            self.assignment.unset_arith(var);
            // Also drop any later arith assignments not on the trail (none
            // expected) and clear dependent theory state.
            self.eval_cache.clear();

            if let Some(next) = frame.region.sample_excluding(&frame.tried) {
                self.arith_resample_budget -= 1;
                frame.tried.push(next.clone());
                self.assignment.set_arith(var, next);
                self.last_blame_vars = blame;
                return true;
            }
            // This cell is exhausted – pop and try the parent sample.
            self.arith_trail.pop();
        }
        self.last_blame_vars = blame;
        false
    }

    /// Pick a value for an arithmetic variable.
    ///
    /// Returns an [`ArithDecision`] that distinguishes a concrete rational
    /// witness from the various flavours of "no rational value" so the caller
    /// can react soundly (learn a lemma, back-jump, or report `Unknown`) instead
    /// of collapsing every failure into a wrong `Unsat`.
    pub(super) fn pick_arith_value(&mut self, var: Var) -> ArithDecision {
        let regions = self.compute_arith_regions(var);
        // Remember which *other* variables the intersected (blame)
        // constraints mention: a cell failure here can only be repaired by
        // re-sampling one of them, which lets the chronological resampler
        // backjump instead of unwinding the whole trail one frame at a time
        // (the VeryMax coupled-monomial goals otherwise burn their entire
        // resample budget walking back through unrelated variables).
        self.last_blame_vars = regions.blame_vars.clone();

        // A rational witness inside `inner` satisfies every intersected
        // constraint by construction, so it is always safe to commit to it.
        // Prefer integers / non-zero samples so multivariate products do not
        // degenerate on the first greedy choice (see `IntervalSet::sample_excluding`).
        if !regions.inner.is_empty()
            && let Some(value) = regions.inner.sample_excluding(&[])
        {
            return ArithDecision::Value(value);
        }

        if self.config.early_termination {
            self.stats.early_terminations += 1;
        }

        // No rational witness. Classify the emptiness.
        if regions.reliable && regions.outer.is_empty() {
            if regions.pure {
                // The pure single-variable constraints are jointly infeasible
                // over the reals: `¬l_1 ∨ … ∨ ¬l_k` is a valid theory lemma.
                return ArithDecision::ProvedEmpty(regions.blame);
            }
            // Coupled constraints substituted to an empty reliable cell. If
            // every earlier arithmetic sample was *forced* (singleton region),
            // the boolean atom assignment alone is theory-unsat and the
            // negation of all assigned theory literals is a valid lemma
            // (e.g. `x=2 ∧ x²+y²=1`). Free greedy samples must not be blamed.
            if !regions.blame.is_empty()
                && self.arith_trail.iter().all(|f| f.forced)
                && let Some(lemma) = self.lemma_negating_assigned_theory_lits()
            {
                return ArithDecision::ProvedEmpty(lemma);
            }
        }
        if regions.pure && regions.reliable && !regions.outer.is_empty() {
            // Real solutions exist but none are rational (algebraic only).
            // Try for an exact real-algebraic witness before conceding: the
            // candidate walk over the cells of the sign-invariant
            // decomposition is a decision procedure for this (pure) case, so
            // exhausting it without a satisfying cell is a *proof* of
            // emptiness, not a shrug. (Ported from upstream v0.3.3.)
            return match self.sample_algebraic_witness(var) {
                AlgebraicWitness::Found(point) => ArithDecision::AlgebraicValue { point },
                AlgebraicWitness::NoRealPoint(lemma) => ArithDecision::ProvedEmpty(lemma),
                AlgebraicWitness::Inconclusive => ArithDecision::IrrationalOnly,
            };
        }

        // Emptiness is conditional on earlier greedy variable choices (the
        // constraints on `var` couple it with already-assigned variables), so
        // it cannot be certified as a variable-local Sturm lemma. Before giving
        // up, attempt a sound *sign-abstraction* certification of GLOBAL
        // infeasibility over the coupled atoms (see `certify_sign_conflict`):
        // when it succeeds the negated-atom clause it returns is a genuine
        // theory lemma we can learn and back-jump over, recovering completeness
        // on multivariate coupled conflicts instead of reporting Unknown.
        if let Some(lemma) = self.certify_sign_conflict() {
            return ArithDecision::ProvedEmpty(lemma);
        }
        // Magnitude reasoning for positive-bound product equalities
        // (e.g. x>1 ∧ y>1 ∧ x·y=1), which pure sign sets cannot refute.
        if let Some(lemma) = self.certify_product_bound_conflict() {
            return ArithDecision::ProvedEmpty(lemma);
        }
        // Linear sum lower-bound conflict: x>a ∧ y>b ∧ x+y<c with a+b≥c.
        if let Some(lemma) = self.certify_linear_sum_bound_conflict() {
            return ArithDecision::ProvedEmpty(lemma);
        }

        ArithDecision::GreedyEmpty
    }

    /// Negation of every currently assigned inequality-atom literal. Valid as a
    /// theory lemma only when the arithmetic model is fully forced by those
    /// atoms (see the `forced` trail flag); callers must check that.
    fn lemma_negating_assigned_theory_lits(&self) -> Option<Vec<Literal>> {
        let mut lemma = Vec::new();
        for atom in &self.atoms {
            let Atom::Ineq(ineq) = atom else {
                continue;
            };
            let val = self.assignment.bool_value(ineq.bool_var);
            if val.is_true() {
                lemma.push(Literal::negative(ineq.bool_var));
            } else if val.is_false() {
                lemma.push(Literal::positive(ineq.bool_var));
            }
        }
        if lemma.is_empty() { None } else { Some(lemma) }
    }

    /// Certify `x > a ∧ y > b ∧ x + y < c` (and non-strict variants) when the
    /// bounds force `a+b ≥ c` (strictness-adjusted).
    pub(super) fn certify_linear_sum_bound_conflict(&self) -> Option<Vec<Literal>> {
        // lowers: var → (bound, strict, lit)
        let mut lowers: FxHashMap<Var, (BigRational, bool, Literal)> = FxHashMap::default();
        // upper bounds on sums: (vars, bound, strict, lit) for v1+v2+… < / ≤ bound
        let mut sum_uppers: Vec<(Vec<Var>, BigRational, bool, Literal)> = Vec::new();

        for atom in &self.atoms {
            let Atom::Ineq(ineq) = atom else {
                continue;
            };
            if ineq.factors.len() != 1 {
                continue;
            }
            let val = self.assignment.bool_value(ineq.bool_var);
            if val.is_undef() {
                continue;
            }
            let is_true = val.is_true();
            let lit = if is_true {
                Literal::positive(ineq.bool_var)
            } else {
                Literal::negative(ineq.bool_var)
            };
            let poly = &ineq.factors[0].poly;
            // Parse linear: sum coeff_i * v_i + const.
            let mut coeffs: Vec<(Var, BigRational)> = Vec::new();
            let mut constant = BigRational::zero();
            let mut linear_ok = true;
            for term in poly.terms() {
                if term.monomial.is_unit() {
                    constant += &term.coeff;
                } else {
                    let vars: Vec<_> = term.monomial.vars().iter().collect();
                    if vars.len() == 1 && vars[0].power == 1 {
                        coeffs.push((vars[0].var, term.coeff.clone()));
                    } else {
                        linear_ok = false;
                        break;
                    }
                }
            }
            if !linear_ok || coeffs.is_empty() {
                continue;
            }

            if coeffs.len() == 1 {
                let (v, coeff) = &coeffs[0];
                if coeff.is_zero() {
                    continue;
                }
                let bound = -&constant / coeff;
                let (want_lower, strict) = match (ineq.kind, is_true, coeff.is_positive()) {
                    (AtomKind::Gt, true, true) => (true, true),
                    (AtomKind::Lt, false, true) => (true, false),
                    (AtomKind::Lt, true, false) => (true, true),
                    (AtomKind::Gt, false, false) => (true, false),
                    _ => continue,
                };
                if !want_lower {
                    continue;
                }
                let entry = lowers.entry(*v).or_insert((bound.clone(), strict, lit));
                if bound > entry.0 || (bound == entry.0 && strict && !entry.1) {
                    *entry = (bound, strict, lit);
                }
            } else if coeffs.iter().all(|(_, c)| *c == BigRational::one()) {
                // x + y + … OP -const  with unit coeffs.
                let vars: Vec<Var> = coeffs.iter().map(|(v, _)| *v).collect();
                let bound = -constant;
                let (is_upper, strict) = match (ineq.kind, is_true) {
                    (AtomKind::Lt, true) => (true, true),   // sum < bound
                    (AtomKind::Gt, false) => (true, false), // sum ≤ bound
                    _ => continue,
                };
                if is_upper {
                    sum_uppers.push((vars, bound, strict, lit));
                }
            }
        }

        for (vars, ub, ub_strict, ulit) in &sum_uppers {
            if vars.len() < 2 {
                continue;
            }
            let mut sum_lo = BigRational::zero();
            let mut any_strict = false;
            let mut lits: Vec<Literal> = vec![*ulit];
            let mut ok = true;
            for v in vars {
                let Some((b, s, l)) = lowers.get(v) else {
                    ok = false;
                    break;
                };
                sum_lo += b;
                any_strict |= *s;
                lits.push(*l);
            }
            if !ok {
                continue;
            }
            // sum > sum_lo (if any strict lower) or sum ≥ sum_lo otherwise.
            // Conflicts with sum < ub when sum_lo ≥ ub (strict lower or strict upper),
            // or sum_lo > ub.
            let unsat = if sum_lo > *ub {
                true
            } else if sum_lo == *ub {
                // equal bounds: conflict if either side is strict
                any_strict || *ub_strict
            } else {
                false
            };
            if unsat {
                let mut lemma: Vec<Literal> = lits.iter().map(|l| l.negate()).collect();
                lemma.sort_by_key(|l| l.index());
                lemma.dedup();
                if lemma.len() >= 2 {
                    return Some(lemma);
                }
            }
        }
        None
    }

    /// Certify unsat of `x·y = c` (or `x·y - c = 0`) together with strict or
    /// non-strict positive lower bounds on `x` and `y`.
    ///
    /// If `x > a ≥ 0`, `y > b ≥ 0` and `c ≤ a·b` (strict bounds), or
    /// `x ≥ a > 0`, `y ≥ b > 0` and `c < a·b`, then `x·y = c` is impossible
    /// over the reals. Returns a lemma negating the three participating atoms.
    /// Certify infeasibility of a two-variable *product* atom against sign-
    /// compatible variable bounds, and return the valid theory lemma.
    ///
    /// Covered patterns (all sound over ℝ):
    /// * `x ≥ a ≥ 0 ∧ y ≥ b ≥ 0 ⟹ x·y ≥ a·b` (strict variant when a bound is
    ///   strict and the other side's bound is nonzero);
    /// * the mirrored `x ≤ a ≤ 0 ∧ y ≤ b ≤ 0 ⟹ x·y ≥ a·b`;
    ///
    /// so an atom asserting `x·y < c` (or `≤`, `=`) with `c ≤ a·b` (with the
    /// matching strictness) is jointly infeasible with those bounds, and the
    /// clause `¬product ∨ ¬lower_x ∨ ¬lower_y` is a valid lemma. This is the
    /// classic VeryMax ITS monomial shape (`Nl2CT1 * lam0n7` products against
    /// `lam ≥ 0` bounds) that neither the sign fixpoint nor the pure
    /// single-variable regions can refute.
    pub(super) fn certify_product_bound_conflict(&self) -> Option<Vec<Literal>> {
        /// One currently-assigned bound literal: `v ≥/≤ bound` (strict flag).
        struct Bound {
            bound: BigRational,
            strict: bool,
            lit: Literal,
        }
        // Relation of the product atom, normalized to `x·y rel c` with the
        // coefficient's sign already folded into both.
        #[derive(Clone, Copy, PartialEq, Eq)]
        enum Rel {
            Lt,
            Le,
            Eq,
            /// `x·y ≥ c` – product bounded below; no conflict from below.
            Ge,
            /// `x·y > c` – product bounded strictly below; no conflict.
            Gt,
        }

        let mut lowers: FxHashMap<Var, Bound> = FxHashMap::default();
        let mut uppers: FxHashMap<Var, Bound> = FxHashMap::default();
        let mut products: Vec<(Var, Var, Rel, BigRational, Literal)> = Vec::new();

        for atom in &self.atoms {
            let Atom::Ineq(ineq) = atom else {
                continue;
            };
            if ineq.factors.len() != 1 {
                continue;
            }
            let val = self.assignment.bool_value(ineq.bool_var);
            if val.is_undef() {
                continue;
            }
            let is_true = val.is_true();
            let lit = if is_true {
                Literal::positive(ineq.bool_var)
            } else {
                Literal::negative(ineq.bool_var)
            };
            let Some((coeff, vars, constant)) = parse_monomial_plus_const(&ineq.factors[0].poly)
            else {
                continue;
            };
            if coeff.is_zero() {
                continue;
            }
            let pos = coeff.is_positive();

            // --- single-variable bound: coeff·v + k OP 0 ⇔ v OP −k/coeff ---
            if vars.len() == 1 && vars[0].1 == 1 {
                let v = vars[0].0;
                let bound = -&constant / &coeff;
                // (is_lower, strict) for `v` under (kind, is_true, pos-coeff).
                let rel: Option<(bool, bool)> = match (ineq.kind, is_true, pos) {
                    (AtomKind::Gt, true, true) => Some((true, true)), // v > b
                    (AtomKind::Lt, false, true) => Some((true, false)), // v ≥ b
                    (AtomKind::Lt, true, false) => Some((true, true)), // v > b
                    (AtomKind::Gt, false, false) => Some((true, false)), // v ≥ b
                    (AtomKind::Lt, true, true) => Some((false, true)), // v < b
                    (AtomKind::Gt, false, true) => Some((false, false)), // v ≤ b
                    (AtomKind::Gt, true, false) => Some((false, true)), // v < b
                    (AtomKind::Lt, false, false) => Some((false, false)), // v ≤ b
                    _ => None, // equalities / disequalities: no half-line
                };
                let Some((is_lower, strict)) = rel else {
                    continue;
                };
                let stronger = |new: &Bound, old: &Bound| -> bool {
                    // A stronger lower bound is larger; a stronger upper bound
                    // is smaller; strict beats non-strict at equality.
                    if is_lower {
                        new.bound > old.bound
                            || (new.bound == old.bound && new.strict && !old.strict)
                    } else {
                        new.bound < old.bound
                            || (new.bound == old.bound && new.strict && !old.strict)
                    }
                };
                let table = if is_lower { &mut lowers } else { &mut uppers };
                let entry = Bound {
                    bound: bound.clone(),
                    strict,
                    lit,
                };
                match table.get(&v) {
                    Some(old) if !stronger(&entry, old) => {}
                    _ => {
                        table.insert(v, entry);
                    }
                }
                continue;
            }

            // --- two-variable product: coeff·x·y + k OP 0 ⇔ x·y rel −k/coeff
            //     (the relation flips when the coefficient is negative) ---
            if vars.len() == 2 && vars[0].1 == 1 && vars[1].1 == 1 {
                let c = -&constant / &coeff;
                let rel = match (ineq.kind, is_true) {
                    (AtomKind::Lt, true) => Rel::Lt,  // p < 0
                    (AtomKind::Gt, false) => Rel::Le, // ¬(p>0) = p ≤ 0
                    (AtomKind::Gt, true) => Rel::Gt,  // p > 0
                    (AtomKind::Lt, false) => Rel::Ge, // ¬(p<0) = p ≥ 0
                    (AtomKind::Eq, true) => Rel::Eq,  // p = 0
                    _ => continue,                    // ¬(p=0): unbounded shape
                };
                // p = coeff·xy + k. With coeff > 0: p OP 0 ⇔ xy OP −k/coeff.
                // With coeff < 0 the relation direction flips.
                let rel = if pos {
                    rel
                } else {
                    match rel {
                        Rel::Lt => Rel::Gt,
                        Rel::Gt => Rel::Lt,
                        Rel::Le => Rel::Ge,
                        Rel::Ge => Rel::Le,
                        Rel::Eq => Rel::Eq,
                    }
                };
                if matches!(rel, Rel::Ge | Rel::Gt) {
                    continue; // product bounded *below*: no conflict against lower bounds
                }
                products.push((vars[0].0, vars[1].0, rel, c, lit));
            }
        }

        /// Derive the product's implied lower behaviour from two same-sign
        /// bounds: returns Some((ab, strict)) meaning `x·y ≥ ab` (strictly
        /// `>` when `strict`), or None when the sign combination carries no
        /// sound product bound (mixed signs, or a bound on the wrong side).
        fn product_lower(
            a: &BigRational,
            sx: bool,
            b: &BigRational,
            sy: bool,
        ) -> Option<(BigRational, bool)> {
            let ab = a * b;
            if a.is_zero() && b.is_zero() {
                // x ≥ 0 ∧ y ≥ 0 ⟹ xy ≥ 0; xy > 0 needs both strict.
                return Some((ab, sx && sy));
            }
            // Nonneg pair: x ≥ a ≥ 0, y ≥ b ≥ 0 ⟹ xy ≥ ab, strict when either
            // bound is strict (the other side's bound is nonzero).
            if !a.is_negative() && !b.is_negative() {
                let strict = (sx && !b.is_zero()) || (sy && !a.is_zero());
                return Some((ab, strict));
            }
            None
        }

        for (x, y, rel, c, prod_lit) in &products {
            // Same-side bound pairs only: (lower, lower, both ≥ 0) or
            // (upper, upper, both ≤ 0). The latter mirrors signs: x ≤ a ≤ 0,
            // y ≤ b ≤ 0 ⟹ xy ≥ ab.
            let implied = match (lowers.get(x), lowers.get(y)) {
                (Some(bx), Some(by)) if !bx.bound.is_negative() && !by.bound.is_negative() => {
                    product_lower(&bx.bound, bx.strict, &by.bound, by.strict)
                        .map(|(ab, s)| (ab, s, bx.lit, by.lit))
                }
                _ => match (uppers.get(x), uppers.get(y)) {
                    (Some(bx), Some(by)) if !bx.bound.is_positive() && !by.bound.is_positive() => {
                        // Mirror: bounds are v ≤ a ≤ 0; strictness on `≤` means
                        // v < a. |v| ≥ |a| gives xy ≥ ab (a·b ≥ 0).
                        let a = &bx.bound;
                        let b = &by.bound;
                        let ab = a * b;
                        if a.is_zero() && b.is_zero() {
                            Some((ab, bx.strict && by.strict))
                        } else {
                            let strict = (bx.strict && !b.is_zero()) || (by.strict && !a.is_zero());
                            Some((ab, strict))
                        }
                        .map(|(ab, s)| (ab, s, bx.lit, by.lit))
                    }
                    _ => None,
                },
            };
            let Some((ab, strict, lx, ly)) = implied else {
                continue;
            };
            // `xy ≥ ab` (or `>`) against `xy rel c`.
            let unsat = match rel {
                // xy ≥ ab (or >) versus xy < c / xy ≤ c / xy = c.
                Rel::Lt => ab >= *c || (strict && ab == *c),
                Rel::Le => ab > *c || (strict && ab >= *c),
                Rel::Eq => ab > *c || (strict && ab >= *c),
                // Ge/Gt are filtered before this point; arms for
                // exhaustiveness so a future variant cannot fall through
                // silently (unsound-default protection).
                Rel::Ge | Rel::Gt => false,
            };
            if unsat {
                let mut lemma = vec![prod_lit.negate(), lx.negate(), ly.negate()];
                lemma.sort_by_key(|l| l.index());
                lemma.dedup();
                if lemma.len() >= 2 {
                    return Some(lemma);
                }
            }
        }
        None
    }

    /// Attempt to certify that the currently-assigned polynomial atoms are
    /// jointly infeasible over the reals using a sound *sign abstraction*, and
    /// if so return a valid theory lemma (the disjunction of the negations of
    /// the participating atoms' current literals).
    ///
    /// This is the sound, model-based single-cell explanation recommended by
    /// the architecture audit for multivariate coupled conflicts: rather than
    /// the (unsound) "negate every atom sharing a variable" assembly retained
    /// in `explain.rs`, we abstract each assigned single-factor `monomial +
    /// constant` atom into a constraint on the *sign* of its variables, then
    /// run a monotone fixpoint that propagates forced signs across the coupling
    /// (product) atoms. If some variable is forced to have no consistent sign,
    /// the conjunction of the contributing atoms is genuinely unsatisfiable
    /// over R, so the clause negating their current literals is a valid lemma.
    ///
    /// Every step is a sound entailment (interval/sign reasoning is an
    /// over-approximation: a derived contradiction is a real one), so this
    /// never fabricates an UNSAT. When no contradiction can be derived it
    /// returns `None` (honest: the caller keeps searching or reports Unknown).
    ///
    /// It deliberately handles only the `single non-constant monomial +
    /// constant` atom shape with odd-power variable coupling (which covers the
    /// classic `x>1 ∧ x·y>1 ∧ y<0`-style conflicts); richer couplings that this
    /// abstraction cannot certify fall through to `None`.
    pub(super) fn certify_sign_conflict(&self) -> Option<Vec<Literal>> {
        // Abstracted view of one currently-assigned atom.
        struct SignAtom {
            /// The atom's current literal (negated into the lemma).
            lit: Literal,
            /// Sign of the (single) monomial's coefficient (never zero).
            coeff_sign: i8,
            /// Variable powers of the monomial.
            vars: Vec<(Var, u32)>,
            /// The set of signs the monomial value is constrained to.
            target: u8,
        }

        let mut sign_atoms: Vec<SignAtom> = Vec::new();
        for atom in &self.atoms {
            let Atom::Ineq(ineq) = atom else {
                continue;
            };
            if ineq.factors.len() != 1 {
                continue;
            }
            let val = self.assignment.bool_value(ineq.bool_var);
            if val.is_undef() {
                continue;
            }
            let is_true = val.is_true();
            let Some((coeff, vars, constant)) = parse_monomial_plus_const(&ineq.factors[0].poly)
            else {
                continue;
            };
            if vars.is_empty() {
                continue; // a bare constant constrains no variable's sign
            }
            // Atom is `monomial + constant OP 0`, i.e. `monomial OP -constant`.
            let threshold = -constant;
            let target = monomial_target_signset(ineq.kind, is_true, &threshold);
            if target == SIGN_FULL {
                continue; // no usable sign information
            }
            let lit = if is_true {
                Literal::positive(ineq.bool_var)
            } else {
                Literal::negative(ineq.bool_var)
            };
            sign_atoms.push(SignAtom {
                lit,
                coeff_sign: rational_sign(&coeff),
                vars,
                target,
            });
        }

        if sign_atoms.len() < 2 {
            return None;
        }

        // Same-monomial sign-set intersection: two assigned atoms over the
        // *same* monomial (up to the coefficient's sign, folded into the
        // target set) jointly constrain that monomial's sign; an empty
        // intersection is a direct contradiction.  This catches the
        // `p > 0 ∧ p ≤ 0` pattern on nonlinear products (e.g. `x·y > 0 ∧
        // ¬(−x·y < 0)`) that the per-variable fixpoint below cannot see,
        // because neither variable's sign is determined alone.
        {
            use std::collections::BTreeMap;
            // Normalized key: sorted variable powers with the coefficient's
            // sign removed; the sign itself flips the target set when negative.
            /// Accumulator for the same-monomial sign-set intersection:
            /// monomial key → (intersected sign set, contributing atom ids).
            type MonoSigns = BTreeMap<Vec<(Var, u32)>, (u8, Vec<usize>)>;
            let mut per_monomial: MonoSigns = BTreeMap::new();
            for (ai, sa) in sign_atoms.iter().enumerate() {
                let mut key = sa.vars.clone();
                key.sort_unstable();
                let target = if sa.coeff_sign < 0 {
                    // ¬ sign-flip: negating the monomial mirrors the sign set
                    // around zero.  SIGN_POS/SIGN_NEG swap; SIGN_POS|SIGN_NEG
                    // (both) stays; zero bits are unaffected by negation only
                    // for the zero itself – handled via the same bit mirror.
                    mirror_signset(sa.target)
                } else {
                    sa.target
                };
                let e = per_monomial.entry(key).or_insert((target, Vec::new()));
                e.0 &= target;
                e.1.push(ai);
            }
            for (_key, (set, atoms)) in per_monomial {
                if set == 0 {
                    let mut lemma: Vec<Literal> = Vec::new();
                    for &idx in &atoms {
                        let neg = sign_atoms[idx].lit.negate();
                        if !lemma.contains(&neg) {
                            lemma.push(neg);
                        }
                    }
                    if lemma.len() >= 2 {
                        return Some(lemma);
                    }
                }
            }
        }

        // Monotone fixpoint: each variable's sign-set starts full and only ever
        // shrinks (intersection), so this terminates.
        let mut signs: FxHashMap<Var, u8> = FxHashMap::default();
        let mut blame: FxHashMap<Var, FxHashSet<usize>> = FxHashMap::default();
        for sa in &sign_atoms {
            for (v, _) in &sa.vars {
                signs.entry(*v).or_insert(SIGN_FULL);
            }
        }

        let max_iter = (signs.len() + 1) * (sign_atoms.len() + 1) * 3 + 8;
        let mut changed = true;
        let mut guard = 0usize;
        while changed && guard < max_iter {
            changed = false;
            guard += 1;

            for (ai, sa) in sign_atoms.iter().enumerate() {
                // The monomial value's sign is forced strictly only when the
                // target is a nonzero singleton.
                let forced_m = match sa.target {
                    SIGN_POS => 1i8,
                    SIGN_NEG => -1i8,
                    _ => continue,
                };

                for &(v, p) in &sa.vars {
                    // Only odd powers transmit a sign to the variable.
                    if p.is_multiple_of(2) {
                        continue;
                    }

                    // Sign of the cofactor = coeff · ∏_{other vars} sign^power.
                    // Requires every other variable to have a strict singleton
                    // sign (an even power of a strict-signed var is positive).
                    let mut cof = sa.coeff_sign;
                    let mut provenance: FxHashSet<usize> = FxHashSet::default();
                    provenance.insert(ai);
                    let mut resolvable = true;
                    for &(u, up) in &sa.vars {
                        if u == v {
                            continue;
                        }
                        let us = *signs.get(&u).unwrap_or(&SIGN_FULL);
                        let usign = match signset_pow(us, up) {
                            SIGN_POS => 1i8,
                            SIGN_NEG => -1i8,
                            _ => {
                                resolvable = false;
                                break;
                            }
                        };
                        cof *= usign;
                        if let Some(b) = blame.get(&u) {
                            provenance.extend(b.iter().copied());
                        }
                    }
                    if !resolvable {
                        continue;
                    }

                    // forced_m = cof · sign(v)  ⇒  sign(v) = forced_m · cof.
                    let vbit = sign_to_bit(forced_m * cof);
                    let cur = signs.entry(v).or_insert(SIGN_FULL);
                    let refined = *cur & vbit;
                    if refined == *cur {
                        continue;
                    }
                    *cur = refined;
                    let bl = blame.entry(v).or_default();
                    bl.extend(provenance.iter().copied());
                    changed = true;

                    if refined == 0 {
                        // `v` has no consistent sign: the contributing atoms are
                        // jointly unsatisfiable over R.
                        let mut lemma: Vec<Literal> = Vec::new();
                        for &idx in bl.iter() {
                            let neg = sign_atoms[idx].lit.negate();
                            if !lemma.contains(&neg) {
                                lemma.push(neg);
                            }
                        }
                        if lemma.len() >= 2 {
                            return Some(lemma);
                        }
                    }
                }
            }
        }

        None
    }

    /// Accumulate feasible-region information for `var` across every assigned
    /// constraint that mentions it.
    pub(super) fn compute_arith_regions(&self, var: Var) -> ArithRegions {
        let mut inner = IntervalSet::reals();
        let mut outer = IntervalSet::reals();
        let mut blame = Vec::new();
        let mut blame_vars = Vec::new();
        let mut pure = true;
        let mut reliable = true;

        for atom in &self.atoms {
            match atom {
                Atom::Ineq(ineq) => {
                    let involves_var = ineq.factors.iter().any(|f| f.poly.vars().contains(&var));
                    if !involves_var {
                        continue;
                    }
                    let val = self.assignment.bool_value(ineq.bool_var);
                    if val.is_undef() {
                        continue;
                    }
                    let is_true = val.is_true();

                    match self.ineq_atom_region(ineq, var, is_true) {
                        None => continue, // does not constrain `var`
                        Some((a_inner, a_outer, a_reliable)) => {
                            inner = inner.intersect(&a_inner);
                            outer = outer.intersect(&a_outer);
                            reliable = reliable && a_reliable;

                            // "pure" iff the constraint mentions no variable
                            // other than `var` (so its infeasibility is not
                            // conditional on an earlier assignment).
                            let atom_pure = ineq
                                .factors
                                .iter()
                                .all(|f| f.poly.vars().iter().all(|v| *v == var));
                            pure = pure && atom_pure;

                            let lit = if is_true {
                                Literal::negative(ineq.bool_var)
                            } else {
                                Literal::positive(ineq.bool_var)
                            };
                            if !blame.contains(&lit) {
                                blame.push(lit);
                                for f in &ineq.factors {
                                    for bv in f.poly.vars() {
                                        if bv != var && !blame_vars.contains(&bv) {
                                            blame_vars.push(bv);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                Atom::Root(root) => {
                    let involves_var = root.var == var || root.poly.vars().contains(&var);
                    if !involves_var {
                        continue;
                    }
                    let val = self.assignment.bool_value(root.bool_var);
                    if val.is_undef() {
                        continue;
                    }
                    let is_true = val.is_true();
                    let constraint = self.atom_constraint_on_var(atom, var, is_true);
                    if constraint.is_reals() {
                        continue;
                    }
                    inner = inner.intersect(&constraint);
                    outer = outer.intersect(&constraint);
                    // Root-atom regions are approximate; never let them certify
                    // a global emptiness lemma.
                    reliable = false;

                    let root_pure = root.var == var && root.poly.vars().iter().all(|v| *v == var);
                    pure = pure && root_pure;

                    let lit = if is_true {
                        Literal::negative(root.bool_var)
                    } else {
                        Literal::positive(root.bool_var)
                    };
                    if !blame.contains(&lit) {
                        blame.push(lit);
                        for bv in root.poly.vars() {
                            if bv != var && !blame_vars.contains(&bv) {
                                blame_vars.push(bv);
                            }
                        }
                    }
                }
            }
        }

        ArithRegions {
            inner,
            outer,
            blame,
            blame_vars,
            pure,
            reliable,
        }
    }

    /// Compute `(inner, outer, reliable)` feasible regions for a single
    /// inequality atom on `var`, using exact Sturm root isolation so that
    /// irrational roots are never silently dropped.
    ///
    /// * `inner` – a subset of the true real feasible region containing only
    ///   rational points (safe to sample as a witness).
    /// * `outer` – a superset of the true real feasible region (empty only if
    ///   the true region is empty).
    /// * `reliable` – whether `outer`'s emptiness can be trusted (all roots
    ///   isolated into singleton-root brackets).
    ///
    /// Returns `None` when the atom places no constraint on `var` under the
    /// current partial assignment (e.g. another variable is still unassigned).
    fn ineq_atom_region(
        &self,
        ineq: &IneqAtom,
        var: Var,
        is_true: bool,
    ) -> Option<(IntervalSet, IntervalSet, bool)> {
        // Only single-factor atoms are handled precisely; multi-factor atoms
        // are treated as unconstraining (matches the historical behaviour).
        if ineq.factors.len() != 1 {
            return None;
        }
        let factor = &ineq.factors[0];

        // Substitute every assigned variable other than `var`.
        let mut sub_poly = factor.poly.clone();
        for v in factor.poly.vars() {
            if v != var {
                let val = self.assignment.arith_value(v)?;
                sub_poly = sub_poly.substitute(v, &Polynomial::constant(val.clone()));
            }
        }

        // Constant after substitution: the constraint is decided outright.
        if sub_poly.is_constant() {
            let value = sub_poly.eval(&FxHashMap::default());
            let sign = rational_sign(&value);
            let ok = sign_satisfies(ineq.kind, is_true, sign);
            return if ok {
                Some((IntervalSet::reals(), IntervalSet::reals(), true))
            } else {
                Some((IntervalSet::empty(), IntervalSet::empty(), true))
            };
        }

        // Must be univariate in `var` for the interval machinery.
        if !sub_poly.is_univariate() {
            return None;
        }
        // Guard: the remaining variable must actually be `var`.
        if sub_poly.degree(var) == 0 {
            return None;
        }

        Some(self.univariate_regions(&sub_poly, var, ineq.kind, is_true))
    }

    /// Build `(inner, outer, reliable)` interval sets for a univariate
    /// polynomial constraint using Sturm root isolation.
    fn univariate_regions(
        &self,
        poly: &Polynomial,
        var: Var,
        kind: AtomKind,
        is_true: bool,
    ) -> (IntervalSet, IntervalSet, bool) {
        // Exact rational roots (used for precise inner cell boundaries and for
        // rational equality witnesses).
        let rational_roots = self.find_univariate_roots(poly, var);

        // All distinct real roots (rational *and* irrational) via Sturm.
        let sturm = SturmSequence::new(poly, var);
        let num_distinct = sturm.count_roots() as usize;
        let mut iso = sturm.isolate_roots();
        iso.sort_by(|a, b| a.0.cmp(&b.0));

        let mut reliable = iso.len() == num_distinct;

        // Classify each isolating bracket, preferring exact rational roots.
        let mut reprs: Vec<RootRepr> = Vec::new();
        let mut used = vec![false; rational_roots.len()];
        for (lo, hi) in &iso {
            let mut in_bracket: Vec<(usize, BigRational)> = Vec::new();
            for (idx, r) in rational_roots.iter().enumerate() {
                if !used[idx] && r >= lo && r <= hi {
                    in_bracket.push((idx, r.clone()));
                }
            }
            match in_bracket.len() {
                0 => reprs.push(RootRepr {
                    lo: lo.clone(),
                    hi: hi.clone(),
                    exact: None,
                }),
                1 => {
                    let (idx, r) = in_bracket[0].clone();
                    used[idx] = true;
                    reprs.push(RootRepr {
                        lo: r.clone(),
                        hi: r.clone(),
                        exact: Some(r),
                    });
                }
                _ => {
                    // Multiple rational roots collapsed into one bracket: coarse.
                    reliable = false;
                    for (idx, r) in in_bracket {
                        used[idx] = true;
                        reprs.push(RootRepr {
                            lo: r.clone(),
                            hi: r.clone(),
                            exact: Some(r),
                        });
                    }
                }
            }
        }
        // Any rational root not covered by a bracket (defensive).
        for (idx, r) in rational_roots.iter().enumerate() {
            if !used[idx] {
                reprs.push(RootRepr {
                    lo: r.clone(),
                    hi: r.clone(),
                    exact: Some(r.clone()),
                });
            }
        }
        reprs.sort_by(|a, b| a.lo.cmp(&b.lo));

        let mut inner = IntervalSet::empty();
        let mut outer = IntervalSet::empty();

        // No roots: the polynomial has constant sign over the whole line.
        if reprs.is_empty() {
            let sign = self.eval_sign(poly, var, &BigRational::zero());
            if sign_satisfies(kind, is_true, sign) {
                return (IntervalSet::reals(), IntervalSet::reals(), true);
            }
            return (IntervalSet::empty(), IntervalSet::empty(), reliable);
        }

        let n = reprs.len();

        // Region left of the first root: (-∞, r_0).
        let left_sample = &reprs[0].lo - BigRational::one();
        if sign_satisfies(kind, is_true, self.eval_sign(poly, var, &left_sample)) {
            inner = inner.union(&IntervalSet::lt(reprs[0].lo.clone()));
            outer = outer.union(&IntervalSet::lt(reprs[0].hi.clone()));
        }

        // Regions strictly between consecutive roots.
        for i in 0..n - 1 {
            let a = &reprs[i];
            let b = &reprs[i + 1];
            if a.hi < b.lo {
                let mid = (&a.hi + &b.lo) / BigRational::from_integer(2.into());
                if sign_satisfies(kind, is_true, self.eval_sign(poly, var, &mid)) {
                    inner = inner.union(&IntervalSet::from_interval(Interval::open(
                        a.hi.clone(),
                        b.lo.clone(),
                    )));
                    outer = outer.union(&IntervalSet::from_interval(Interval::open(
                        a.lo.clone(),
                        b.hi.clone(),
                    )));
                }
            } else {
                // Brackets touch/overlap (e.g. two roots isolated by adjacent
                // intervals sharing an endpoint): we cannot sample the cell
                // between them to learn its sign. Conservatively assume it may
                // satisfy the target and fold it into the `outer` superset so
                // emptiness is never wrongly claimed; `inner` gains nothing.
                outer = outer.union(&IntervalSet::from_interval(Interval::open(
                    a.lo.clone(),
                    b.hi.clone(),
                )));
            }
        }

        // Region right of the last root: (r_{n-1}, +∞).
        let right_sample = &reprs[n - 1].hi + BigRational::one();
        if sign_satisfies(kind, is_true, self.eval_sign(poly, var, &right_sample)) {
            inner = inner.union(&IntervalSet::gt(reprs[n - 1].hi.clone()));
            outer = outer.union(&IntervalSet::gt(reprs[n - 1].lo.clone()));
        }

        // Roots themselves (sign 0) for equality-flavoured targets.
        if sign_satisfies(kind, is_true, 0) {
            for r in &reprs {
                if let Some(exact) = &r.exact {
                    inner = inner.union(&IntervalSet::point(exact.clone()));
                    outer = outer.union(&IntervalSet::point(exact.clone()));
                } else {
                    // Irrational root: no rational witness, but the outer
                    // region must cover it so emptiness is not wrongly claimed.
                    outer = outer.union(&IntervalSet::from_interval(Interval::closed(
                        r.lo.clone(),
                        r.hi.clone(),
                    )));
                }
            }
        }

        (inner, outer, reliable)
    }

    /// Get the constraint that an atom places on a variable.
    pub(super) fn atom_constraint_on_var(
        &self,
        atom: &Atom,
        var: Var,
        atom_is_true: bool,
    ) -> IntervalSet {
        match atom {
            Atom::Ineq(ineq) => {
                // For now, only handle single-factor atoms
                if ineq.factors.len() != 1 {
                    return IntervalSet::reals();
                }

                let factor = &ineq.factors[0];

                // Substitute all assigned variables except `var`
                let mut sub_poly = factor.poly.clone();
                for v in factor.poly.vars() {
                    if v != var
                        && let Some(val) = self.assignment.arith_value(v)
                    {
                        sub_poly = sub_poly.substitute(v, &Polynomial::constant(val.clone()));
                    }
                }

                // Now sub_poly should be univariate in `var`
                if !sub_poly.is_univariate() && !sub_poly.is_constant() {
                    // Can't simplify further
                    return IntervalSet::reals();
                }

                // Find roots
                let roots = self.find_univariate_roots(&sub_poly, var);

                // Determine signs between roots
                let signs = self.compute_signs_between_roots(&sub_poly, var, &roots);

                // Create interval set based on constraint kind and polarity
                let target_sign = match (ineq.kind, atom_is_true) {
                    (AtomKind::Eq, true) => 0,    // p = 0
                    (AtomKind::Eq, false) => 127, // p != 0 (special case)
                    (AtomKind::Lt, true) => -1,   // p < 0
                    (AtomKind::Lt, false) => 1,   // p >= 0 (includes 0)
                    (AtomKind::Gt, true) => 1,    // p > 0
                    (AtomKind::Gt, false) => -1,  // p <= 0 (includes 0)
                    _ => return IntervalSet::reals(),
                };

                if target_sign == 127 {
                    // p != 0: complement of {roots}
                    let zero_set = IntervalSet::sign_set(&roots, &signs, 0);
                    zero_set.complement()
                } else if target_sign == 1 && !atom_is_true {
                    // p >= 0: positive or zero
                    let pos_set = IntervalSet::sign_set(&roots, &signs, 1);
                    let zero_set = IntervalSet::sign_set(&roots, &signs, 0);
                    pos_set.union(&zero_set)
                } else if target_sign == -1 && !atom_is_true {
                    // p <= 0: negative or zero
                    let neg_set = IntervalSet::sign_set(&roots, &signs, -1);
                    let zero_set = IntervalSet::sign_set(&roots, &signs, 0);
                    neg_set.union(&zero_set)
                } else {
                    IntervalSet::sign_set(&roots, &signs, target_sign)
                }
            }
            Atom::Root(root) => {
                use crate::cad::SturmSequence;

                // For root atoms, we need to isolate the roots and determine the constraint
                // x op root[i](p) where op is =, <, >, <=, >=

                // First, check if this root atom actually involves the variable `var`
                if root.var != var && !root.poly.vars().contains(&var) {
                    return IntervalSet::reals();
                }

                // If the atom involves `var` in the polynomial (not as the root variable),
                // we cannot easily extract a constraint on `var` alone
                if root.var != var {
                    return IntervalSet::reals();
                }

                // Substitute all assigned variables (except var) into the polynomial
                let mut sub_poly = root.poly.clone();
                for v in root.poly.vars() {
                    if v != var {
                        if let Some(val) = self.assignment.arith_value(v) {
                            sub_poly = sub_poly.substitute(v, &Polynomial::constant(val.clone()));
                        } else {
                            return IntervalSet::reals();
                        }
                    }
                }

                // If the polynomial is constant, no roots exist
                if sub_poly.is_constant() {
                    return IntervalSet::empty();
                }

                // Isolate the roots
                let sturm = SturmSequence::new(&sub_poly, var);
                let root_intervals = sturm.isolate_roots();

                // Check if we have enough roots. `root_index` is only
                // guaranteed to exist for the polynomial's *generic*
                // structure; for this specific substitution of the other
                // variables, the i-th real root can fail to exist at all
                // (e.g. a pair of real roots became complex). When that
                // happens, the *positive* assertion `x op root[i](p)` can
                // never hold for any `x` (there is no such root to compare
                // against), so its feasible region is correctly empty --
                // but that also means the assertion's *negation* is
                // vacuously true for every `x`, so the negated atom's
                // feasible region must be the full real line, not empty
                // too. Returning `empty()` unconditionally here regardless
                // of `atom_is_true` would wrongly shrink the negated atom's
                // feasible set to nothing.
                if (root.root_index as usize) > root_intervals.len() || root.root_index == 0 {
                    return if atom_is_true {
                        IntervalSet::empty()
                    } else {
                        IntervalSet::reals()
                    };
                }

                // Get the i-th root interval
                let (root_lo, root_hi) = &root_intervals[(root.root_index - 1) as usize];

                // Create interval set based on the atom kind and polarity
                match (root.kind, atom_is_true) {
                    (AtomKind::RootEq, true) => {
                        // x = root[i](p)
                        IntervalSet::from_point(root_lo.clone())
                    }
                    (AtomKind::RootEq, false) => {
                        // x != root[i](p) - complement of the point
                        IntervalSet::from_point(root_lo.clone()).complement()
                    }
                    (AtomKind::RootLt, true) => {
                        // x < root[i](p) - approximately (-∞, root_hi)
                        IntervalSet::lt(root_hi.clone())
                    }
                    (AtomKind::RootLt, false) => {
                        // x >= root[i](p) - approximately [root_lo, +∞)
                        IntervalSet::ge(root_lo.clone())
                    }
                    (AtomKind::RootGt, true) => {
                        // x > root[i](p) - approximately (root_lo, +∞)
                        IntervalSet::gt(root_lo.clone())
                    }
                    (AtomKind::RootGt, false) => {
                        // x <= root[i](p) - approximately (-∞, root_hi]
                        IntervalSet::le(root_hi.clone())
                    }
                    (AtomKind::RootLe, true) => {
                        // x <= root[i](p)
                        IntervalSet::le(root_hi.clone())
                    }
                    (AtomKind::RootLe, false) => {
                        // x > root[i](p)
                        IntervalSet::gt(root_lo.clone())
                    }
                    (AtomKind::RootGe, true) => {
                        // x >= root[i](p)
                        IntervalSet::ge(root_lo.clone())
                    }
                    (AtomKind::RootGe, false) => {
                        // x < root[i](p)
                        IntervalSet::lt(root_hi.clone())
                    }
                    _ => IntervalSet::reals(),
                }
            }
        }
    }

    /// Find roots of a univariate polynomial.
    pub(super) fn find_univariate_roots(&self, poly: &Polynomial, var: Var) -> Vec<BigRational> {
        // For now, use a simple approach for low-degree polynomials
        let degree = poly.degree(var);

        if degree == 0 {
            return Vec::new();
        }

        if degree == 1 {
            // Linear: ax + b = 0  =>  x = -b/a
            return self.find_linear_root(poly);
        }

        if degree == 2 {
            // Quadratic: use quadratic formula (rational roots only)
            return self.find_quadratic_roots(poly);
        }

        // For higher degrees, find exact rational roots via the rational root theorem.
        // Any rational root p/q of a_n x^n + ... + a_0 satisfies p | a_0 and q | a_n.
        self.find_rational_roots(poly, var)
    }

    /// Find all exact rational roots of a polynomial using the rational root theorem.
    ///
    /// Converts rational coefficients to integers and tests all divisor combinations.
    pub(super) fn find_rational_roots(&self, poly: &Polynomial, var: Var) -> Vec<BigRational> {
        use num_bigint::BigInt;
        use num_traits::Zero;

        // Collect univariate coefficients: coeff[k] = coefficient of var^k
        let degree = poly.degree(var) as usize;
        if degree == 0 {
            return Vec::new();
        }

        // Gather rational coefficients for each power of var.
        // Only works for truly univariate polynomials.
        let mut rat_coeffs: Vec<BigRational> = (0..=degree)
            .map(|k| poly.univ_coeff(var, k as u32))
            .collect();

        // Clear leading zeros (shouldn't happen but be safe)
        while rat_coeffs.len() > 1 && rat_coeffs.last().is_some_and(|c| c.is_zero()) {
            rat_coeffs.pop();
        }
        let n = rat_coeffs.len();
        if n <= 1 {
            return Vec::new();
        }

        // Scale all coefficients by LCM of denominators to get integer coefficients.
        let lcm_denom: BigInt = rat_coeffs
            .iter()
            .fold(BigInt::from(1i64), |acc, r| lcm_bigint(&acc, r.denom()));

        let int_coeffs: Vec<BigInt> = rat_coeffs
            .iter()
            .map(|r| r.numer() * (&lcm_denom / r.denom()))
            .collect();

        let mut roots = Vec::new();

        // Peel off the factors of x. This used to rebuild the deflated
        // polynomial and recurse; the number of steps is the multiplicity
        // of the root at zero, i.e. the input-controlled degree, and the
        // `Vec` return type has no channel for a depth error.
        let mut coeffs: &[BigInt] = &int_coeffs;
        while coeffs.len() >= 2 && coeffs[0].is_zero() {
            roots.push(BigRational::zero());
            coeffs = &coeffs[1..];
        }

        let n = coeffs.len();
        if n < 2 {
            roots.sort();
            roots.dedup();
            return roots;
        }
        // The deflated polynomial is what the candidate test must run
        // against, exactly as the recursive form did.
        let poly = poly_from_int_coeffs(coeffs, var);
        let poly = &poly;

        let a0 = coeffs[0].clone(); // constant term
        let an = coeffs[n - 1].clone(); // leading coefficient

        // Divisors of the constant term and of the leading coefficient. If
        // either set could not be enumerated within the trial-division
        // budget, return only the roots established by deflation rather
        // than testing an incomplete candidate set – this list is already
        // "the rational roots we could establish" (a degree>=3 polynomial's
        // irrational roots are never in it either).
        let (Some(divisors_a0), Some(divisors_an)) =
            (integer_divisors(a0.abs()), integer_divisors(an.abs()))
        else {
            roots.sort();
            roots.dedup();
            return roots;
        };

        // Test all p/q where p | a0, q | an (both positive and negative)
        for p in &divisors_a0 {
            for q in &divisors_an {
                if q.is_zero() {
                    continue;
                }
                for &sign in &[1i64, -1i64] {
                    let candidate = BigRational::new(p * BigInt::from(sign), q.clone());
                    // Evaluate poly at candidate
                    let mut eval_map = rustc_hash::FxHashMap::default();
                    eval_map.insert(var, candidate.clone());
                    let val = poly.eval(&eval_map);
                    if val.is_zero() {
                        roots.push(candidate);
                    }
                }
            }
        }

        roots.sort();
        roots.dedup();
        roots
    }

    /// Find the root of a linear polynomial.
    pub(super) fn find_linear_root(&self, poly: &Polynomial) -> Vec<BigRational> {
        // p = ax + b, find x = -b/a
        let terms = poly.terms();
        if terms.len() > 2 {
            return Vec::new();
        }

        let mut a = BigRational::zero();
        let mut b = BigRational::zero();

        for term in terms {
            if term.monomial.is_unit() {
                b = term.coeff.clone();
            } else if term.monomial.total_degree() == 1 {
                a = term.coeff.clone();
            }
        }

        if a.is_zero() {
            return Vec::new();
        }

        vec![-b / a]
    }

    /// Find rational roots of a quadratic polynomial.
    pub(super) fn find_quadratic_roots(&self, poly: &Polynomial) -> Vec<BigRational> {
        // p = ax^2 + bx + c
        // Discriminant = b^2 - 4ac
        // If discriminant is a perfect square, roots are rational

        let terms = poly.terms();
        if terms.len() > 3 {
            return Vec::new();
        }

        let mut a = BigRational::zero();
        let mut b = BigRational::zero();
        let mut c = BigRational::zero();

        for term in terms {
            match term.monomial.total_degree() {
                0 => c = term.coeff.clone(),
                1 => b = term.coeff.clone(),
                2 => a = term.coeff.clone(),
                _ => return Vec::new(),
            }
        }

        if a.is_zero() {
            // Actually linear
            if b.is_zero() {
                return Vec::new();
            }
            return vec![-c.clone() / b.clone()];
        }

        // Discriminant
        let disc = &b * &b - BigRational::from_integer(4.into()) * &a * &c;

        if disc.is_negative() {
            return Vec::new();
        }

        if disc.is_zero() {
            let root = -b / (BigRational::from_integer(2.into()) * a);
            return vec![root];
        }

        // Check if discriminant is a perfect square
        // For rational discriminant p/q, we need both p and q to be perfect squares
        let numer = disc.numer().clone();
        let denom = disc.denom().clone();

        if let (Some(sqrt_n), Some(sqrt_d)) =
            (super::integer_sqrt(&numer), super::integer_sqrt(&denom))
        {
            let sqrt_disc = BigRational::new(sqrt_n, sqrt_d);
            let two_a = BigRational::from_integer(2.into()) * &a;
            let root1 = (-&b + &sqrt_disc) / &two_a;
            let root2 = (-&b - &sqrt_disc) / &two_a;

            let mut roots = vec![root1, root2];
            roots.sort();
            roots.dedup();
            roots
        } else {
            // Irrational roots - cannot represent exactly
            Vec::new()
        }
    }

    /// Compute signs of polynomial between roots.
    pub(super) fn compute_signs_between_roots(
        &self,
        poly: &Polynomial,
        var: Var,
        roots: &[BigRational],
    ) -> Vec<i8> {
        if roots.is_empty() {
            // No roots - evaluate at any point
            let test_val = BigRational::zero();
            let mut eval_map = FxHashMap::default();
            eval_map.insert(var, test_val);
            let val = poly.eval(&eval_map);
            let sign = if val.is_zero() {
                0
            } else if val.is_positive() {
                1
            } else {
                -1
            };
            return vec![sign];
        }

        let mut signs = Vec::with_capacity(roots.len() + 1);

        // Before first root
        let before = &roots[0] - BigRational::one();
        signs.push(self.eval_sign(poly, var, &before));

        // Between roots
        for i in 0..roots.len() - 1 {
            let mid = (&roots[i] + &roots[i + 1]) / BigRational::from_integer(2.into());
            signs.push(self.eval_sign(poly, var, &mid));
        }

        // After last root
        if let Some(last_root) = roots.last() {
            let after = last_root + BigRational::one();
            signs.push(self.eval_sign(poly, var, &after));
        }

        signs
    }

    /// Evaluate the sign of a polynomial at a point.
    pub(super) fn eval_sign(&self, poly: &Polynomial, var: Var, val: &BigRational) -> i8 {
        let mut eval_map = FxHashMap::default();
        eval_map.insert(var, val.clone());
        let result = poly.eval(&eval_map);
        if result.is_zero() {
            0
        } else if result.is_positive() {
            1
        } else {
            -1
        }
    }
}

/// A representative for one distinct real root of a univariate polynomial.
///
/// For a rational root `exact` is `Some(r)` and `lo == hi == r`. For an
/// irrational root `exact` is `None` and `[lo, hi]` is an isolating interval
/// that brackets exactly one root.
struct RootRepr {
    lo: BigRational,
    hi: BigRational,
    exact: Option<BigRational>,
}

/// Sign of a rational value as `-1`, `0`, or `1`.
fn rational_sign(value: &BigRational) -> i8 {
    if value.is_zero() {
        0
    } else if value.is_positive() {
        1
    } else {
        -1
    }
}

// ======== Sign-abstraction lattice for coupled-conflict certification ========
//
// A sign-set is a subset of {negative, zero, positive} encoded as a bitmask.
// This backs `NlsatSolver::certify_sign_conflict`; every operation is a sound
// over-approximation, so a derived empty set is a genuine infeasibility.

/// Bit for a strictly negative value.
const SIGN_NEG: u8 = 1;
/// Bit for a zero value.
const SIGN_ZERO: u8 = 2;
/// Bit for a strictly positive value.
const SIGN_POS: u8 = 4;
/// The full lattice top ({-, 0, +}).
const SIGN_FULL: u8 = SIGN_NEG | SIGN_ZERO | SIGN_POS;

/// Map a concrete sign (`-1`, `0`, `1`) to its singleton bit.
fn sign_to_bit(s: i8) -> u8 {
    match s.cmp(&0) {
        std::cmp::Ordering::Less => SIGN_NEG,
        std::cmp::Ordering::Equal => SIGN_ZERO,
        std::cmp::Ordering::Greater => SIGN_POS,
    }
}

/// Sign-set of `base^power` given the sign-set of `base`.
fn signset_pow(base: u8, power: u32) -> u8 {
    if power == 0 {
        return SIGN_POS; // x^0 = 1 > 0
    }
    if power.is_multiple_of(2) {
        // Even power: negatives and positives both map to positive; zero to zero.
        let mut out = 0;
        if base & (SIGN_NEG | SIGN_POS) != 0 {
            out |= SIGN_POS;
        }
        if base & SIGN_ZERO != 0 {
            out |= SIGN_ZERO;
        }
        out
    } else {
        base // odd power preserves sign
    }
}

/// Sign-set the monomial value is constrained to by the atom `kind`/polarity,
/// given the effective threshold `t = -constant` (the atom is `monomial + k OP
/// 0`, i.e. `monomial OP -k = t`). Returns [`SIGN_FULL`] when no strict sign is
/// entailed.
fn monomial_target_signset(kind: AtomKind, is_true: bool, threshold: &BigRational) -> u8 {
    let ts = rational_sign(threshold);
    // Effective comparison of the monomial value `m` against `t`.
    #[derive(Clone, Copy)]
    enum Rel {
        Gt,
        Ge,
        Lt,
        Le,
        Eq,
        Ne,
    }
    let rel = match (kind, is_true) {
        (AtomKind::Gt, true) => Rel::Gt,
        (AtomKind::Gt, false) => Rel::Le,
        (AtomKind::Lt, true) => Rel::Lt,
        (AtomKind::Lt, false) => Rel::Ge,
        (AtomKind::Eq, true) => Rel::Eq,
        (AtomKind::Eq, false) => Rel::Ne,
        _ => return SIGN_FULL, // root kinds handled elsewhere
    };
    match rel {
        // m > t: if t ≥ 0 then m > 0.
        Rel::Gt => match ts {
            0 | 1 => SIGN_POS,
            _ => SIGN_FULL,
        },
        // m ≥ t: t > 0 ⇒ m > 0; t = 0 ⇒ m ≥ 0.
        Rel::Ge => match ts {
            1 => SIGN_POS,
            0 => SIGN_POS | SIGN_ZERO,
            _ => SIGN_FULL,
        },
        // m < t: if t ≤ 0 then m < 0.
        Rel::Lt => match ts {
            0 | -1 => SIGN_NEG,
            _ => SIGN_FULL,
        },
        // m ≤ t: t < 0 ⇒ m < 0; t = 0 ⇒ m ≤ 0.
        Rel::Le => match ts {
            -1 => SIGN_NEG,
            0 => SIGN_NEG | SIGN_ZERO,
            _ => SIGN_FULL,
        },
        // m = t: sign(m) = sign(t).
        Rel::Eq => match ts {
            1 => SIGN_POS,
            0 => SIGN_ZERO,
            _ => SIGN_NEG,
        },
        // m ≠ t: only informative when t = 0 (m ≠ 0).
        Rel::Ne => match ts {
            0 => SIGN_NEG | SIGN_POS,
            _ => SIGN_FULL,
        },
    }
}

/// Parsed shape of a `coeff·(single monomial) + constant` polynomial:
/// `(leading coefficient, variable powers of the monomial, constant term)`.
/// Mirror a sign-set bit pattern through negation: positive ↔ negative,
/// zero stays zero.  Used to normalize a monomial's coefficient sign into
/// its target sign-set (backing `certify_sign_conflict`).
fn mirror_signset(set: u8) -> u8 {
    // Layout convention (see SIGN_* constants): bit0 = negative, bit1 = zero,
    // bit2 = positive.  Negation swaps the negative and positive bits.
    (set & 0b010) | ((set & 0b100) >> 2) | ((set & 0b001) << 2)
}

type MonomialPlusConst = (BigRational, Vec<(Var, u32)>, BigRational);

/// Parse a polynomial of the shape `coeff·(single non-constant monomial) +
/// constant` into `(coeff, variable powers, constant)`. Returns `None` for any
/// polynomial that is not exactly one non-constant monomial plus an optional
/// constant term.
fn parse_monomial_plus_const(poly: &Polynomial) -> Option<MonomialPlusConst> {
    let mut constant = BigRational::zero();
    let mut monomial: Option<(BigRational, Vec<(Var, u32)>)> = None;
    for term in poly.terms() {
        if term.monomial.is_unit() {
            constant += &term.coeff;
        } else {
            if monomial.is_some() {
                return None; // more than one non-constant monomial
            }
            let vars: Vec<(Var, u32)> = term
                .monomial
                .vars()
                .iter()
                .map(|vp| (vp.var, vp.power))
                .collect();
            monomial = Some((term.coeff.clone(), vars));
        }
    }
    let (coeff, vars) = monomial?;
    Some((coeff, vars, constant))
}

/// Whether a polynomial of the given `sign` at a point satisfies the atom
/// `kind` under the given polarity.
///
/// `sign` is `-1`, `0`, or `1` for `p < 0`, `p = 0`, `p > 0` respectively.
fn sign_satisfies(kind: AtomKind, is_true: bool, sign: i8) -> bool {
    let holds = match kind {
        AtomKind::Eq => sign == 0,
        AtomKind::Lt => sign < 0,
        AtomKind::Gt => sign > 0,
        // Root kinds are handled elsewhere; treat as unconstrained.
        _ => return true,
    };
    if is_true { holds } else { !holds }
}

// ======== Helpers for rational root theorem ========

/// Euclidean GCD for non-negative BigInts.
fn gcd_bigint(mut a: num_bigint::BigInt, mut b: num_bigint::BigInt) -> num_bigint::BigInt {
    use num_traits::Zero;
    while !b.is_zero() {
        let t = &a % &b;
        a = b;
        b = t;
    }
    a.abs()
}

/// Compute the least common multiple of two BigInts.
fn lcm_bigint(a: &num_bigint::BigInt, b: &num_bigint::BigInt) -> num_bigint::BigInt {
    use num_traits::Zero;
    if a.is_zero() || b.is_zero() {
        return num_bigint::BigInt::from(1i64);
    }
    let g = gcd_bigint(a.abs(), b.abs());
    (a * b).abs() / g
}

/// Trial-division budget for divisor enumeration.
///
/// `n` is a polynomial coefficient straight from `.smt2` input, so its
/// magnitude is attacker-chosen and `sqrt(n)` bignum modulos is unbounded
/// work – a 40-digit prime coefficient would hang the solver forever. This
/// budget enumerates every `n` below 10¹⁰ exactly and reports failure
/// instead of hanging above that.
const TRIAL_DIVISION_BUDGET: u64 = 100_000;

/// Return all positive divisors of a positive BigInt.
///
/// `None` means the trial-division budget was exhausted, so the divisor set
/// is not complete. Callers must not use a partial list: the rational-root
/// theorem only rules candidates in or out when both divisor sets are
/// complete.
fn integer_divisors(n: num_bigint::BigInt) -> Option<Vec<num_bigint::BigInt>> {
    use num_traits::{One, Zero};
    if n.is_zero() {
        return Some(vec![num_bigint::BigInt::one()]);
    }
    let mut divisors = Vec::new();
    let mut i = num_bigint::BigInt::one();
    let mut steps = 0u64;
    loop {
        if &i * &i > n {
            break;
        }
        if steps >= TRIAL_DIVISION_BUDGET {
            return None;
        }
        steps += 1;
        let r = &n % &i;
        let q = &n / &i;
        if r.is_zero() {
            divisors.push(i.clone());
            if q != i {
                divisors.push(q);
            }
        }
        i += num_bigint::BigInt::one();
    }
    Some(divisors)
}

/// Build a univariate Polynomial from a Vec of BigInt coefficients (index = power of var).
fn poly_from_int_coeffs(
    coeffs: &[num_bigint::BigInt],
    var: oxiz_math::polynomial::Var,
) -> oxiz_math::polynomial::Polynomial {
    use num_traits::Zero;
    use oxiz_math::polynomial::{Monomial, MonomialOrder, Polynomial, Term};

    let terms: Vec<Term> = coeffs
        .iter()
        .enumerate()
        .filter(|(_, c)| !c.is_zero())
        .map(|(k, c)| {
            let coeff = BigRational::new(c.clone(), num_bigint::BigInt::from(1i64));
            let monomial = if k == 0 {
                Monomial::unit()
            } else {
                Monomial::from_var_power(var, k as u32)
            };
            Term::new(coeff, monomial)
        })
        .collect();
    Polynomial::from_terms(terms, MonomialOrder::default())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::RootAtom;

    // Regression test for the item: when a root atom's index references a
    // root that doesn't exist for the current substitution (here, `x^2 + 1`
    // has zero real roots at all, so root index 1 never exists), the
    // *positive* assertion `x = root[1](x^2+1)` can never hold for any x
    // (correctly empty), but its negation `x != root[1](x^2+1)` is
    // vacuously true for every x -- the feasible region must be the full
    // real line, not empty too.
    #[test]
    fn test_root_atom_missing_root_negated_yields_full_set_not_empty() {
        let solver = NlsatSolver::new();
        let x: Var = 0;

        // x^2 + 1: no real roots.
        let x_poly = Polynomial::from_var(x);
        let poly = Polynomial::add(
            &Polynomial::mul(&x_poly, &x_poly),
            &Polynomial::constant(BigRational::one()),
        );

        let root_atom = RootAtom::new(AtomKind::RootEq, x, 1, poly);
        let atom = Atom::Root(root_atom);

        // Positive polarity: no such root exists, so nothing can satisfy
        // `x = root[1](p)` -- correctly empty.
        let positive_region = solver.atom_constraint_on_var(&atom, x, true);
        assert!(
            positive_region.is_empty(),
            "positive root-atom assertion referencing a nonexistent root \
             must be infeasible"
        );

        // Negated polarity: the (unsatisfiable) positive assertion's
        // negation is vacuously true everywhere.
        let negated_region = solver.atom_constraint_on_var(&atom, x, false);
        assert!(
            negated_region.is_reals(),
            "negated root-atom assertion referencing a nonexistent root must \
             be the full real line, not empty: {negated_region:?}"
        );
    }

    // Same scenario but for an inequality root-atom kind (RootLt), to cover
    // more than just the RootEq branch's point/complement pairing.
    #[test]
    fn test_root_atom_missing_root_negated_yields_full_set_not_empty_for_inequality() {
        let solver = NlsatSolver::new();
        let x: Var = 0;

        let x_poly = Polynomial::from_var(x);
        let poly = Polynomial::add(
            &Polynomial::mul(&x_poly, &x_poly),
            &Polynomial::constant(BigRational::one()),
        );

        let root_atom = RootAtom::new(AtomKind::RootLt, x, 1, poly);
        let atom = Atom::Root(root_atom);

        let positive_region = solver.atom_constraint_on_var(&atom, x, true);
        assert!(positive_region.is_empty());

        let negated_region = solver.atom_constraint_on_var(&atom, x, false);
        assert!(
            negated_region.is_reals(),
            "negated inequality root-atom assertion referencing a nonexistent \
             root must be the full real line, not empty: {negated_region:?}"
        );
    }
}
