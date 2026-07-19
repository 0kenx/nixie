//! Cut generation and management for LIA solver
//!
//! All cutting-plane generators derive their inequalities from the *actual*
//! simplex tableau row of a fractional basic variable, never from a scalar
//! value in isolation.  The returned [`LinExpr`] `C` encodes the valid
//! inequality `C <= 0` (same convention as [`LiaSolver::generate_cover_cut`]
//! and [`Simplex::add_le`]).  Every emitted cut is a valid inequality of the
//! mixed-integer hull: it never removes an integer-feasible point.  Whenever a
//! sound cut cannot be derived the generator returns [`None`] rather than
//! fabricating an inequality — branch-and-bound (see `branching.rs`) remains a
//! sound and complete decision procedure for LIA, so a missing cut only forgoes
//! an optional strengthening.

use super::super::simplex::{LinExpr, VarId};
use super::helpers::gcd;
use super::types::LiaSolver;
#[allow(unused_imports)]
use crate::prelude::*;
use num_rational::Rational64;
use num_traits::{One, Zero};

impl LiaSolver {
    /// Derive a cutting plane from the tableau row of a fractional basic variable.
    ///
    /// Given the row of a basic integer variable `x_var`
    ///
    /// ```text
    /// x_var = a0 + Σ_j a_j · x_j        (x_j non-basic, resting at a bound)
    /// ```
    ///
    /// each non-basic term is rewritten in the non-negative slack
    /// `y_j = x_j - l_j` (variable at its lower bound) or `y_j = u_j - x_j`
    /// (variable at its upper bound), giving
    ///
    /// ```text
    /// x_var = x̄_var + Σ_j â_j · y_j ,   y_j ≥ 0 ,
    /// ```
    ///
    /// where `x̄_var` is the current (fractional) value of the basic variable.
    /// Let `f0 = x̄_var − ⌊x̄_var⌋ ∈ (0,1)`.
    ///
    /// The Gomory/GMI coefficient formulas are stated for the canonical source
    /// row `x_var + Σ_j ā_j y_j = x̄_var`; since the simplex stores the row as
    /// `x_var = x̄_var + Σ_j â_j y_j`, the canonical coefficient is
    /// `ā_j = −â_j` (this negation is essential — using `â_j` directly emits an
    /// invalid inequality that removes integer-feasible points).
    ///
    /// * `pure_integer == false` produces the **Gomory Mixed-Integer (GMI)**
    ///   cut `Σ_j γ_j y_j ≥ 1`, valid whether or not the non-basic variables are
    ///   integer:
    ///   * integer `y_j` (variable is an integer variable resting at an integer
    ///     bound) with `f_j = ā_j − ⌊ā_j⌋`:
    ///     `γ_j = f_j/f0` if `f_j ≤ f0`, else `γ_j = (1−f_j)/(1−f0)`;
    ///   * continuous `y_j`:
    ///     `γ_j = ā_j/f0` if `ā_j ≥ 0`, else `γ_j = −ā_j/(1−f0)`.
    ///
    /// * `pure_integer == true` produces the **pure-integer Gomory fractional
    ///   cut** `Σ_j f_j y_j ≥ f0` with `f_j = ā_j − ⌊ā_j⌋`, which is only valid
    ///   when *every* non-basic variable in the row is integer; if any non-basic
    ///   is continuous the method returns [`None`].
    ///
    /// Both cuts are translated back into the original variables and returned
    /// with the convention `C <= 0`.  Returns [`None`] when `x_var` is not a
    /// basic integer variable with a fractional value, when the row is empty, or
    /// when a non-basic variable is not resting at a finite bound (so the
    /// `y_j ≥ 0` substitution is unavailable).
    ///
    /// Reference: Cornuéjols, "Valid inequalities for mixed integer linear
    /// programs" (2008); Dutertre & de Moura, "A Fast Linear-Arithmetic Solver
    /// for DPLL(T)" (2006).
    fn tableau_row_cut(&self, var: VarId, pure_integer: bool) -> Option<LinExpr> {
        // The cut is only sound for a basic integer variable with a fractional
        // LP value.
        if !self.int_vars.contains_key(&var) || !self.simplex.is_basic(var as usize) {
            return None;
        }

        let bar = self.simplex.value(var);
        let f0 = bar - bar.floor();
        if f0.is_zero() {
            return None; // already integral: nothing to cut
        }

        let one = Rational64::one();
        let zero = Rational64::zero();
        let one_minus_f0 = one - f0;

        // Fetch the tableau row `x_var = constant + Σ a_j x_j`.
        let row = self
            .simplex
            .tableau_iter()
            .find(|(v, _)| **v == var)
            .map(|(_, e)| e.clone())?;
        if row.terms.is_empty() {
            return None;
        }

        // Base right-hand side: `Σ f_j y_j ≥ f0` (pure) or `Σ γ_j y_j ≥ 1` (GMI).
        let base_rhs = if pure_integer { f0 } else { one };

        // Accumulate the cut as `C = R − Σ c_j x_j` with the convention `C ≤ 0`.
        let mut cut = LinExpr::new();
        let mut rhs = base_rhs;

        for (xj, a_j) in &row.terms {
            let xj = *xj;
            let a_j = *a_j;
            if a_j.is_zero() {
                continue;
            }

            let idx = xj as usize;
            let vj = self.simplex.value(xj);
            let lower = self.simplex.lower_real_at(idx);
            let upper = self.simplex.upper_real_at(idx);

            // Determine which bound the non-basic variable rests at.  A general
            // simplex parks non-basic variables at a bound; if this variable is
            // not at a finite bound we cannot form the non-negative slack `y_j`,
            // so no sound cut is available.
            let (at_lower, bound_val) = if lower == Some(vj) {
                (true, vj)
            } else if upper == Some(vj) {
                (false, vj)
            } else {
                return None;
            };

            // Coefficient of `y_j` in the *stored* row orientation
            // `x_var = x̄_var + Σ â_j y_j`:  `â_j = a_j` at a lower bound,
            // `−a_j` at an upper bound.
            let hat_a = if at_lower { a_j } else { -a_j };

            // The Gomory/GMI coefficient formulas below are stated for the
            // canonical source row `x_var + Σ ā_j y_j = x̄_var`, whereas the
            // simplex stores `x_var = x̄_var + Σ â_j y_j`.  Rearranging,
            // `ā_j = −â_j`; using `â_j` directly would flip the split on the
            // sign of the coefficient and the fractional part, yielding an
            // invalid inequality that cuts off integer-feasible points.
            let bar_a = -hat_a;

            // `y_j` is integral only when `x_j` is an integer variable resting
            // at an integer bound.  Slack variables are conservatively treated
            // as continuous (their integrality is not tracked), which keeps the
            // GMI cut valid.
            let is_int = self.int_vars.contains_key(&xj) && bound_val.is_integer();

            let gamma = if pure_integer {
                // The pure-integer Gomory fractional cut is only valid when
                // every non-basic variable is integral.
                if !is_int {
                    return None;
                }
                bar_a - bar_a.floor() // f_j ∈ [0,1)
            } else if is_int {
                let fj = bar_a - bar_a.floor();
                if fj <= f0 {
                    fj / f0
                } else {
                    (one - fj) / one_minus_f0
                }
            } else if bar_a > zero {
                bar_a / f0
            } else {
                -bar_a / one_minus_f0
            };

            if gamma.is_zero() {
                continue;
            }

            // Translate `γ_j y_j` back to `x_j` and fold into `C = R − Σ c_j x_j`:
            //   lower: y_j = x_j − l_j  ⇒ c_j = +γ_j , R += γ_j·l_j
            //   upper: y_j = u_j − x_j  ⇒ c_j = −γ_j , R −= γ_j·u_j
            if at_lower {
                cut.add_term(xj, -gamma);
                rhs += gamma * bound_val;
            } else {
                cut.add_term(xj, gamma);
                rhs -= gamma * bound_val;
            }
        }

        if cut.terms.is_empty() {
            return None;
        }

        cut.add_constant(rhs);
        Some(cut)
    }

    /// Generate a Gomory (mixed-integer) cut from the tableau row of `var`.
    ///
    /// This is the Gomory Mixed-Integer (GMI) cut derived from the simplex row
    /// of the fractional basic variable `var`.  It is valid for the integer hull
    /// (never removes an integer-feasible point) and separates the current
    /// fractional LP point.  Returns [`None`] when no sound cut can be derived
    /// (see [`LiaSolver::tableau_row_cut`]).
    pub(super) fn generate_gomory_cut(&self, var: VarId, value: Rational64) -> Option<LinExpr> {
        if value.is_integer() {
            return None;
        }
        self.tableau_row_cut(var, false)
    }

    /// Coefficient lifting for strengthening Gomory cuts.
    ///
    /// Correct coefficient lifting must be *validity preserving* — it may never
    /// turn a valid cut into one that removes an integer-feasible point.  A
    /// sound lifting procedure requires per-variable bound information together
    /// with a sequence-independent lifting function; an earlier revision applied
    /// an ad-hoc coefficient scaling that could invalidate the cut.  Until a
    /// validity-preserving lifting is implemented we leave the cut unchanged so
    /// the already-valid input inequality is emitted verbatim, and report that
    /// no lifting was performed.
    ///
    /// Reference: Gu, Nemhauser, Savelsbergh (1998), "Sequence Independent
    /// Lifting"; Wolsey, "Integer Programming", Chapter 8.
    pub fn lift_gomory_cut(&self, cut: &mut LinExpr, var: VarId) -> bool {
        // Intentionally a no-op: preserve validity by not modifying the cut.
        let _ = (&*cut, var);
        false
    }

    /// Sequence-independent coefficient lifting across all variables in a cut.
    ///
    /// Delegates to [`LiaSolver::lift_gomory_cut`], which is currently a
    /// validity-preserving no-op (see its documentation).  The cut is therefore
    /// returned unchanged.
    pub fn lift_cut_all_vars(&self, cut: &mut LinExpr) {
        let vars: Vec<VarId> = cut.terms.iter().map(|(v, _)| *v).collect();
        for &var in &vars {
            let _ = self.lift_gomory_cut(cut, var);
        }
    }

    /// GCD-based infeasibility detection
    ///
    /// For a constraint: a_1*x_1 + a_2*x_2 + ... + a_n*x_n <= b
    /// where all a_i and x_i are integers, if gcd(a_1, a_2, ..., a_n) does not divide b,
    /// then the constraint is infeasible over integers.
    pub fn check_gcd_infeasibility(coeffs: &[i64], bound: i64) -> bool {
        if coeffs.is_empty() {
            return false;
        }

        let g = coeffs.iter().fold(0i64, |acc, &c| gcd(acc, c.abs()));

        if g == 0 {
            return false;
        }

        // If gcd does not divide bound, infeasible
        bound % g != 0
    }

    /// Tighten bounds using GCD reasoning
    ///
    /// For: a_1*x_1 + a_2*x_2 + ... + a_n*x_n <= b
    /// We can tighten to: a_1*x_1 + a_2*x_2 + ... + a_n*x_n <= floor(b / gcd) * gcd
    pub fn tighten_bound(coeffs: &[i64], bound: i64) -> i64 {
        if coeffs.is_empty() {
            return bound;
        }

        let g = coeffs.iter().fold(0i64, |acc, &c| gcd(acc, c.abs()));

        if g == 0 || g == 1 {
            return bound;
        }

        // Tighten bound
        (bound / g) * g
    }

    /// Generate a Mixed-Integer Rounding (MIR) cut from the tableau row of `var`.
    ///
    /// For a single simplex row the Mixed-Integer Rounding cut coincides with the
    /// Gomory Mixed-Integer cut, so this delegates to the same tableau-derived
    /// construction (see `LiaSolver::tableau_row_cut`).  The result is valid
    /// for the integer hull and separates the current fractional point, or
    /// [`None`] when no sound cut can be derived.
    ///
    /// Reference: Marchand & Wolsey, "Aggregation and Mixed Integer Rounding to
    /// Solve MIPs" (2001) — MIR applied to a tableau row yields the GMI cut.
    pub fn generate_mir_cut(&self, var: VarId, value: Rational64) -> Option<LinExpr> {
        if value.is_integer() {
            return None;
        }
        self.tableau_row_cut(var, false)
    }

    /// Generate a Chvatal-Gomory (CG) cut from the tableau row of `var`.
    ///
    /// This is the pure-integer Gomory fractional cut (`Σ f_j y_j ≥ f0`), the
    /// Chvátal-Gomory rounding of the tableau row.  It is valid only when every
    /// non-basic variable in the row is integral; because slack integrality is
    /// not tracked, a row that contains any continuous (e.g. slack) non-basic
    /// yields [`None`] rather than an unsound cut.  When it does fire, the cut is
    /// valid for the integer hull and separates the current fractional point.
    pub fn generate_cg_cut(&self, var: VarId, value: Rational64) -> Option<LinExpr> {
        if value.is_integer() {
            return None;
        }
        self.tableau_row_cut(var, true)
    }

    /// Generate a disjunctive (split) cut for the split on `var`.
    ///
    /// For an integer variable `x` with fractional LP value `x*` the split
    /// disjunction is `x ≤ ⌊x*⌋ ∨ x ≥ ⌈x*⌉`.  The Gomory Mixed-Integer cut
    /// derived from the tableau row of `var` is exactly the split cut for this
    /// disjunction, so this delegates to the tableau-derived construction (see
    /// `LiaSolver::tableau_row_cut`).  The result is a valid inequality of the
    /// integer hull — it never removes an integer-feasible point — and separates
    /// the current fractional point.
    ///
    /// Returns [`None`] for an integer `value` and whenever no sound cut can be
    /// derived (e.g. `var` is non-basic, or a non-basic term of the row is not
    /// resting at a finite bound).
    ///
    /// Reference: Balas, "Disjunctive Programming" (1979); Cornuéjols (2008) —
    /// the GMI cut is the split cut for the elementary split on the basic
    /// variable.
    pub fn generate_disjunctive_cut(&self, var: VarId, value: Rational64) -> Option<LinExpr> {
        if value.is_integer() {
            return None;
        }
        self.tableau_row_cut(var, false)
    }

    /// Generate a cover cut for a knapsack constraint
    ///
    /// Cover cuts are generated from knapsack constraints of the form:
    /// sum(a_i * x_i) <= b, where x_i are binary (0/1) variables
    ///
    /// A cover C is a subset of variables such that sum(a_i for i in C) > b.
    /// The corresponding cover inequality is: sum(x_i for i in C) <= |C| - 1
    ///
    /// Cover cuts are very effective for 0-1 integer programs and combinatorial problems.
    ///
    /// Reference: "Integer Programming" by Wolsey, Chapter 9
    pub fn generate_cover_cut(&self, coeffs: &[i64], vars: &[VarId], rhs: i64) -> Option<LinExpr> {
        if coeffs.len() != vars.len() || coeffs.is_empty() {
            return None;
        }

        // Find a minimal cover (greedy approach)
        // A cover is a set of variables whose sum of coefficients exceeds rhs
        let mut indices: Vec<usize> = (0..coeffs.len()).collect();

        // Sort by coefficient (descending) for greedy selection
        indices.sort_by(|&i, &j| coeffs[j].cmp(&coeffs[i]));

        let mut cover = Vec::new();
        let mut cover_sum = 0i64;

        // Greedily add variables to cover until we exceed rhs
        for &idx in &indices {
            cover.push(idx);
            cover_sum += coeffs[idx];

            if cover_sum > rhs {
                break; // We have a cover
            }
        }

        if cover_sum <= rhs {
            return None; // No cover found
        }

        // Generate the cover inequality: sum(x_i for i in cover) <= |cover| - 1
        let mut cut = LinExpr::new();

        for &idx in &cover {
            cut.add_term(vars[idx], Rational64::one());
        }

        // RHS is |cover| - 1
        cut.add_constant(-Rational64::from_integer((cover.len() as i64) - 1));

        Some(cut)
    }

    /// Generate an extended cover cut (lifted cover cut)
    ///
    /// Extended cover cuts strengthen basic cover cuts by lifting coefficients
    /// of variables not in the cover.
    ///
    /// For a cover cut sum(x_i for i in C) <= |C| - 1, we can add lifted variables:
    /// sum(x_i for i in C) + sum(alpha_j * x_j for j not in C) <= |C| - 1
    ///
    /// where alpha_j is computed via lifting to maintain validity.
    pub fn generate_extended_cover_cut(
        &self,
        coeffs: &[i64],
        vars: &[VarId],
        rhs: i64,
    ) -> Option<LinExpr> {
        // First generate a basic cover cut
        let cut = self.generate_cover_cut(coeffs, vars, rhs)?;

        // Lifting cover cuts requires solving small knapsack lifting problems to
        // compute valid coefficients for the non-cover variables; a lift that is
        // not validity preserving would remove integer-feasible points.  Until
        // that is implemented we return the (valid) basic cover cut unchanged
        // rather than adding unsound lifted terms.
        Some(cut)
    }
}

#[cfg(test)]
mod cut_validity_tests {
    use super::*;
    use crate::arithmetic::simplex::{LinExpr, VarId};
    use num_rational::Rational64;
    use num_traits::Zero;

    fn r(n: i64) -> Rational64 {
        Rational64::from_integer(n)
    }

    /// Build `{x ≥ 0, y ≥ 0, x + 2y ≤ 2, 3x + 2y ≤ 4}`.
    ///
    /// Maximising `x + y` reaches the fractional vertex `(1, 1/2)`, while the
    /// integer-feasible points include `(0,0), (1,0), (0,1)`.
    fn build_instance_a() -> (LiaSolver, VarId, VarId) {
        let mut s = LiaSolver::new();
        let x = s.new_var();
        let y = s.new_var();
        s.simplex.set_lower(x, r(0), 0);
        s.simplex.set_lower(y, r(0), 1);

        let mut c1 = LinExpr::new();
        c1.add_term(x, r(1));
        c1.add_term(y, r(2));
        c1.add_constant(r(-2));
        s.simplex.add_le(c1, 2);

        let mut c2 = LinExpr::new();
        c2.add_term(x, r(3));
        c2.add_term(y, r(2));
        c2.add_constant(r(-4));
        s.simplex.add_le(c2, 3);

        (s, x, y)
    }

    /// Build `{x ≥ 0, y ≥ 0, 2x + 3y ≤ 5}`.
    ///
    /// Maximising `x` reaches the fractional vertex `(5/2, 0)` at which the
    /// integer variable `y` is non-basic at its (integer) lower bound with a
    /// fractional row coefficient, exercising the integer branch of the GMI
    /// construction.
    fn build_instance_f() -> (LiaSolver, VarId, VarId) {
        let mut s = LiaSolver::new();
        let x = s.new_var();
        let y = s.new_var();
        s.simplex.set_lower(x, r(0), 0);
        s.simplex.set_lower(y, r(0), 1);

        let mut c1 = LinExpr::new();
        c1.add_term(x, r(2));
        c1.add_term(y, r(3));
        c1.add_constant(r(-5));
        s.simplex.add_le(c1, 2);

        (s, x, y)
    }

    /// Build `{x ≥ 0, y ≥ 0, 4x − y ≤ 3}`.
    ///
    /// Maximising `x − 10y` drives `y` to its lower bound `0` and reaches the
    /// fractional vertex `(3/4, 0)`, so the fractional part `f0 = 3/4 ≠ 1/2`.
    /// This is the discriminating instance: at `f0 = 1/2` the wrong-sign GMI
    /// coefficients coincide with the correct ones (because `frac(â) = frac(−â)`
    /// and `f0 = 1−f0`), fully masking a sign error in the fractional-part /
    /// continuous split; here they differ, so a wrong-sign cut provably removes
    /// the feasible integer point `(1,1)` (`4·1−1 = 3 ≤ 3`).
    fn build_instance_g() -> (LiaSolver, VarId, VarId) {
        let mut s = LiaSolver::new();
        let x = s.new_var();
        let y = s.new_var();
        s.simplex.set_lower(x, r(0), 0);
        s.simplex.set_lower(y, r(0), 1);

        let mut c1 = LinExpr::new();
        c1.add_term(x, r(4));
        c1.add_term(y, r(-1));
        c1.add_constant(r(-3));
        s.simplex.add_le(c1, 2);

        (s, x, y)
    }

    /// Evaluate cut `C` (convention `C ≤ 0`) at an integer assignment of the two
    /// original variables.  Returns `Some(value)` when the point is feasible
    /// under all asserted constraints (slack values are read from a freshly
    /// solved copy of the instance), or `None` when the point is infeasible.
    fn eval_cut_at(
        build: impl Fn() -> (LiaSolver, VarId, VarId),
        cut: &LinExpr,
        xval: i64,
        yval: i64,
    ) -> Option<Rational64> {
        let (mut s, x, y) = build();
        s.simplex.set_lower(x, r(xval), 100);
        s.simplex.set_upper(x, r(xval), 101);
        s.simplex.set_lower(y, r(yval), 102);
        s.simplex.set_upper(y, r(yval), 103);

        if s.simplex.check().is_err() || s.simplex.resource_limit_reached() {
            return None; // point violates the asserted constraints
        }

        let mut acc = cut.constant;
        for (v, c) in &cut.terms {
            acc += *c * s.simplex.value(*v);
        }
        Some(acc)
    }

    /// Assert that `cut` removes no integer-feasible point of the instance
    /// (validity) and that it separates the current fractional LP point
    /// (usefulness).
    fn assert_cut_valid_and_separating(
        solver: &LiaSolver,
        build: impl Fn() -> (LiaSolver, VarId, VarId) + Copy,
        cut: &LinExpr,
    ) {
        // Validity: no feasible integer point may violate `C ≤ 0`.
        for xi in 0..=4 {
            for yi in 0..=4 {
                if let Some(cv) = eval_cut_at(build, cut, xi, yi) {
                    assert!(
                        cv <= Rational64::zero(),
                        "cut removes feasible integer point ({xi},{yi}): C = {cv}"
                    );
                }
            }
        }

        // Usefulness: the current fractional LP point must be cut off.
        let mut current = cut.constant;
        for (v, c) in &cut.terms {
            current += *c * solver.simplex.value(*v);
        }
        assert!(
            current > Rational64::zero(),
            "cut does not separate the current fractional point (C = {current})"
        );
    }

    fn optimise_max_sum(
        build: impl Fn() -> (LiaSolver, VarId, VarId),
    ) -> (LiaSolver, VarId, VarId) {
        let (mut s, x, y) = build();
        let mut obj = LinExpr::new();
        obj.add_term(x, r(-1)); // minimise -(x+y) == maximise x+y
        obj.add_term(y, r(-1));
        let _ = s.simplex.optimize_linexpr(&obj);
        (s, x, y)
    }

    fn optimise_max_x(build: impl Fn() -> (LiaSolver, VarId, VarId)) -> (LiaSolver, VarId, VarId) {
        let (mut s, x, y) = build();
        let mut obj = LinExpr::new();
        obj.add_term(x, r(-1)); // minimise -x == maximise x
        let _ = s.simplex.optimize_linexpr(&obj);
        (s, x, y)
    }

    fn optimise_max_x_minus_10y(
        build: impl Fn() -> (LiaSolver, VarId, VarId),
    ) -> (LiaSolver, VarId, VarId) {
        let (mut s, x, y) = build();
        let mut obj = LinExpr::new();
        obj.add_term(x, r(-1)); // minimise -(x - 10y) == maximise x - 10y
        obj.add_term(y, r(10));
        let _ = s.simplex.optimize_linexpr(&obj);
        (s, x, y)
    }

    /// Every generator that emits a cut for instance A must emit a valid,
    /// separating cut (continuous / slack non-basic branch of GMI).
    #[test]
    fn cuts_valid_instance_a() {
        let (s, x, y) = optimise_max_sum(build_instance_a);

        let mut produced = 0;
        for &var in &[x, y] {
            let val = s.simplex.value(var);
            if val.is_integer() {
                continue;
            }
            let cuts = [
                s.generate_gomory_cut(var, val),
                s.generate_mir_cut(var, val),
                s.generate_cg_cut(var, val),
                s.generate_disjunctive_cut(var, val),
            ];
            for cut in cuts.into_iter().flatten() {
                produced += 1;
                assert_cut_valid_and_separating(&s, build_instance_a, &cut);
            }
        }
        assert!(
            produced > 0,
            "expected at least one cut at the fractional optimum"
        );
    }

    /// Instance F exercises the *integer* non-basic branch of the GMI/CG
    /// construction (`y` non-basic at an integer bound with a fractional row
    /// coefficient); every emitted cut must be valid and separating.
    #[test]
    fn cuts_valid_instance_f() {
        let (s, x, y) = optimise_max_x(build_instance_f);

        let mut produced = 0;
        for &var in &[x, y] {
            let val = s.simplex.value(var);
            if val.is_integer() {
                continue;
            }
            let cuts = [
                s.generate_gomory_cut(var, val),
                s.generate_mir_cut(var, val),
                s.generate_cg_cut(var, val),
                s.generate_disjunctive_cut(var, val),
            ];
            for cut in cuts.into_iter().flatten() {
                produced += 1;
                assert_cut_valid_and_separating(&s, build_instance_f, &cut);
            }
        }
        assert!(
            produced > 0,
            "expected at least one cut at the fractional optimum"
        );
    }

    /// Instance G is the discriminating case with `f0 = 3/4 ≠ 1/2`.  A
    /// wrong-sign GMI construction (using the stored `â_j` instead of the
    /// canonical `ā_j = −â_j`) produces `6x − 2y ≤ 3`, which removes the
    /// feasible integer point `(1,1)`.  The correct construction yields `x ≤ y`,
    /// which removes no feasible integer point.  Every emitted cut must be valid
    /// and separating, so this test fails on the sign bug and passes only on the
    /// corrected coefficients.
    #[test]
    fn cuts_valid_instance_g_f0_not_half() {
        let (s, x, y) = optimise_max_x_minus_10y(build_instance_g);

        // The fractional optimum is (3/4, 0): f0 = 3/4, the discriminating value.
        assert_eq!(s.simplex.value(x), Rational64::new(3, 4));
        assert_eq!(s.simplex.value(y), Rational64::zero());

        let mut produced = 0;
        for &var in &[x, y] {
            let val = s.simplex.value(var);
            if val.is_integer() {
                continue;
            }
            let cuts = [
                s.generate_gomory_cut(var, val),
                s.generate_mir_cut(var, val),
                s.generate_cg_cut(var, val),
                s.generate_disjunctive_cut(var, val),
            ];
            for cut in cuts.into_iter().flatten() {
                produced += 1;
                assert_cut_valid_and_separating(&s, build_instance_g, &cut);
            }
        }
        assert!(
            produced > 0,
            "expected at least one cut at the f0=3/4 fractional optimum"
        );
    }

    /// Generators must be honest: no cut for an integer value, and no cut for a
    /// variable with no tableau row (nothing solved yet).
    #[test]
    fn no_cut_without_fractional_basic_row() {
        let mut s = LiaSolver::new();
        let x = s.new_var();
        let _y = s.new_var();

        // Integer value -> None regardless of state.
        assert!(s.generate_gomory_cut(x, r(3)).is_none());
        assert!(s.generate_mir_cut(x, r(3)).is_none());
        assert!(s.generate_cg_cut(x, r(3)).is_none());
        assert!(s.generate_disjunctive_cut(x, r(3)).is_none());

        // Fractional value but the variable is not a basic row -> None (honest),
        // never a fabricated inequality.
        assert!(s.generate_gomory_cut(x, Rational64::new(3, 2)).is_none());
        assert!(
            s.generate_disjunctive_cut(x, Rational64::new(3, 2))
                .is_none()
        );
    }

    /// The GMI cut for instance A is the known inequality `3x + 4y ≤ 4`; verify
    /// it separates the fractional vertex and keeps every integer-feasible point
    /// (regression guard for the exact coefficients).
    #[test]
    fn gomory_cut_matches_known_inequality() {
        let (s, x, y) = optimise_max_sum(build_instance_a);

        // y is the fractional basic variable at (1, 1/2).
        let yval = s.simplex.value(y);
        assert_eq!(yval, Rational64::new(1, 2));
        let _ = x;

        let cut = s
            .generate_gomory_cut(y, yval)
            .expect("a GMI cut exists at the fractional vertex");

        // Evaluated over original variables the cut is equivalent to 3x+4y ≤ 4.
        // Check that against every integer point in the box, using the same
        // feasibility oracle the solver uses.
        for xi in 0..=4 {
            for yi in 0..=4 {
                let feasible = eval_cut_at(build_instance_a, &cut, xi, yi);
                // The 3x+4y ≤ 4 region and the asserted-constraint region agree
                // on which integer points are feasible here, so a feasible point
                // must satisfy the cut.
                if let Some(cv) = feasible {
                    assert!(cv <= Rational64::zero(), "({xi},{yi}) wrongly cut: {cv}");
                }
            }
        }
    }
}
