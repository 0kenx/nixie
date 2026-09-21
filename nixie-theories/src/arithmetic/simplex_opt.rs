//! Optimization extension for the Simplex solver.
//!
//! Provides `optimize_linexpr` for minimizing a linear expression over the
//! current feasible region using the primal simplex method with Bland's rule.

use super::delta::DeltaRational;
use super::simplex::{
    LinExpr, Simplex, SnapBound, VarId, checked_add_r64, checked_div_r64, checked_mul_r64,
    checked_sub_r64,
};
use num_rational::Rational64;
use num_traits::Zero;

/// Checked `(a - b) / eff` ratio computation (the ratio test's gap):
/// `None` when the difference or the division does not fit `Rational64` —
/// the caller must abandon the optimization rather than wrap (a wrapped
/// ratio walks the search off the feasible region and can report a
/// bogus "optimum", which narrows `lp_int_bounds`'s case-split range —
/// the false-`unsat` direction).  `neg` flips the divisor's sign first
/// (`gap / -eff`), also checked.
fn ratio_gap(a: Rational64, b: Rational64, eff: &Rational64, neg: bool) -> Option<Rational64> {
    let gap = checked_sub_r64(a, b)?;
    let divisor = if neg { checked_neg(*eff)? } else { *eff };
    if gap >= Rational64::zero() {
        checked_div_r64(gap, divisor)
    } else {
        Some(Rational64::zero())
    }
}

fn one_r() -> Rational64 {
    use num_traits::One as _;
    Rational64::one()
}

fn checked_neg(r: Rational64) -> Option<Rational64> {
    let n = (*r.numer() as i128).checked_neg()?;
    if !(i64::MIN as i128..=i64::MAX as i128).contains(&n) {
        return None;
    }
    Some(Rational64::new_raw(n as i64, *r.denom()))
}

/// Status of a simplex optimization call.
#[derive(Debug, Clone, PartialEq)]
pub enum SimplexOptStatus {
    /// Optimal value found.
    Optimal(Rational64),
    /// Objective is unbounded (can be improved without limit).
    Unbounded,
    /// The constraint set is infeasible.
    Infeasible,
    /// Could not determine (e.g., pivot limit hit).
    Unknown,
}

impl Simplex {
    /// Evaluate a linear expression at the current assignment, CHECKED:
    /// a wrapped objective value would masquerade as an optimum (the
    /// `lp_int_bounds` case-split range narrows → a permanent clause that
    /// excludes reachable values → a false `unsat`), so the honest answer
    /// for an unrepresentable sum is `None`.
    pub(super) fn eval_linexpr(&self, obj: &LinExpr) -> Option<Rational64> {
        let mut val = obj.constant;
        for (var, coef) in &obj.terms {
            let idx = *var as usize;
            if idx < self.assignment_len() {
                let term = checked_mul_r64(self.assignment_at(idx), *coef)?;
                val = checked_add_r64(val, term)?;
            }
        }
        Some(val)
    }

    /// Compute the reduced objective coefficient for a non-basic variable.
    ///
    /// After substituting all basic variables, the objective becomes:
    ///
    ///   obj_val = constant + Σ over non-basic v of (reduced_coef(v) · v)
    ///
    /// where:
    ///
    ///   reduced_coef(v) = obj_coef(v)
    ///                   + Σ over basic b of (obj_coef(b) · tableau_coef(b, v))
    /// CHECKED like [`Self::eval_linexpr`]: a wrapped reduced cost chooses
    /// phantom entering variables and mis-terminates the search.
    pub(super) fn reduced_obj_coef(
        &self,
        obj: &LinExpr,
        nonbasic_var: VarId,
    ) -> Option<Rational64> {
        // Direct coefficient of this variable in obj.
        let direct = obj
            .terms
            .iter()
            .find(|(v, _)| *v == nonbasic_var)
            .map(|(_, c)| *c)
            .unwrap_or_else(Rational64::zero);

        // Indirect contribution via basic variables.
        let mut indirect = Rational64::zero();
        for (basic_var, row) in self.tableau_iter() {
            let obj_coef = obj
                .terms
                .iter()
                .find(|(v, _)| *v == basic_var)
                .map(|(_, c)| *c)
                .unwrap_or_else(Rational64::zero);
            if obj_coef.is_zero() {
                continue;
            }
            let row_coef = row
                .terms
                .iter()
                .find(|(v, _)| *v == nonbasic_var)
                .map(|(_, c)| *c)
                .unwrap_or_else(Rational64::zero);
            indirect = checked_add_r64(indirect, checked_mul_r64(obj_coef, row_coef)?)?;
        }

        checked_add_r64(direct, indirect)
    }

    /// Minimize a linear expression over the current feasible region.
    ///
    /// The solver must already be in a feasible state (after `check()`) before
    /// calling this method.
    ///
    /// Returns:
    /// - [`SimplexOptStatus::Optimal`]`(v)` – minimum value `v` was found.
    /// - [`SimplexOptStatus::Unbounded`] – objective can decrease without bound.
    /// - [`SimplexOptStatus::Infeasible`] – the constraint set is infeasible.
    /// - [`SimplexOptStatus::Unknown`] – pivot limit hit; result undetermined.
    ///
    /// Uses Bland's rule throughout to prevent cycling.
    pub fn optimize_linexpr(&mut self, obj: &LinExpr) -> SimplexOptStatus {
        // Phase 0: verify feasibility and find a primal feasible point.
        if self.check().is_err() {
            return SimplexOptStatus::Infeasible;
        }

        // Phase 1: primal simplex to minimise obj over the feasible region.
        //
        // Reduced cost of non-basic x_j:
        //   c̄_j = c_j + Σ_{b ∈ basic} c_b · a_{b,j}
        // where a_{b,j} is the coefficient of x_j in row b.
        //
        // If c̄_j < 0 and x_j can increase → entering (increasing reduces obj).
        // If c̄_j > 0 and x_j can decrease → entering (decreasing reduces obj).
        //
        // Bland's rule: among all improving variables, choose the one with the
        // smallest VarId index (prevents cycling).

        let mut result = SimplexOptStatus::Unknown;

        'outer: for _ in 0..self.max_pivots() {
            self.update_assignment();
            // The re-derivation may itself hit the honest width limit
            // (`resource_limit`): the vector is then stale, and every
            // downstream read would be a guess.
            if self.resource_limit_reached() {
                return SimplexOptStatus::Unknown;
            }

            let num_vars = self.assignment_len();

            // Find entering variable (Bland's rule: ascending VarId scan).
            let mut enter_var: Option<VarId> = None;
            let mut enter_decrease: bool = false;

            for v_id in 0..num_vars as VarId {
                let v_idx = v_id as usize;
                if self.is_basic(v_idx) {
                    continue;
                }

                let Some(rc) = self.reduced_obj_coef(obj, v_id) else {
                    // An unrepresentable reduced cost cannot be reasoned
                    // over: abandon with Unknown (the honest decline).
                    return SimplexOptStatus::Unknown;
                };
                let can_inc = self.can_increase(v_id);
                let can_dec = self.can_decrease(v_id);

                let is_entering =
                    (rc < Rational64::zero() && can_inc) || (rc > Rational64::zero() && can_dec);

                if is_entering {
                    enter_var = Some(v_id);
                    enter_decrease = rc > Rational64::zero();
                    break;
                }
            }

            let (enter, decrease_it) = match enter_var {
                None => {
                    // An objective value that cannot be represented is not
                    // an optimum: report Unknown, never a wrapped value.
                    result = match self.eval_linexpr(obj) {
                        Some(v) => SimplexOptStatus::Optimal(v),
                        None => SimplexOptStatus::Unknown,
                    };
                    break 'outer;
                }
                Some(v) => (v, enter_decrease),
            };

            // Ratio test: find the leaving variable (and the bound it is
            // driven to — the pivot's snap target).
            let mut leaving: Option<VarId> = None;
            let mut leaving_snap = SnapBound::LowerPreferred;
            let mut best_ratio: Option<Rational64> = None;

            let basic_vars: Vec<VarId> = self.tableau_keys().collect();

            for basic_var in &basic_vars {
                let a = match self.tableau_coef_of(*basic_var, enter) {
                    Some(c) => c,
                    None => continue,
                };

                let bv_idx = *basic_var as usize;
                let bv_val = self.assignment_real_at(bv_idx);
                let eff = if decrease_it { -a } else { a };

                let ratio = if eff > Rational64::zero() {
                    self.upper_real_at(bv_idx)
                        .map(|hi| ratio_gap(hi, bv_val, &eff, false))
                } else if eff < Rational64::zero() {
                    self.lower_real_at(bv_idx)
                        .map(|lo| ratio_gap(bv_val, lo, &eff, true))
                } else {
                    continue;
                };
                // A ratio that cannot be represented abandons the search:
                // a wrapped ratio picks a wrong leaving variable and walks
                // the search off the feasible region.
                if matches!(ratio, Some(None)) {
                    return SimplexOptStatus::Unknown;
                }
                let ratio = ratio.flatten();

                if let Some(r) = ratio {
                    let is_better = match best_ratio {
                        None => true,
                        Some(best) => {
                            r < best || (r == best && *basic_var < leaving.unwrap_or(VarId::MAX))
                        }
                    };
                    if is_better {
                        best_ratio = Some(r);
                        leaving = Some(*basic_var);
                        // The bound this basic is driven to by the entering
                        // column's move (the pivot's snap target): `eff > 0`
                        // rises into the upper gap, `eff < 0` falls to the
                        // lower.
                        leaving_snap = if eff > Rational64::zero() {
                            SnapBound::Upper
                        } else {
                            SnapBound::Lower
                        };
                    }
                }
            }

            // Check enter's own bound.
            let enter_idx = enter as usize;
            let enter_val = self.assignment_real_at(enter_idx);
            let enter_own_limit = if decrease_it {
                self.lower_real_at(enter_idx)
                    .map(|lo| ratio_gap(enter_val, lo, &one_r(), false))
            } else {
                self.upper_real_at(enter_idx)
                    .map(|hi| ratio_gap(hi, enter_val, &one_r(), false))
            };
            if matches!(enter_own_limit, Some(None)) {
                return SimplexOptStatus::Unknown;
            }
            let enter_own_limit = enter_own_limit.flatten();

            if let Some(limit) = enter_own_limit {
                let is_better = match best_ratio {
                    None => true,
                    Some(best) => limit < best,
                };
                if is_better {
                    best_ratio = Some(limit);
                    leaving = None;
                }
            }

            match leaving {
                None if best_ratio.is_some() => {
                    // Enter variable hits its own bound; no pivot needed.
                    let new_val = if decrease_it {
                        self.lower_delta_at(enter_idx)
                            .unwrap_or_else(DeltaRational::zero)
                    } else {
                        self.upper_delta_at(enter_idx)
                            .unwrap_or_else(DeltaRational::zero)
                    };
                    self.set_assignment_at(enter_idx, new_val);
                    self.update_assignment();
                    if self.resource_limit_reached() {
                        return SimplexOptStatus::Unknown;
                    }
                }
                None => {
                    result = SimplexOptStatus::Unbounded;
                    break 'outer;
                }
                Some(lv) => {
                    // A declined pivot (width, resource limit) leaves the
                    // state un-advanced: continuing would reason over a
                    // stale assignment.  Abandon honestly.  The snap stays
                    // the historical lower-preferred rule (the optimizer's
                    // trajectories are calibrated to it, like the SOI
                    // driver's; only the DdM repair loops snap to the
                    // violated bound).
                    let _ = leaving_snap;
                    if !self.pivot(lv, enter, SnapBound::LowerPreferred) {
                        result = SimplexOptStatus::Unknown;
                        break 'outer;
                    }
                }
            }
        }

        // If the loop exhausted the pivot budget without proving optimality or
        // unboundedness, `result` is still `Unknown`. We MUST NOT relabel that
        // truncated search as `Optimal`: the current assignment is feasible but
        // possibly far from optimal, and callers rely on `Unknown` meaning "the
        // search was cut off". Only the no-entering-variable branch (which sets
        // `Optimal` inside the loop) may report optimality.
        if matches!(result, SimplexOptStatus::Unknown) {
            self.update_assignment();
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::SimplexConfig;
    use num_traits::One;

    #[test]
    fn test_pivot_limit_reports_unknown_not_optimal() {
        // Regression (audit theories-p3): when the pivot budget is exhausted the
        // optimizer must NOT relabel the truncated search as Optimal. With
        // max_pivots = 0 the optimization loop body never runs, so optimality
        // cannot be proven and the honest result is Unknown.
        let config = SimplexConfig {
            max_pivots: 0,
            ..SimplexConfig::default()
        };
        let mut simplex = Simplex::with_config(config);

        let x = simplex.new_var();
        // 0 <= x <= 5, feasible immediately (no pivots needed to be feasible).
        simplex.set_lower(x, Rational64::zero(), 0);
        simplex.set_upper(x, Rational64::from_integer(5), 1);

        // Objective: minimize x.
        let mut obj = LinExpr::new();
        obj.add_term(x, Rational64::one());

        let status = simplex.optimize_linexpr(&obj);
        assert_eq!(
            status,
            SimplexOptStatus::Unknown,
            "pivot budget of 0 must yield Unknown, never a fabricated Optimal"
        );
    }

    #[test]
    fn test_optimal_reported_when_budget_sufficient() {
        // With an adequate pivot budget the same problem is solved to optimality.
        let mut simplex = Simplex::new();
        let x = simplex.new_var();
        simplex.set_lower(x, Rational64::zero(), 0);
        simplex.set_upper(x, Rational64::from_integer(5), 1);

        let mut obj = LinExpr::new();
        obj.add_term(x, Rational64::one());

        let status = simplex.optimize_linexpr(&obj);
        // Minimum of x over [0, 5] is 0.
        assert_eq!(status, SimplexOptStatus::Optimal(Rational64::zero()));
    }
}
