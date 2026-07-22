//! Loos–Weispfenning virtual term substitution for linear real-arithmetic QE.
//!
//! Eliminates an existential quantifier `∃x. φ(x)` over linear real arithmetic
//! using the "elimination from below" test set. As `x` increases from `-∞`,
//! the truth value of `φ` only changes at the boundary values of its atoms; a
//! satisfying interval is therefore either unbounded below or has a lower
//! endpoint that coincides with (or lies infinitesimally above) some boundary.
//! Hence
//!
//! ```text
//! ∃x. φ(x)  ≡  φ[-∞]  ∨  ⋁_{s ∈ P} φ[s]  ∨  ⋁_{s ∈ E} φ[s + ε]
//! ```
//!
//! where `P` collects the boundaries of non-strict lower bounds and equalities
//! (`x ≥ s`, `x = s`), and `E` collects the boundaries of strict lower bounds
//! and disequalities (`x > s`, `x ≠ s`). The infinitesimal shift `s + ε` is
//! substituted virtually: `ε` is eliminated symbolically through the atom
//! rewriting rules in `super::lra`, so the output is an ordinary
//! quantifier-free formula. All arithmetic is exact rational arithmetic.
//!
//! Because every disjunct is a concrete witness (a real value, the limit at
//! `-∞`, or an open interval just above a boundary), the elimination set may be
//! freely over-approximated without affecting soundness; the candidate set
//! below is generated for both polarities of every atom, which keeps the
//! construction complete without threading boolean polarity through the parser.
//!
//! Integer-sorted variables are rejected with an explicit `Err`: over the
//! integers the infinitesimal `+ε` shift is replaced by `+1` (Cooper's method),
//! which this eliminator does not implement.
//!
//! Reference: Loos & Weispfenning, *Applying linear quantifier elimination*
//! (Comput. J. 1993); Z3's `qe_arith.cpp`.

use super::lra;
use crate::ast::{TermId, TermManager};
use crate::prelude::FxHashMap;
#[allow(unused_imports)]
use crate::prelude::*;
use num_traits::Signed;

/// Virtual term substitution QE engine.
pub struct VirtualTermEliminator {
    /// Statistics
    stats: VirtualTermStats,
}

/// Virtual term elimination statistics.
#[derive(Debug, Clone, Default)]
pub struct VirtualTermStats {
    /// Number of quantifiers eliminated
    pub quantifiers_eliminated: usize,
    /// Number of virtual terms generated
    pub virtual_terms_generated: usize,
    /// Number of test points evaluated
    pub test_points_evaluated: usize,
}

/// Classify an atom `x_coeff·x + rest REL 0` by the lower-bound test points it
/// contributes to the "from below" elimination set. Both polarities of the
/// atom are considered (over-approximating soundly), so the returned flags
/// indicate whether a plain point `s` and/or an infinitesimal point `s + ε` are
/// required, where `s` is the atom's boundary value.
fn lower_bound_points(rel: lra::Rel, x_coeff_positive: bool) -> (bool, bool) {
    let mut plain = false;
    let mut eps = false;
    for r in [rel, rel.negate()] {
        // Normalise `form REL 0` to `x REL' s`: dividing by a negative
        // coefficient reverses the inequality direction.
        let rn = if x_coeff_positive { r } else { r.flip() };
        match rn {
            lra::Rel::Ge | lra::Rel::Eq => plain = true,
            lra::Rel::Gt | lra::Rel::Ne => eps = true,
            lra::Rel::Lt | lra::Rel::Le => {}
        }
    }
    (plain, eps)
}

impl VirtualTermEliminator {
    /// Create a new virtual term eliminator.
    pub fn new() -> Self {
        Self {
            stats: VirtualTermStats::default(),
        }
    }

    /// Eliminate an existential quantifier `∃var. formula(var)` over linear real
    /// arithmetic.
    ///
    /// On success returns a quantifier-free formula equivalent to
    /// `∃var. formula` in which `var` does not occur. Returns `Err` for
    /// formulae outside the supported linear-real fragment (soundness is
    /// preserved: no wrong or `var`-containing result is ever returned as
    /// `Ok`).
    pub fn eliminate_exists(
        &mut self,
        var: String,
        formula: TermId,
        tm: &mut TermManager,
    ) -> Result<TermId, String> {
        let x = tm.intern_str(&var);

        // If `x` does not occur, ∃x.φ ≡ φ.
        if !lra::mentions_var(formula, x, tm) {
            self.stats.quantifiers_eliminated += 1;
            return Ok(formula);
        }

        // The infinitesimal shift `s + ε` is only valid over a dense order.
        let real_sort = tm.sorts.real_sort;
        if lra::find_var_sort(formula, x, tm) != Some(real_sort) {
            return Err(
                "virtual_term: Loos-Weispfenning virtual substitution requires real sort \
                 (use CooperEliminator for integers)"
                    .to_string(),
            );
        }

        // Build the "from below" elimination set from every atom mentioning x.
        let mut atoms = Vec::new();
        lra::collect_x_atoms(formula, x, tm, &mut atoms)?;

        let mut plain_points: Vec<TermId> = Vec::new();
        let mut eps_points: Vec<TermId> = Vec::new();
        for a in &atoms {
            let (plain, eps) = lower_bound_points(a.rel, a.x_coeff.is_positive());
            if !(plain || eps) {
                continue;
            }
            let s = lra::boundary_term(&a.x_coeff, &a.others, &a.constant, tm)
                .ok_or("virtual_term: coefficient too large to eliminate")?;
            if plain {
                plain_points.push(s);
            }
            if eps {
                eps_points.push(s);
            }
        }
        plain_points.sort_by_key(|t| t.0);
        plain_points.dedup();
        eps_points.sort_by_key(|t| t.0);
        eps_points.dedup();

        let x_id = tm.mk_var(&var, real_sort);
        let mut disjuncts: Vec<TermId> = Vec::new();

        // -∞ test point.
        let neg_inf = lra::inf_rewrite(formula, x, false, tm)?;
        disjuncts.push(neg_inf);
        self.stats.test_points_evaluated += 1;

        // Non-strict / equality lower bounds: substitute the exact value `s`.
        for s in plain_points {
            let mut subst = FxHashMap::default();
            subst.insert(x_id, s);
            let substituted = tm.substitute(formula, &subst);
            disjuncts.push(tm.simplify(substituted));
            self.stats.virtual_terms_generated += 1;
            self.stats.test_points_evaluated += 1;
        }

        // Strict / disequality lower bounds: virtually substitute `s + ε`.
        for s in eps_points {
            let d = lra::eps_rewrite(formula, x, s, tm)?;
            disjuncts.push(tm.simplify(d));
            self.stats.virtual_terms_generated += 1;
            self.stats.test_points_evaluated += 1;
        }

        self.stats.quantifiers_eliminated += 1;
        let result = tm.mk_or(disjuncts);
        Ok(tm.simplify(result))
    }

    /// Get statistics.
    pub fn stats(&self) -> &VirtualTermStats {
        &self.stats
    }
}

impl Default for VirtualTermEliminator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::TermKind;
    use num_bigint::BigInt;
    use num_rational::{BigRational, Rational64};
    use num_traits::{One, Zero};

    fn real_var(tm: &mut TermManager, name: &str) -> TermId {
        let real_sort = tm.sorts.real_sort;
        tm.mk_var(name, real_sort)
    }

    fn rl(tm: &mut TermManager, n: i64) -> TermId {
        tm.mk_real(Rational64::new(n, 1))
    }

    /// Exact-rational ground evaluator over the fragment the eliminator emits.
    fn eval_bool(tm: &TermManager, id: TermId) -> bool {
        fn num(tm: &TermManager, id: TermId) -> BigRational {
            match &tm.get(id).expect("term").kind {
                TermKind::IntConst(n) => BigRational::from_integer(n.clone()),
                TermKind::RealConst(r) => {
                    BigRational::new(BigInt::from(*r.numer()), BigInt::from(*r.denom()))
                }
                TermKind::Neg(a) => -num(tm, *a),
                TermKind::Add(args) => args
                    .iter()
                    .fold(BigRational::zero(), |acc, &a| acc + num(tm, a)),
                TermKind::Sub(a, b) => num(tm, *a) - num(tm, *b),
                TermKind::Mul(args) => args
                    .iter()
                    .fold(BigRational::one(), |acc, &a| acc * num(tm, a)),
                other => panic!("unexpected arithmetic term {other:?}"),
            }
        }
        match &tm.get(id).expect("term").kind {
            TermKind::True => true,
            TermKind::False => false,
            TermKind::Not(a) => !eval_bool(tm, *a),
            TermKind::And(args) => args.iter().all(|&a| eval_bool(tm, a)),
            TermKind::Or(args) => args.iter().any(|&a| eval_bool(tm, a)),
            TermKind::Implies(a, b) => !eval_bool(tm, *a) || eval_bool(tm, *b),
            TermKind::Lt(a, b) => num(tm, *a) < num(tm, *b),
            TermKind::Le(a, b) => num(tm, *a) <= num(tm, *b),
            TermKind::Gt(a, b) => num(tm, *a) > num(tm, *b),
            TermKind::Ge(a, b) => num(tm, *a) >= num(tm, *b),
            TermKind::Eq(a, b) => num(tm, *a) == num(tm, *b),
            other => panic!("unexpected boolean term {other:?}"),
        }
    }

    #[test]
    fn test_eliminator_starts_empty() {
        let e = VirtualTermEliminator::new();
        assert_eq!(e.stats().quantifiers_eliminated, 0);
    }

    #[test]
    fn strict_open_interval_is_true() {
        // ∃x. (x > 2) ∧ (x < 4)   → true.
        let mut tm = TermManager::new();
        let x = real_var(&mut tm, "x");
        let two = rl(&mut tm, 2);
        let four = rl(&mut tm, 4);
        let c1 = tm.mk_gt(x, two);
        let c2 = tm.mk_lt(x, four);
        let phi = tm.mk_and(vec![c1, c2]);

        let mut e = VirtualTermEliminator::new();
        let result = e
            .eliminate_exists("x".to_string(), phi, &mut tm)
            .expect("elimination should succeed");
        let x_spur = tm.intern_str("x");
        assert!(!lra::mentions_var(result, x_spur, &tm), "x still present");
        assert!(eval_bool(&tm, result), "expected true");
    }

    #[test]
    fn strict_empty_interval_is_false() {
        // ∃x. (x > 2) ∧ (x < 2)   → false.
        let mut tm = TermManager::new();
        let x = real_var(&mut tm, "x");
        let two = rl(&mut tm, 2);
        let c1 = tm.mk_gt(x, two);
        let c2 = tm.mk_lt(x, two);
        let phi = tm.mk_and(vec![c1, c2]);

        let mut e = VirtualTermEliminator::new();
        let result = e
            .eliminate_exists("x".to_string(), phi, &mut tm)
            .expect("elimination should succeed");
        let x_spur = tm.intern_str("x");
        assert!(!lra::mentions_var(result, x_spur, &tm), "x still present");
        assert!(!eval_bool(&tm, result), "expected false");
    }

    #[test]
    fn half_open_boundary_via_epsilon() {
        // ∃x. (x > 2) ∧ (x ≤ 2)   → false: the strict lower bound has no room.
        let mut tm = TermManager::new();
        let x = real_var(&mut tm, "x");
        let two = rl(&mut tm, 2);
        let c1 = tm.mk_gt(x, two);
        let c2 = tm.mk_le(x, two);
        let phi = tm.mk_and(vec![c1, c2]);

        let mut e = VirtualTermEliminator::new();
        let result = e
            .eliminate_exists("x".to_string(), phi, &mut tm)
            .expect("elimination should succeed");
        assert!(!eval_bool(&tm, result), "expected false");
    }

    #[test]
    fn unbounded_below_is_true() {
        // ∃x. x < 5   → true (witnessed at -∞).
        let mut tm = TermManager::new();
        let x = real_var(&mut tm, "x");
        let five = rl(&mut tm, 5);
        let phi = tm.mk_lt(x, five);

        let mut e = VirtualTermEliminator::new();
        let result = e
            .eliminate_exists("x".to_string(), phi, &mut tm)
            .expect("elimination should succeed");
        assert!(eval_bool(&tm, result), "expected true");
    }

    #[test]
    fn disequality_is_satisfiable() {
        // ∃x. x ≠ 3   → true over the reals.
        let mut tm = TermManager::new();
        let x = real_var(&mut tm, "x");
        let three = rl(&mut tm, 3);
        let eq = tm.mk_eq(x, three);
        let phi = tm.mk_not(eq);

        let mut e = VirtualTermEliminator::new();
        let result = e
            .eliminate_exists("x".to_string(), phi, &mut tm)
            .expect("elimination should succeed");
        assert!(eval_bool(&tm, result), "expected true");
    }

    #[test]
    fn integer_sort_is_rejected() {
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let x = tm.mk_var("x", int_sort);
        let five = tm.mk_int(5);
        let phi = tm.mk_lt(x, five);

        let mut e = VirtualTermEliminator::new();
        assert!(
            e.eliminate_exists("x".to_string(), phi, &mut tm).is_err(),
            "integer sort must be rejected, not faked"
        );
    }

    #[test]
    fn nonlinear_is_rejected() {
        let mut tm = TermManager::new();
        let x = real_var(&mut tm, "x");
        let y = real_var(&mut tm, "y");
        let xx = tm.mk_mul(vec![x, x]);
        let phi = tm.mk_eq(xx, y);

        let mut e = VirtualTermEliminator::new();
        assert!(
            e.eliminate_exists("x".to_string(), phi, &mut tm).is_err(),
            "non-linear input must be rejected, not faked"
        );
    }
}
