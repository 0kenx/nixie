//! Linear inequality decision procedure for the NRA solver.
//!
//! [`NraSolver::check_sat`](crate::grobner::buchberger::NraSolver::check_sat)
//! cannot resolve non-constant polynomial inequalities on its own -- it only
//! reduces a constraint modulo the equalities' Gröbner basis. When what's left
//! after reduction is *linear* (affine, degree <= 1 in every variable), it is a
//! real linear-real-arithmetic decision problem, decided here by exact-rational
//! Fourier-Motzkin elimination (Fourier 1826 / Motzkin 1936; Bradley & Manna,
//! *The Calculus of Computation*, §5.3) instead of giving up with `Unknown`.
//!
//! A `delta`-margin reduction against `oxiz_math::simplex::SimplexTableau`
//! (`p >= delta` for shrinking trial `delta > 0`) was considered first, but
//! rejected: it is sound for Sat but can never *prove* Unsat for a system whose
//! non-strict relaxation is satisfiable only on the shared boundary -- the
//! canonical `x > 0 ∧ x < 0` case (satisfiable at `x = 0` once relaxed,
//! genuinely Unsat once strict). No finite grid of trial `delta` values can
//! distinguish "the supremum of feasible `delta` is 0" from "an even smaller
//! `delta` would work"; that needs real LP optimization, which `SimplexTableau`
//! does not expose. Fourier-Motzkin avoids this: strict and non-strict bounds
//! combine exactly (strict iff either parent was strict), deciding Sat/Unsat
//! outright with no epsilon machinery.
//!
//! Disequalities (`p != 0`) are disjunctive (`p > 0` or `p < 0`) and are
//! handled by explicit case-split over all sign combinations.

use crate::grobner::buchberger::{Relation, SatResult};
use crate::polynomial::{Polynomial, Var};
use crate::prelude::FxHashMap;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

/// Cap on resolvent atoms tracked during Fourier-Motzkin elimination:
/// eliminating one variable can multiply the atom count by up to
/// (lower-bound atoms) x (upper-bound atoms), so a pathological input could
/// blow this up. Beyond the cap we return an honest `Unknown` instead of an
/// unbounded stall; small conjunctions (what this solver actually sees)
/// stay far below it.
const FM_MAX_ATOMS: usize = 20_000;

/// Cap on `!=` constraints handled by explicit `p > 0` / `p < 0` case-split
/// (2^k branches); beyond this, `Unknown` rather than an exponential stall.
const MAX_DISEQUALITY_BRANCHES: u32 = 12;

/// A linear atom `sum(coeffs[v] * v) + constant (>=|>) 0`: the canonical
/// form Fourier-Motzkin elimination operates on (every relation normalized
/// to a lower-bound-style `>= 0` / `> 0`).
#[derive(Debug, Clone)]
struct LinearAtom {
    coeffs: FxHashMap<Var, BigRational>,
    constant: BigRational,
    strict: bool,
}

impl LinearAtom {
    /// Build the canonical atom for `poly (relation) 0`: `relation` is one
    /// of `Greater`/`GreaterEqual`/`Less`/`LessEqual` (callers normalize
    /// away `Equal`/`NotEqual` first) and `poly` is linear.
    fn from_polynomial(poly: &Polynomial, relation: Relation) -> Self {
        debug_assert!(matches!(
            relation,
            Relation::Greater | Relation::GreaterEqual | Relation::Less | Relation::LessEqual
        ));

        let negate = matches!(relation, Relation::Less | Relation::LessEqual);
        let strict = matches!(relation, Relation::Greater | Relation::Less);

        let mut coeffs: FxHashMap<Var, BigRational> = FxHashMap::default();
        let mut constant = BigRational::zero();

        for term in poly.terms() {
            if term.monomial.is_unit() {
                constant += term.coeff.clone();
                continue;
            }
            // `poly.is_linear()` is guaranteed by the caller chain (checked
            // in `NraSolver::check_sat`), so every non-constant term is a
            // single variable to the first power.
            let vp = term.monomial.vars()[0];
            let entry = coeffs.entry(vp.var).or_insert_with(BigRational::zero);
            *entry += term.coeff.clone();
        }

        if negate {
            constant = -constant;
            for c in coeffs.values_mut() {
                *c = -core::mem::replace(c, BigRational::zero());
            }
        }

        Self {
            coeffs,
            constant,
            strict,
        }
    }

    /// Coefficient of `var` in this atom (zero if `var` does not appear).
    fn coeff(&self, var: Var) -> BigRational {
        self.coeffs
            .get(&var)
            .cloned()
            .unwrap_or_else(BigRational::zero)
    }
}

/// Eliminate `var` from `atoms` via Fourier-Motzkin resolution, returning
/// `None` if the resolvent count would exceed [`FM_MAX_ATOMS`].
fn fm_eliminate_var(atoms: Vec<LinearAtom>, var: Var) -> Option<Vec<LinearAtom>> {
    let mut no_var = Vec::new();
    let mut lower = Vec::new(); // positive coefficient of `var`: a lower bound on `var`
    let mut upper = Vec::new(); // negative coefficient of `var`: an upper bound on `var`

    for atom in atoms {
        let c = atom.coeff(var);
        if c.is_zero() {
            no_var.push(atom);
        } else if c.is_positive() {
            lower.push(atom);
        } else {
            upper.push(atom);
        }
    }

    if no_var.len() + lower.len() * upper.len() > FM_MAX_ATOMS {
        return None;
    }

    for l in &lower {
        let c_v = l.coeff(var); // > 0
        for u in &upper {
            let d_v = u.coeff(var); // < 0
            // Scale `l` by `-d_v` (>0) and `u` by `c_v` (>0): the `var` terms
            // cancel exactly (coefficient (-d_v*c_v + c_v*d_v) = 0), and
            // since both scale factors are positive, each parent's relation
            // direction survives the scaling -- so the sum is a valid
            // entailed constraint.
            let pos_l = -d_v;
            let pos_u = c_v.clone();

            let mut coeffs: FxHashMap<Var, BigRational> = FxHashMap::default();
            for (&w, c) in &l.coeffs {
                if w == var {
                    continue;
                }
                *coeffs.entry(w).or_insert_with(BigRational::zero) += &pos_l * c;
            }
            for (&w, c) in &u.coeffs {
                if w == var {
                    continue;
                }
                *coeffs.entry(w).or_insert_with(BigRational::zero) += &pos_u * c;
            }
            coeffs.retain(|_, c| !c.is_zero());

            let constant = &pos_l * &l.constant + &pos_u * &u.constant;
            let strict = l.strict || u.strict;

            no_var.push(LinearAtom {
                coeffs,
                constant,
                strict,
            });
        }
    }

    Some(no_var)
}

/// Decide satisfiability of a conjunction of canonical linear atoms by
/// eliminating `vars` one at a time, then checking the surviving constants.
fn fm_decide(mut atoms: Vec<LinearAtom>, vars: &[Var]) -> SatResult {
    for &var in vars {
        match fm_eliminate_var(atoms, var) {
            Some(next) => atoms = next,
            None => return SatResult::Unknown,
        }
    }

    // Every variable eliminated: each atom is now a pure `constant (>=|>) 0`.
    for atom in &atoms {
        let ok = if atom.strict {
            atom.constant.is_positive()
        } else {
            !atom.constant.is_negative()
        };
        if !ok {
            return SatResult::Unsat;
        }
    }

    SatResult::Sat
}

/// Decide satisfiability of a conjunction of linear polynomial constraints
/// (some of which may be `!=`, handled via case-split). `constraints` must
/// already be reduced modulo the equality Gröbner basis and every
/// polynomial must be linear; enforced by the sole caller, `check_sat`.
pub(crate) fn decide_linear_arms(constraints: &[(&Polynomial, Relation)]) -> SatResult {
    let mut definite: Vec<(&Polynomial, Relation)> = Vec::new();
    let mut disequalities: Vec<&Polynomial> = Vec::new();

    for (poly, relation) in constraints {
        match relation {
            Relation::NotEqual => disequalities.push(poly),
            // `Equal` never reaches `self.inequalities` (see
            // `add_constraint`), but handle it correctly anyway (as the
            // conjunction of both non-strict bounds) rather than assume.
            Relation::Equal => {
                definite.push((poly, Relation::GreaterEqual));
                definite.push((poly, Relation::LessEqual));
            }
            other => definite.push((poly, *other)),
        }
    }

    if disequalities.len() as u32 > MAX_DISEQUALITY_BRANCHES {
        return SatResult::Unknown;
    }

    let branch_count = 1u32 << disequalities.len();
    let mut any_unknown = false;

    for branch in 0..branch_count {
        let mut arms = definite.clone();
        for (bit, poly) in disequalities.iter().enumerate() {
            let relation = if (branch >> bit) & 1 == 0 {
                Relation::Greater
            } else {
                Relation::Less
            };
            arms.push((*poly, relation));
        }

        match linear_system_sat(&arms) {
            SatResult::Sat => return SatResult::Sat,
            SatResult::Unknown => any_unknown = true,
            SatResult::Unsat => {}
        }
    }

    if any_unknown {
        SatResult::Unknown
    } else {
        // Every branch (or the single definite system, if there were no
        // disequalities) was proven infeasible: the disjunction is infeasible.
        SatResult::Unsat
    }
}

/// Decide satisfiability of one conjunction of definite (non-`!=`, non-`=`)
/// linear relations via exact-rational Fourier-Motzkin elimination.
fn linear_system_sat(arms: &[(&Polynomial, Relation)]) -> SatResult {
    let mut vars: Vec<Var> = Vec::new();
    for (poly, _) in arms {
        for term in poly.terms() {
            for vp in term.monomial.vars() {
                if !vars.contains(&vp.var) {
                    vars.push(vp.var);
                }
            }
        }
    }
    vars.sort_unstable();

    let atoms: Vec<LinearAtom> = arms
        .iter()
        .map(|(poly, relation)| LinearAtom::from_polynomial(poly, *relation))
        .collect();

    fm_decide(atoms, &vars)
}

#[cfg(test)]
mod tests {
    use super::*;

    // -----------------------------------------------------------------
    // Whitebox regression test for the Fourier-Motzkin resolvent used by
    // the linear inequality decision procedure (`decide_linear_arms` /
    // `linear_system_sat`). Public-API-level coverage of `check_sat` with
    // linear inequalities lives in
    // `oxiz-math/tests/audit_qe_math_follow.rs` (it needs no access to
    // these private internals).
    // -----------------------------------------------------------------

    #[test]
    fn test_fm_eliminate_var_combines_strict_and_non_strict_correctly() {
        // Directly exercise the Fourier-Motzkin resolvent: x >= 0 (lower,
        // non-strict) and -x > 0 i.e. x < 0 (upper, strict) eliminate to
        // `0 > 0`, which is false -- so the pair is Unsat. The combined
        // atom must inherit strictness from its strict parent.
        let ge = LinearAtom::from_polynomial(&Polynomial::from_var(0), Relation::GreaterEqual);
        let lt = LinearAtom::from_polynomial(&Polynomial::from_var(0), Relation::Less);

        let resolved = fm_eliminate_var(vec![ge, lt], 0).expect("small system stays under cap");
        assert_eq!(resolved.len(), 1);
        assert!(resolved[0].coeffs.is_empty());
        assert!(
            resolved[0].strict,
            "resolvent of a strict parent must be strict"
        );
        assert!(
            !resolved[0].constant.is_positive() && !resolved[0].constant.is_negative(),
            "0 > 0 must reduce to a false constant atom (constant == 0, strict)"
        );
    }
}
