//! Certified `sat` over the reals.
//!
//! # What this module claims
//!
//! [`certify`] answers `true` only after it has built a concrete, *total*
//! interpretation of every symbol a real goal mentions and checked that every
//! assertion – ground and quantified alike – is true under it.  That is a model
//! in the ordinary semantic sense, so `sat` follows without appealing to the
//! ground solver's verdict or to "no counterexample was found".  `false` says
//! nothing and leaves the caller's `unknown` in place.
//!
//! # Why a finite computation decides an infinite domain
//!
//! The integer certifier ([`super::eval`]) enumerates one representative per
//! region because its functions are *constant* off their pin tables.  Over the
//! reals that is not enough: `∀x. f(x) = x` has no such model at all.  So the
//! real engine interprets each function as pins plus an **affine** default
//! `λy. a·y + b`, and pays for it by evaluating *symbolically* instead of
//! pointwise.
//!
//! Under such an interpretation every term of the fragment
//! [`harvest::harvest`] accepts denotes a **piecewise-affine** function of the
//! bound variable, and every atom a **piecewise-constant** truth value:
//!
//! * a literal, a free constant and the bound variable are affine outright;
//! * `+`, `-`, and multiplication or division by a constant preserve
//!   affineness (a genuinely quadratic product is refused);
//! * an application `f(t)` is affine on each cell where `t` is: `t` meets each
//!   of the finitely many pinned arguments at most once, and cutting the line
//!   at those meeting points leaves cells on which either `t` is constant (so
//!   `f(t)` is a single pinned or default value) or `t` misses every pin (so
//!   `f(t) = default ∘ t`, again affine).  Nested applications compose, which
//!   is what decides `f(g(x)) = g(f(x))`;
//! * a comparison of two affine forms changes truth only where their difference
//!   crosses zero – one point – so cutting there leaves each cell with a single
//!   constant verdict.
//!
//! Each of those steps adds finitely many cuts, so the body ends up as a
//! partition of `ℝ` into finitely many **non-empty** cells with one verdict
//! each.  Non-emptiness is what makes the last step an equivalence rather than
//! an approximation: `∀x. body` iff every cell says `true`, and `∃x. body` iff
//! some cell does.  The existential witness is therefore *found*, not guessed.
//!
//! # Where the candidate interpretations come from
//!
//! Pins come from the goal's own literal equations and from the ground model;
//! defaults are searched over a small ordered set (a macro definition the goal
//! states, the affine through two pins, the identity, the pinned values, zero,
//! the goal's literals) – see [`synth`].  Nothing in that search is trusted:
//! every combination is verified in full before `true` is returned.
//!
//! Reference: Ge & de Moura, "Complete instantiation for quantified formulas in
//! SMT" (CAV 2009), and Z3's `smt/smt_model_finder.cpp` / macro-finder
//! treatment of quasi-macro definitions.

mod affine;
mod eval;
mod harvest;
mod interp;
mod synth;

use oxiz_core::ast::{TermId, TermManager};
use oxiz_core::interner::Spur;

#[allow(unused_imports)]
use crate::prelude::*;

use super::value::ValueSort;
use affine::{Affine, Rat};
use eval::{RealEvalError, evaluate};
use interp::{RealFunc, RealInterp};
use synth::{RealFacts, collect_facts, detect_macros, num_candidates};

/// Cap on the number of default *combinations* across all function symbols.
const MAX_COMBINATIONS: usize = 512;

/// Try to certify a real goal satisfiable by constructing and verifying a total
/// interpretation.
///
/// Declines immediately – before any search – on a goal outside the real
/// fragment, so the integer certifier and this one never share a goal and each
/// verdict rests on the completeness argument written for its own domain.
pub(crate) fn certify(
    assertions: &[TermId],
    assignments: &FxHashMap<TermId, TermId>,
    manager: &TermManager,
) -> bool {
    let Some(harvested) = harvest::harvest(assertions, manager) else {
        return false;
    };
    // A goal with no quantifier is the ground solver's business.
    if !harvested.has_quantifier {
        return false;
    }

    let facts = collect_facts(assertions, assignments, manager, &harvested);
    let macros = detect_macros(assertions, manager);

    // Every free constant needs a value, or the interpretation is not total.
    for (name, sort) in &harvested.consts {
        let known = match sort {
            ValueSort::Real => facts.consts.contains_key(name),
            ValueSort::Bool => facts.bool_consts.contains_key(name),
            ValueSort::Int => false,
        };
        if !known {
            return false;
        }
    }

    let mut literals = harvested.literals.clone();
    literals.sort();
    literals.dedup();

    // Deterministic order: the search's outcome must not depend on hash-map
    // iteration order.
    let mut symbols: Vec<(Spur, ValueSort)> = harvested
        .funcs
        .iter()
        .map(|(&func, &sort)| (func, sort))
        .collect();
    symbols.sort_by(|a, b| manager.resolve_str(a.0).cmp(manager.resolve_str(b.0)));

    let candidates: Vec<Vec<Affine>> = symbols
        .iter()
        .map(|&(func, sort)| match sort {
            // A predicate's "affine default" is one of the two truth values;
            // they are carried as `0` and `1` and read back in `build`.
            ValueSort::Bool => vec![
                Affine::constant(Rat::from_integer(0.into())),
                Affine::constant(Rat::from_integer(1.into())),
            ],
            ValueSort::Real => num_candidates(func, &facts, &macros, &literals),
            ValueSort::Int => Vec::new(),
        })
        .collect();

    let mut combinations: usize = 1;
    for list in &candidates {
        if list.is_empty() {
            return false;
        }
        match combinations.checked_mul(list.len()) {
            Some(total) if total <= MAX_COMBINATIONS => combinations = total,
            _ => return false,
        }
    }

    let mut odometer = vec![0usize; candidates.len()];
    for _ in 0..combinations {
        let Some(interpretation) = build(&symbols, &candidates, &odometer, &facts) else {
            return false;
        };
        match verify(assertions, &interpretation, manager) {
            Ok(true) => return true,
            Ok(false) => {}
            // An unsupported construct is a property of the *goal*, not of the
            // candidate default, so no later combination can do better.
            Err(RealEvalError::Unsupported) => return false,
            Err(RealEvalError::Exhausted) => return false,
        }
        if !advance(&mut odometer, &candidates) {
            break;
        }
    }
    false
}

/// Assemble the interpretation the current odometer position describes.
fn build(
    symbols: &[(Spur, ValueSort)],
    candidates: &[Vec<Affine>],
    odometer: &[usize],
    facts: &RealFacts,
) -> Option<RealInterp> {
    let mut interpretation = RealInterp {
        funcs: FxHashMap::default(),
        consts: facts.consts.clone(),
        bool_consts: facts.bool_consts.clone(),
    };
    for (index, &(func, sort)) in symbols.iter().enumerate() {
        let position = *odometer.get(index)?;
        let default = candidates.get(index)?.get(position)?.clone();
        let entry = match sort {
            ValueSort::Real => {
                let mut pins: Vec<(Rat, Rat)> = facts
                    .num_pins
                    .get(&func)
                    .map(|table| table.iter().map(|(k, v)| (k.clone(), v.clone())).collect())
                    .unwrap_or_default();
                pins.sort();
                RealFunc::Num { pins, default }
            }
            ValueSort::Bool => {
                let mut pins: Vec<(Rat, bool)> = facts
                    .bool_pins
                    .get(&func)
                    .map(|table| table.iter().map(|(k, v)| (k.clone(), *v)).collect())
                    .unwrap_or_default();
                pins.sort_by(|a, b| a.0.cmp(&b.0));
                let flag = default
                    .as_constant()
                    .is_some_and(|value| *value != Rat::from_integer(0.into()));
                RealFunc::Bool {
                    pins,
                    default: flag,
                }
            }
            ValueSort::Int => return None,
        };
        interpretation.funcs.insert(func, entry);
    }
    Some(interpretation)
}

/// Whether every assertion is true under `interpretation`.
fn verify(
    assertions: &[TermId],
    interpretation: &RealInterp,
    manager: &TermManager,
) -> Result<bool, RealEvalError> {
    for &assertion in assertions {
        if !evaluate(assertion, interpretation, manager)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Step the odometer to the next default combination, or report that the search
/// space is exhausted.
fn advance(odometer: &mut [usize], candidates: &[Vec<Affine>]) -> bool {
    for index in (0..odometer.len()).rev() {
        let limit = candidates.get(index).map_or(0, Vec::len);
        let Some(position) = odometer.get_mut(index) else {
            continue;
        };
        *position += 1;
        if *position < limit {
            return true;
        }
        *position = 0;
    }
    false
}

#[cfg(test)]
mod tests;
