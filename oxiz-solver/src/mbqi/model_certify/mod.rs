//! Certified `sat` for quantified goals: build a total interpretation and
//! *verify* every assertion under it.
//!
//! # What this module claims
//!
//! [`certify`] answers `true` only when it has constructed a concrete, total
//! interpretation of every symbol the assertion set mentions and checked that
//! **every assertion – ground and quantified alike – evaluates to `true`**
//! under it.  That is a model in the ordinary semantic sense, so `sat` follows
//! without any appeal to the ground solver's verdict, to a saturation
//! argument, or to "no counterexample was found".  A `false` answer says
//! nothing: the caller keeps its existing behaviour and, ultimately, answers
//! `unknown`.
//!
//! # The interpretation: pins plus a *searched* default
//!
//! Each uninterpreted function is interpreted as the finite pin table the
//! ground model already fixed (`f(0, 0) := 1`, ...) extended by one default
//! value everywhere else.  The default is **not** zero and is not guessed
//! once: it is searched over the values the goal itself makes plausible – the
//! function's own pinned results first, then `0`, then the goal's integer
//! literals – and each candidate is *checked*, not assumed.  That search is
//! what decides
//!
//! ```text
//! (assert (forall ((x Int)) (= (f (f x)) (f x))))   with  f(0)=5, f(5)=5, f(3)=3
//! ```
//!
//! – no constant default of `0` satisfies it, `f := pins + 5` does, and the
//! certifier finds that by trying and verifying.
//!
//! # Why a finite check decides an infinite domain
//!
//! Under a pins-plus-default interpretation the only integers any atom can
//! distinguish are the *critical* ones: the goal's literals, the pinned
//! arguments and results, the constants' values, the defaults, and the values
//! already given to enclosing bound variables.  Those cut `Int` into finitely
//! many regions – one singleton per critical value, one gap between and beyond
//! them – and, for the fragment
//! [`harvest::region_stable`] accepts, the body's truth value is constant
//! across each region:
//!
//! * a bound variable drawn from a gap is not a pinned argument, so every
//!   application over it returns the default – the same value at every point
//!   of the gap, and hence the same value for everything built on top;
//! * a bound variable is otherwise only ever *compared*, and only against
//!   critical values or other bound variables, whose own values join the
//!   critical set before their domains are built.
//!
//! So enumerating one representative per region – which is exactly what
//! [`eval::evaluate`] does – decides `∀`/`∃` over the whole of `Int`.  Outside
//! that fragment the module declines; it never trades the argument for a
//! sample.
//!
//! # Existentials are witnessed, not guessed
//!
//! Because the same enumeration decides `∃`, a `forall`-`exists` alternation
//! is certified by *finding* the witness for every representative of the outer
//! variable – the Skolem function is realised pointwise by the search rather
//! than instantiated with candidate ground terms.
//!
//! Reference: Ge & de Moura, "Complete instantiation for quantified formulas in
//! SMT" (CAV 2009), and Z3's `smt/smt_model_finder.cpp` default-value model
//! construction.

mod eval;
mod harvest;
mod real;
mod value;

#[cfg(test)]
mod tests;

use num_bigint::BigInt;
use oxiz_core::ast::{TermId, TermManager};
use oxiz_core::interner::Spur;

#[allow(unused_imports)]
use crate::prelude::*;

use eval::{EvalError, evaluate};
use harvest::{ModelFacts, harvest, read_model, region_stable};
use value::{CertValue, FuncInterp, Interpretation, ValueSort};

/// Cap on the number of default values tried per function symbol.
const MAX_DEFAULT_CANDIDATES: usize = 8;

/// Cap on the number of default *combinations* across all function symbols.
const MAX_COMBINATIONS: usize = 512;

/// Cap on the total number of evaluation steps one [`certify`] call may spend.
///
/// Bounds the certifier's cost independently of how the search goes.  Running
/// out declines, so this can only cost completeness.
const CERTIFY_STEP_BUDGET: usize = 4_000_000;

/// Try to certify `assertions` satisfiable by constructing and verifying a
/// total interpretation built from the ground model `assignments`.
///
/// Answers `true` only with a verified model in hand (see the module docs).
pub(crate) fn certify(
    assertions: &[TermId],
    assignments: &FxHashMap<TermId, TermId>,
    manager: &TermManager,
) -> bool {
    // The real engine ([`real`]) declines a goal that mentions an
    // integer-sorted symbol and the integer engine below declines one that
    // mentions a real, so exactly one of them can ever certify a given goal –
    // and each does so under the completeness argument written for its own
    // domain.
    if real::certify(assertions, assignments, manager) {
        return true;
    }

    let Some(facts) = prepare(assertions, assignments, manager) else {
        return false;
    };
    let Preparation {
        model,
        symbols,
        base_ints,
    } = facts;

    let candidates: Vec<Vec<CertValue>> = symbols
        .iter()
        .map(|&(func, sort)| default_candidates(func, sort, &model, &base_ints))
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

    let mut budget = CERTIFY_STEP_BUDGET;
    let mut odometer = vec![0usize; candidates.len()];
    for _ in 0..combinations {
        let interpretation = build_interpretation(&symbols, &candidates, &odometer, &model);
        let critical = critical_set(&base_ints, &interpretation);
        match verify(assertions, &interpretation, manager, &critical, &mut budget) {
            Ok(true) => return true,
            Ok(false) => {}
            Err(EvalError::Exhausted) => return false,
            Err(EvalError::Unsupported) => return false,
        }
        if !advance(&mut odometer, &candidates) {
            break;
        }
    }
    false
}

/// The inputs the default search iterates over.
struct Preparation {
    /// Pins and constant values read off the ground model.
    model: ModelFacts,
    /// Function symbols needing an interpretation, in a deterministic order.
    symbols: Vec<(Spur, ValueSort)>,
    /// Integer literals of the goal plus every integer the model fixes.
    base_ints: Vec<BigInt>,
}

/// Harvest the goal, check it is inside the certifiable fragment, and read the
/// ground model – or decline.
fn prepare(
    assertions: &[TermId],
    assignments: &FxHashMap<TermId, TermId>,
    manager: &TermManager,
) -> Option<Preparation> {
    let harvested = harvest(assertions, manager)?;
    // A goal with no quantifier is the ground solver's business; certifying it
    // here would only duplicate work.
    if !harvested.has_quantifier {
        return None;
    }
    // A real-sorted symbol is the real engine's business; the region argument
    // below is written for `Int` and does not transfer.
    if harvested
        .applied
        .values()
        .any(|&sort| sort == ValueSort::Real)
    {
        return None;
    }
    if !region_stable(assertions, &harvested.bound_names, manager) {
        return None;
    }

    let model = read_model(assignments, &harvested.bound_names, manager);

    let mut symbols: Vec<(Spur, ValueSort)> = harvested
        .applied
        .iter()
        .map(|(&func, &sort)| (func, sort))
        .collect();
    // Deterministic order: the search's outcome must not depend on hash-map
    // iteration order.
    symbols.sort_by(|a, b| manager.resolve_str(a.0).cmp(manager.resolve_str(b.0)));

    let mut base_ints = harvested.int_consts;
    for table in model.pins.values() {
        for (args, result) in table {
            for arg in args {
                if let CertValue::Int(n) = arg {
                    base_ints.push(n.clone());
                }
            }
            if let CertValue::Int(n) = result {
                base_ints.push(n.clone());
            }
        }
    }
    for value in model.consts.values() {
        if let CertValue::Int(n) = value {
            base_ints.push(n.clone());
        }
    }
    base_ints.sort();
    base_ints.dedup();

    Some(Preparation {
        model,
        symbols,
        base_ints,
    })
}

/// The default values worth trying for one function symbol, most promising
/// first.
///
/// A function's own pinned results come first: an interpretation that reuses a
/// value the model already committed to is the one most likely to keep the
/// pinned constraints and the quantifier consistent (it is what makes
/// `f(f x) = f x` work with `f := pins + 5`).  Then `0`, then the goal's own
/// integer literals.
fn default_candidates(
    func: Spur,
    sort: ValueSort,
    model: &ModelFacts,
    base_ints: &[BigInt],
) -> Vec<CertValue> {
    if sort == ValueSort::Bool {
        return vec![CertValue::Bool(false), CertValue::Bool(true)];
    }

    let mut seen: FxHashSet<BigInt> = FxHashSet::default();
    let mut out: Vec<CertValue> = Vec::new();
    let push = |n: BigInt, out: &mut Vec<CertValue>, seen: &mut FxHashSet<BigInt>| {
        if out.len() < MAX_DEFAULT_CANDIDATES && seen.insert(n.clone()) {
            out.push(CertValue::Int(n));
        }
    };

    if let Some(table) = model.pins.get(&func) {
        let mut pinned: Vec<BigInt> = table.values().filter_map(|v| v.as_int().cloned()).collect();
        pinned.sort();
        pinned.dedup();
        for n in pinned {
            push(n, &mut out, &mut seen);
        }
    }
    push(BigInt::from(0), &mut out, &mut seen);
    for n in base_ints {
        push(n.clone(), &mut out, &mut seen);
    }
    out
}

/// Assemble the interpretation the current odometer position describes.
fn build_interpretation(
    symbols: &[(Spur, ValueSort)],
    candidates: &[Vec<CertValue>],
    odometer: &[usize],
    model: &ModelFacts,
) -> Interpretation {
    let mut interpretation = Interpretation {
        funcs: FxHashMap::default(),
        consts: model.consts.clone(),
    };
    for (index, &(func, _)) in symbols.iter().enumerate() {
        let default = odometer
            .get(index)
            .and_then(|&position| candidates.get(index).and_then(|list| list.get(position)))
            .cloned()
            .unwrap_or(CertValue::Int(BigInt::from(0)));
        interpretation.funcs.insert(
            func,
            FuncInterp {
                entries: model.pins.get(&func).cloned().unwrap_or_default(),
                default,
            },
        );
    }
    interpretation
}

/// The integers atoms can distinguish under `interpretation`.
///
/// This is `base_ints` (the goal's literals and everything the model fixes)
/// plus the chosen defaults – a default is a function *result*, so a
/// comparison can see it and the enumeration must be able to straddle it.
fn critical_set(base_ints: &[BigInt], interpretation: &Interpretation) -> Vec<BigInt> {
    let mut out = base_ints.to_vec();
    for interp in interpretation.funcs.values() {
        if let CertValue::Int(n) = &interp.default {
            out.push(n.clone());
        }
    }
    out.sort();
    out.dedup();
    out
}

/// Whether every assertion evaluates to `true` under `interpretation`.
fn verify(
    assertions: &[TermId],
    interpretation: &Interpretation,
    manager: &TermManager,
    critical: &[BigInt],
    budget: &mut usize,
) -> Result<bool, EvalError> {
    for &assertion in assertions {
        match evaluate(assertion, interpretation, manager, critical, budget) {
            Ok(CertValue::Bool(true)) => {}
            Ok(_) => return Ok(false),
            // An unsupported construct is a property of the *goal*, not of the
            // candidate default, so no later combination can do better.
            Err(EvalError::Unsupported) => return Err(EvalError::Unsupported),
            Err(EvalError::Exhausted) => return Err(EvalError::Exhausted),
        }
    }
    Ok(true)
}

/// Step the odometer to the next default combination, or report that the
/// search space is exhausted.
fn advance(odometer: &mut [usize], candidates: &[Vec<CertValue>]) -> bool {
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
