//! Capture-avoiding single-variable substitution shared by the DER and
//! Skolemization tactics.
//!
//! Split out of the former single-file `tactic/quantifier.rs`; see
//! [`super`] for the module layout.
//!
//! # Why this delegates to [`TermManager::substitute`]
//!
//! This module used to carry its own hand-rolled recursive walk. It matched a
//! 21-variant whitelist of `TermKind`s (`Var`, the Boolean connectives,
//! `Eq`, the linear-arithmetic operators, `Ite`, `Apply`, `Select`/`Store`,
//! `Forall`/`Exists`) and ended in
//!
//! ```text
//! // For other terms, just return as-is (constants, etc.)
//! _ => term_id,
//! ```
//!
//! so **every** bit-vector, string, floating-point and datatype operator, plus
//! `Mod`, `Xor`, `Distinct`, `Let` and `Match`, was silently returned
//! unchanged. The comment's "(constants, etc.)" was true only of the literal
//! leaves that also land in that arm; for the operator kinds it was a silent
//! under-substitution.
//!
//! That is not a cosmetic gap. Both callers *drop the binder* they are
//! eliminating:
//!
//! * [`super::DerTactic`] rewrites `∃x. (x = t ∧ ψ(x))` to `ψ(t)` and
//!   `∀x. (x ≠ t ∨ ψ(x))` to `ψ(t)`, and
//! * [`super::SkolemizationTactic`] replaces an existential variable by a
//!   fresh Skolem term and drops its quantifier,
//!
//! and both report the result as an *equisatisfiable rewrite* of the input.
//! When the substitution silently does nothing, the eliminated variable
//! survives in the output as a **free** variable, so the tactic returns a
//! different formula than the one it claims. `∃x:BV8. (x = #x05 ∧ x <u #x01)`
//! is unsatisfiable, but the old code rewrote it to `x <u #x01` with `x` free,
//! which is satisfiable: UNSAT became SAT. See this module's regression tests
//! in `super::tests`. The identical "return the term unchanged when we give
//! up" behaviour in [`TermManager::substitute`]'s since-removed depth cap was
//! confirmed to be a genuine soundness exposure for exactly this reason.
//!
//! The old walk had two further defects:
//!
//! * **No capture avoidance.** Descending into a `Forall`/`Exists` that did
//!   not re-bind the substituted name, it rebuilt the binder verbatim, so
//!   `(forall ((y Int)) (P x y))[x := y]` became
//!   `(forall ((y Int)) (P y y))` -- the substituted free `y` captured. Both
//!   callers can hit this: DER's replacement `t` is an arbitrary term from an
//!   equality, and a Skolem term mentions the governing universal variables,
//!   any of which an inner binder may re-bind. (The retired code's doc comment
//!   asserted a Skolem term "cannot be captured by inner binders of other
//!   variables"; nothing established that.)
//! * **Unguarded native recursion**, once per level of term nesting, so a
//!   deep but perfectly valid term aborted the process with a stack overflow.
//!
//! [`TermManager::substitute`] fixes all four at once: it has an arm for every
//! `TermKind` with no catch-all (a new variant is a compile error there), it is
//! capture-avoiding across all four binder forms, it respects shadowing, and it
//! walks with an explicit heap stack instead of the native call stack. So this
//! is now a thin adapter: resolve the caller's variable *name* to the actual
//! free occurrences it denotes, then hand a one-target map to the core routine.

use crate::ast::{TermId, TermKind, TermManager};
use crate::interner::Spur;
#[allow(unused_imports)]
use crate::prelude::*;

/// Capture-avoiding substitution of the variable named `var_name` by
/// `replacement` throughout `term_id`.
///
/// Only *free* occurrences are replaced: an occurrence inside a
/// `Forall`/`Exists`/`Let`/`Match` that re-binds the same name is a different
/// variable and is left alone (the old implementation got this right for
/// `Forall`/`Exists` and wrong -- by never descending at all -- for `Let` and
/// `Match`). Where a bound variable's name would otherwise capture a free
/// variable of `replacement`, that binder is alpha-renamed first.
///
/// Occurrences are matched by **name alone**, across all sorts, which is what
/// the callers ask for -- they pass a binder's `Spur` and nothing else. Two
/// distinct variables that share a name at different sorts therefore both get
/// replaced, exactly as before this function was rewritten. Narrowing that to
/// `replacement`'s own sort was considered and rejected: it would risk a new
/// *under*-substitution whenever the replacement's sort differs benignly from
/// the variable's (`Int` versus `Real`), and under-substitution is the failure
/// mode this rewrite exists to eliminate.
///
/// The free-variable query is deliberately the pattern-aware
/// [`TermManager::free_vars_including_patterns`]: a variable occurring only in
/// a quantifier's trigger is still a live occurrence, and the retired walk did
/// substitute into patterns, so skipping them here would under-substitute.
pub fn substitute_single_var(
    manager: &mut TermManager,
    term_id: TermId,
    var_name: Spur,
    replacement: TermId,
) -> TermId {
    let targets: FxHashMap<TermId, TermId> = manager
        .free_vars_including_patterns(term_id)
        .into_iter()
        .filter(|&var| {
            matches!(
                manager.get(var).map(|t| &t.kind),
                Some(TermKind::Var(name)) if *name == var_name
            )
        })
        .map(|var| (var, replacement))
        .collect();

    // Nothing named `var_name` occurs free (it is absent, or every occurrence
    // is shadowed by an inner binder of the same name): the term is already
    // its own substitution instance.
    if targets.is_empty() {
        return term_id;
    }

    manager.substitute(term_id, &targets)
}
