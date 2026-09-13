//! Turning inferred TLA+ types into SMT sorts.
//!
//! `nixie-tla`'s inferencer says what shape a name has; this says what the
//! solver should call it. The two are deliberately separate: inference is
//! about TLA+, and a type it cannot encode yet is still a correct type.
//!
//! # What is mapped, and what is not
//!
//! The scalar types map directly. Sets, functions, sequences, tuples and
//! records do **not**, and are declined by name rather than approximated —
//! they need the arena encoding described in
//! `docs/studies/2026-09-13-set-theory-not-reachable-from-solver.md`, which is
//! the next slice of milestone 3.
//!
//! A type variable inference never constrained becomes an **uninterpreted
//! sort**, not a guess at a concrete one. That is the honest reading: the
//! specification says the values of this name are only ever compared for
//! equality, which is exactly what an uninterpreted sort means. The gradual
//! typing literature would call this `any` and insert a runtime cast; there is
//! no runtime here to check one, so the uninterpreted sort is both the
//! faithful and the only sound choice.

use nixie_core::{SortId, TermManager};
use nixie_tla::Type;

/// Why a type has no SMT sort yet.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("{0} has no SMT sort yet")]
pub struct NoSort(pub String);

/// The SMT sort for an inferred TLA+ type.
///
/// # Errors
///
/// Returns the shape it cannot map, by name. Never substitutes a different
/// sort: a state variable encoded at the wrong sort is a wrong answer, not a
/// missing feature.
pub fn sort_of(ty: &Type, tm: &mut TermManager) -> Result<SortId, NoSort> {
    match ty {
        Type::Bool => Ok(tm.sorts.bool_sort),
        Type::Int => Ok(tm.sorts.int_sort),
        Type::Str => Ok(tm.sorts.string_sort()),
        // An unconstrained type variable is a value the specification only ever
        // compares for equality. That is an uninterpreted sort, exactly.
        Type::Var(n) => {
            let spur = tm.intern_str(&format!("TlaOpaque{n}"));
            Ok(tm.sorts.intern(nixie_core::SortKind::Uninterpreted(spur)))
        }
        Type::Set(_) => Err(NoSort("a set".into())),
        Type::Seq(_) => Err(NoSort("a sequence".into())),
        // A TLA+ function maps onto an SMT array, which is a theory the solver
        // already has. What an array does **not** carry is the domain, and
        // that shows up in two places. Both err in the same direction, which
        // is the one that matters:
        //
        // * `f[x]` outside `DOMAIN f` is *undefined* in TLA+ and gets some
        //   value from the array, admitting behaviours the specification does
        //   not have.
        // * TLA+ function equality compares domains and the values on them;
        //   SMT array equality compares every index. Array equality is
        //   therefore **stricter**. In a positive position that costs nothing —
        //   the out-of-domain entries are free variables, so the solver picks
        //   witnesses that agree — but under a negation it lets two
        //   TLA+-equal functions be told apart.
        //
        // So the encoding can manufacture a counterexample and cannot hide
        // one: `Violation` may be spurious, `NoViolationWithin` stays sound.
        // That is the same asymmetry as a dropped assumption, and it is the
        // right way round. `Encoder::domain_unmodelled` surfaces it.
        Type::Fun(d, r) => {
            let dom = sort_of(d, tm)?;
            let rng = sort_of(r, tm)?;
            Ok(tm.sorts.array(dom, rng))
        }
        Type::Tuple(_) => Err(NoSort("a tuple".into())),
        Type::Rec { .. } => Err(NoSort("a record".into())),
    }
}
