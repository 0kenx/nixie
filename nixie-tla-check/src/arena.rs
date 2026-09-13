//! The arena: how a TLA+ set reaches a solver that has no set theory.
//!
//! # Why this shape
//!
//! `nixie-theories::set` exists but is not a CDCL(T) theory — there is no
//! `SortKind::Set`, no set term kinds and no Nelson-Oppen dispatch, so nothing
//! a `TermManager` can build reaches it (see
//! `docs/studies/2026-09-13-set-theory-not-reachable-from-solver.md`). SMT
//! arrays are no help either: they have no union, no intersection and no
//! cardinality, so every set operation would need a quantifier or a pointwise
//! expansion over a candidate list.
//!
//! Apalache's answer, ported here, is that **if you are computing a candidate
//! list anyway, compute it exactly**. Every set is represented by a finite
//! list of *candidate members*, each carrying a Boolean term saying whether it
//! is actually in the set. Set operations become propositional structure over
//! those Booleans, and nothing but `Bool`, `Int` and equality ever reaches the
//! solver.
//!
//! ```text
//! {1, 2, 3}          members [1, 2, 3],  present [TRUE, TRUE, TRUE]
//! {x \in S : P(x)}   members of S,       present [in_i /\ P(m_i)]
//! A \cup B           members of both,    present [in_A_i] ++ [in_B_j]
//! x \in S            \/_i (in_i /\ x = m_i)
//! ```
//!
//! # Why tuples and records are structural too
//!
//! They live in the same `Value` enum and are taken apart by the encoder
//! before anything reaches the solver. The reason is TLA+'s, not a
//! convenience: `<<1, "a">>` is a perfectly ordinary tuple, and an SMT array
//! forces one sort across every index, so an array-backed tuple could only
//! ever be homogeneous. A record has the same problem with knobs on, since its
//! fields are named rather than numbered.
//!
//! Making them structural also makes `DOMAIN` exact where an array cannot be:
//! a tuple's domain is `1..n` and a record's is its field names, both of which
//! are known here. For an array-backed function the domain is not represented
//! at all, and `DOMAIN` on one is refused rather than answered with something
//! plausible.
//!
//! # The one thing to be careful about
//!
//! Candidate members are **not** distinct. `{x, y}` has two candidates that
//! may be the same value, and `A \cup B` concatenates two lists that may
//! overlap. Membership and quantification do not care — a duplicate just
//! satisfies the disjunct twice. **Cardinality does**, and counting candidates
//! would over-count `Cardinality({x, y})` as 2 when `x = y`. So a candidate is
//! counted only when no *earlier* candidate is present and equal to it, which
//! is the standard de-duplicating sum and the reason cardinality is not simply
//! a sum of indicator variables.

use nixie_core::{TermId, TermManager};
use std::collections::BTreeMap;
use std::rc::Rc;

/// A TLA+ value as the encoder represents it.
///
/// Only [`Value::Scalar`] has an SMT sort. The others are *structural*: they
/// exist in the encoder and are taken apart before anything reaches the
/// solver, which is what lets TLA+'s heterogeneous tuples and records be
/// encoded at all — an SMT array would force every component to one sort.
#[derive(Debug, Clone)]
pub enum Value {
    /// Anything with an SMT sort of its own: `Int`, `Bool`, `Str`, an
    /// uninterpreted constant, or an array standing for a function.
    Scalar(TermId),
    /// A finite set, as a list of candidates.
    Set(SetCell),
    /// A tuple, component by component.
    ///
    /// In TLA+ a tuple *is* a function on `1..n`, so `t[i]` for a literal `i`
    /// selects a component. Components may have different types, which is why
    /// this is structural rather than an array.
    Tuple(Vec<Rc<Value>>),
    /// A record, field by field.
    ///
    /// A record is a function on its field names, so `r.f` and `r["f"]` are
    /// the same operation and both land here. Sorted by name, so two records
    /// written in a different order compare equal.
    Record(BTreeMap<String, Rc<Value>>),
}

/// A set, represented by the values it might contain.
#[derive(Debug, Clone, Default)]
pub struct SetCell {
    /// The candidates, in the order they were introduced.
    ///
    /// Deliberately a list and not a set: two candidates may denote the same
    /// value, and which ones do is generally not decidable here.
    pub members: Vec<Member>,
}

/// One candidate member of a set.
#[derive(Debug, Clone)]
pub struct Member {
    /// What the candidate is.
    pub value: Rc<Value>,
    /// A Boolean term: is it in the set?
    pub present: TermId,
}

impl SetCell {
    /// The empty set: no candidates at all, so every membership test is
    /// `FALSE` by construction rather than by an axiom.
    #[must_use]
    pub fn empty() -> Self {
        Self {
            members: Vec::new(),
        }
    }

    /// How many candidates this set carries.
    ///
    /// The encoding's size is driven by this, not by the set's actual
    /// cardinality, which is not known until the solver runs.
    #[must_use]
    pub fn candidates(&self) -> usize {
        self.members.len()
    }
}

/// Structural equality of two values, as a Boolean term.
///
/// For sets this is **extensionality**, the only definition TLA+ has: two sets
/// are equal when each contains every member of the other. Comparing candidate
/// lists instead would make `{1, 1}` differ from `{1}`, and `{x} \cup {y}`
/// differ from `{x}` when `x = y`.
///
/// # Errors
///
/// Returns `None` when the two values have different shapes. That is a type
/// error the inferencer should already have caught, so it is reported rather
/// than papered over with `FALSE` — a silent `FALSE` here would make a genuine
/// equality unsatisfiable and could hide a counterexample.
pub fn eq_values(a: &Value, b: &Value, tm: &mut TermManager) -> Option<TermId> {
    match (a, b) {
        (Value::Scalar(x), Value::Scalar(y)) => Some(tm.mk_eq(*x, *y)),
        (Value::Set(s), Value::Set(t)) => {
            let fwd = subset_of(s, t, tm)?;
            let bwd = subset_of(t, s, tm)?;
            Some(tm.mk_and([fwd, bwd]))
        }
        // Componentwise, and a length mismatch is `FALSE` rather than a shape
        // error: two tuples of different arity are both tuples and TLA+ says
        // they are simply not equal.
        (Value::Tuple(xs), Value::Tuple(ys)) => {
            if xs.len() != ys.len() {
                return Some(tm.mk_bool(false));
            }
            let mut conj = Vec::with_capacity(xs.len());
            for (x, y) in xs.iter().zip(ys.iter()) {
                conj.push(eq_values(x, y, tm)?);
            }
            Some(tm.mk_and(conj))
        }
        // Likewise: records with different field sets are different values,
        // not a type error to report.
        (Value::Record(xs), Value::Record(ys)) => {
            if xs.len() != ys.len() || xs.keys().ne(ys.keys()) {
                return Some(tm.mk_bool(false));
            }
            let mut conj = Vec::with_capacity(xs.len());
            for (x, y) in xs.values().zip(ys.values()) {
                conj.push(eq_values(x, y, tm)?);
            }
            Some(tm.mk_and(conj))
        }
        _ => None,
    }
}

/// `s \subseteq t`, as a Boolean term.
///
/// # Errors
///
/// `None` if a member's shape does not match, as [`eq_values`].
pub fn subset_of(s: &SetCell, t: &SetCell, tm: &mut TermManager) -> Option<TermId> {
    let mut conj = Vec::with_capacity(s.members.len());
    for m in &s.members {
        let inside = member_of(&m.value, t, tm)?;
        // `present => inside`, i.e. every candidate that really is in `s` is
        // also in `t`. A candidate that is not present constrains nothing.
        let not_present = tm.mk_not(m.present);
        conj.push(tm.mk_or([not_present, inside]));
    }
    Some(tm.mk_and(conj))
}

/// `v \in set`, as a Boolean term.
///
/// # Errors
///
/// `None` if a member's shape does not match `v`.
pub fn member_of(v: &Value, set: &SetCell, tm: &mut TermManager) -> Option<TermId> {
    let mut disj = Vec::with_capacity(set.members.len());
    for m in &set.members {
        let same = eq_values(v, &m.value, tm)?;
        disj.push(tm.mk_and([m.present, same]));
    }
    // An empty set yields an empty disjunction, which is `FALSE` — exactly
    // right, and it needs no special case.
    Some(tm.mk_or(disj))
}

/// `Cardinality(set)`, as an integer term.
///
/// Counts a candidate only when it is present **and** no earlier candidate is
/// both present and equal to it. Candidates are not distinct — `{x, y}` has
/// two of them and they may denote one value — so a plain sum of indicators
/// would report `Cardinality({x, y}) = 2` even when `x = y`.
///
/// # Errors
///
/// `None` if two members have different shapes.
pub fn cardinality(set: &SetCell, tm: &mut TermManager) -> Option<TermId> {
    let zero = tm.mk_int(0);
    let one = tm.mk_int(1);
    let mut terms = Vec::with_capacity(set.members.len());
    for (i, m) in set.members.iter().enumerate() {
        let mut fresh = vec![m.present];
        for earlier in &set.members[..i] {
            let same = eq_values(&m.value, &earlier.value, tm)?;
            let dup = tm.mk_and([earlier.present, same]);
            fresh.push(tm.mk_not(dup));
        }
        let counts = tm.mk_and(fresh);
        terms.push(tm.mk_ite(counts, one, zero));
    }
    if terms.is_empty() {
        return Some(zero);
    }
    Some(tm.mk_add(terms))
}
