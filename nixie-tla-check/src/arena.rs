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
//! are known here.
//!
//! # Why a function is a pair
//!
//! A TLA+ function *is* a domain and a graph, and an SMT array is only the
//! graph. [`Value::Fun`] carries both: the graph as an array, so `f[x]` and
//! `[f EXCEPT ![i] = v]` cost a select and a store, and the domain as a
//! set-sorted term, so `DOMAIN f` is exact and equality is domain-relative.
//! Keeping only the array was not merely imprecise — array equality compares
//! every index, so two functions that differ *only* in their domain read as
//! equal, which hides a counterexample rather than manufacturing one.
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

use nixie_core::{SortId, TermId, TermManager};
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
    /// A function: a **domain** and a **graph**, which is what TLA+ says a
    /// function is.
    ///
    /// The graph is an SMT array, so `f[x]` is a select and
    /// `[f EXCEPT ![i] = v]` a store — both free, because the array theory is
    /// already in Nelson-Oppen. The domain is a *set-sorted term*, which is
    /// the part an array alone cannot carry, and carrying it is what makes
    /// `DOMAIN f` exact and equality domain-relative.
    ///
    /// Keeping only the array was not merely imprecise, it was unsound in the
    /// direction that hides a counterexample: `[x \in {1} |-> 0]` and
    /// `[x \in {1, 2} |-> 0]` are different TLA+ functions, and two arrays
    /// that agree at 1 can be made to agree at 2 as well, so array equality
    /// alone reports them equal. See [`eq_values`].
    Fun {
        /// The domain, as a set-sorted SMT term.
        domain: TermId,
        /// The graph, as an SMT array from the domain's element sort.
        array: TermId,
    },
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
        // Domain-relative, the only definition TLA+ has: two functions are
        // equal when they have the same domain and agree on it.
        //
        // The graphs are compared by *array* equality, which also compares
        // points outside the domain. That is stricter than TLA+ in one
        // direction only — it can report two TLA+-equal functions unequal,
        // never two unequal ones equal — so it can manufacture a
        // counterexample and can never hide one. It is *exact* whenever both
        // graphs are built by the encoder, because both store over the same
        // canonical base array and therefore already agree everywhere they do
        // not store; the strictness only bites against a free array, which is
        // what a function-typed state variable's graph is.
        //
        // Conjoining the domains is what closes the hiding direction: without
        // it, `[x \in {1} |-> 0]` and `[x \in {1, 2} |-> 0]` are reported
        // equal whenever the base happens to hold 0 at 2.
        (
            Value::Fun {
                domain: da,
                array: aa,
            },
            Value::Fun {
                domain: db,
                array: ab,
            },
        ) => {
            // `mk_eq` does not check sorts, so two functions with different
            // domain or range sorts would build a well-formed-looking term
            // that no theory can decide. Reported as a shape clash — which is
            // what it is — rather than handed to the solver.
            let sort = |t: &TermId| tm.get(*t).map(|d| d.sort);
            if sort(da) != sort(db) || sort(aa) != sort(ab) {
                return None;
            }
            let same_domain = tm.mk_eq(*da, *db);
            let same_graph = tm.mk_eq(*aa, *ab);
            Some(tm.mk_and([same_domain, same_graph]))
        }
        // A tuple **is** a function on `1..n` — TLA+ has no separate sequence
        // type — so `<<2, 4>>` and `[i \in 1..2 |-> 2 * i]` denote one value.
        // The evaluator normalises the two into one representation; the
        // encoder cannot, because a function-typed state variable has no
        // candidate list to turn into a tuple. So the crossing is done here,
        // by the same definition: same domain, and equal at every index.
        (Value::Tuple(xs), Value::Fun { domain, array })
        | (Value::Fun { domain, array }, Value::Tuple(xs)) => {
            let elem = tm
                .get(*domain)
                .and_then(|d| tm.sorts.get(d.sort))
                .and_then(|s| match s.kind {
                    nixie_core::SortKind::Set(e) => Some(e),
                    _ => None,
                })?;
            // The domain has to be exactly `1..n`, built the way the encoder
            // builds one so the two terms are comparable.
            let set_sort = tm.sorts.set(elem);
            let mut want = tm.mk_set_empty_at(set_sort);
            for i in 1..=xs.len() {
                let k = tm.mk_int(i as i64);
                let single = tm.mk_set_singleton(k);
                want = tm.mk_set_union(want, single);
            }
            let mut conj = vec![tm.mk_eq(*domain, want)];
            for (i, x) in xs.iter().enumerate() {
                let k = tm.mk_int((i + 1) as i64);
                let at = tm.mk_select(*array, k);
                conj.push(eq_values(x, &Value::Scalar(at), tm)?);
            }
            Some(tm.mk_and(conj))
        }
        // A structural tuple or record against the *same value reified* as a
        // datatype term. The encoder keeps the structural form wherever it can
        // — it is what makes a literal index and an exact `DOMAIN` work — so a
        // comparison routinely has one of each: `<<a, b>> \in msgs`, where
        // `msgs` is a set of tuples and its members are datatype terms.
        //
        // Compared field by field through selectors rather than by reifying
        // here, because reifying needs the encoder's sort machinery and this
        // module deliberately holds none of it. A single-constructor datatype
        // has no other shape to be, so taking it apart loses nothing.
        (Value::Tuple(xs), Value::Scalar(t)) | (Value::Scalar(t), Value::Tuple(xs)) => {
            let fields = struct_fields(*t, tm)?;
            if fields.len() != xs.len() {
                return Some(tm.mk_bool(false));
            }
            let mut conj = Vec::with_capacity(xs.len());
            for (x, (f, fs)) in xs.iter().zip(fields.iter()) {
                let at = tm.mk_dt_selector(f, *t, *fs);
                conj.push(eq_values(x, &Value::Scalar(at), tm)?);
            }
            Some(tm.mk_and(conj))
        }
        (Value::Record(xs), Value::Scalar(t)) | (Value::Scalar(t), Value::Record(xs)) => {
            let fields = struct_fields(*t, tm)?;
            if fields.len() != xs.len() {
                return Some(tm.mk_bool(false));
            }
            let mut conj = Vec::with_capacity(xs.len());
            for ((name, x), (f, fs)) in xs.iter().zip(fields.iter()) {
                // The datatype's selectors are the record's fields in the same
                // (sorted) order, so a positional walk is a name walk; a
                // mismatch means these are different record types.
                if *f != format!("@f{name}") {
                    return Some(tm.mk_bool(false));
                }
                let at = tm.mk_dt_selector(f, *t, *fs);
                conj.push(eq_values(x, &Value::Scalar(at), tm)?);
            }
            Some(tm.mk_and(conj))
        }
        // Deliberately enumerated rather than a `_` arm: a new `Value` variant
        // must break compilation here, not fall into a silent shape clash.
        (Value::Scalar(_), _)
        | (Value::Set(_), _)
        | (Value::Tuple(_), _)
        | (Value::Record(_), _)
        | (Value::Fun { .. }, _) => None,
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

/// `IF cond THEN a ELSE b`, at whatever shape the two values have.
///
/// `mk_ite` alone only covers [`Value::Scalar`]. The rest need the conditional
/// pushed *inside* the structure, because a tuple, a record and a set are not
/// single SMT terms — and for a set it is not even a matter of pushing it
/// down: the result's candidate list is the two lists concatenated, each
/// candidate kept under the branch it came from. That is exact, and it is why
/// duplicate candidates have to be tolerated everywhere else (they already
/// are; see [`cardinality`]).
///
/// # Errors
///
/// `None` when the two values have different shapes — a tuple against a
/// record, or two tuples of different lengths. That is a type error the
/// inferencer should have caught, and it is reported rather than resolved:
/// picking one side would answer a question nobody asked.
pub fn ite_values(cond: TermId, a: &Value, b: &Value, tm: &mut TermManager) -> Option<Value> {
    match (a, b) {
        (Value::Scalar(x), Value::Scalar(y)) => Some(Value::Scalar(tm.mk_ite(cond, *x, *y))),
        (
            Value::Fun {
                domain: da,
                array: aa,
            },
            Value::Fun {
                domain: db,
                array: ab,
            },
        ) => Some(Value::Fun {
            domain: tm.mk_ite(cond, *da, *db),
            array: tm.mk_ite(cond, *aa, *ab),
        }),
        (Value::Tuple(xs), Value::Tuple(ys)) if xs.len() == ys.len() => {
            let mut out = Vec::with_capacity(xs.len());
            for (x, y) in xs.iter().zip(ys.iter()) {
                out.push(Rc::new(ite_values(cond, x, y, tm)?));
            }
            Some(Value::Tuple(out))
        }
        (Value::Record(xs), Value::Record(ys)) if xs.len() == ys.len() => {
            let mut out = BTreeMap::new();
            for (k, x) in xs {
                let y = ys.get(k)?;
                out.insert(k.clone(), Rc::new(ite_values(cond, x, y, tm)?));
            }
            Some(Value::Record(out))
        }
        (Value::Set(x), Value::Set(y)) => {
            let neg = tm.mk_not(cond);
            let mut members = Vec::with_capacity(x.members.len() + y.members.len());
            for m in &x.members {
                members.push(Member {
                    value: Rc::clone(&m.value),
                    present: tm.mk_and([cond, m.present]),
                });
            }
            for m in &y.members {
                members.push(Member {
                    value: Rc::clone(&m.value),
                    present: tm.mk_and([neg, m.present]),
                });
            }
            Some(Value::Set(SetCell { members }))
        }
        (
            Value::Scalar(_)
            | Value::Set(_)
            | Value::Tuple(_)
            | Value::Record(_)
            | Value::Fun { .. },
            _,
        ) => None,
    }
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

/// The shared base array every function graph is built on, one per array sort.
///
/// Sharing it is load-bearing rather than a saving. Two functions built with
/// the same domain and the same values must come out **equal**, and array
/// equality compares every index — including the ones neither domain mentions.
/// Storing over a common base makes them agree there by construction; a fresh
/// base per function would leave two identical function literals free to
/// differ, which is a counterexample the specification does not have.
///
/// The base itself is unconstrained, which is the right reading of TLA+'s
/// "`f[x]` outside `DOMAIN f` is undefined": some value, never a chosen one.
#[must_use]
pub fn fun_base(array_sort: SortId, tm: &mut TermManager) -> TermId {
    tm.mk_var(&format!("@tla_fun_base_{}", array_sort.0), array_sort)
}

/// A function with a *known* graph: every pair present, no guards.
///
/// This is the literal form — what a concrete function value looks like once
/// the encoder or an evaluator has already worked out each point. The encoder
/// builds conditional graphs of its own for a domain whose membership is not
/// yet decided, but both go over the same [`fun_base`], which is what makes
/// the two comparable.
#[must_use]
pub fn fun_literal(
    pairs: &[(TermId, TermId)],
    domain_sort: SortId,
    range_sort: SortId,
    tm: &mut TermManager,
) -> Value {
    let set_sort = tm.sorts.set(domain_sort);
    let mut domain = tm.mk_set_empty_at(set_sort);
    let array_sort = tm.sorts.array(domain_sort, range_sort);
    let mut array = fun_base(array_sort, tm);
    for (k, v) in pairs {
        let single = tm.mk_set_singleton(*k);
        domain = tm.mk_set_union(domain, single);
        array = tm.mk_store(array, *k, *v);
    }
    Value::Fun { domain, array }
}

/// The selectors of a single-constructor datatype term, in declaration order.
///
/// `None` when the term is not datatype-sorted, which is a shape clash rather
/// than a `FALSE`: comparing a tuple to an integer is a type error the
/// inferencer should have caught, and answering `FALSE` would make a genuine
/// equality unsatisfiable.
fn struct_fields(t: TermId, tm: &TermManager) -> Option<Vec<(String, SortId)>> {
    crate::sorts::struct_fields(tm.get(t)?.sort, tm)
}
