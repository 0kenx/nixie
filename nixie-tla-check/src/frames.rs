//! Per-step candidate **universes** for set-valued state variables (issue #20).
//!
//! # The problem
//!
//! A set-valued `VARIABLE` encodes to one opaque set-sorted SMT variable per
//! step. The set theory reasons about it exactly – membership, union,
//! equality – but a **bounded quantifier** over it has nothing to instantiate
//! with: the encoder needs a candidate list, and an opaque variable has none.
//! That single gap is the corpus's largest blocker class.
//!
//! # The frame idea
//!
//! Apalache solves this with arena cells whose element lists are padded and
//! chosen by oracle constraints. Per this repository's design note, we keep
//! the native set theory and instead derive a candidate **universe** per
//! set-valued variable:
//!
//! * `U_v` starts as the elements of the value `Init` assigns (or the set an
//!   `v \in S` initial conjunct names).
//! * every assignment `v' = rhs` in `Next` contributes the elements of
//!   `rhs` – where reading a set-valued variable yields *its* universe, so
//!   `v' = v \ {t}` inherits and `v' = v \cup {..}` extends it; and
//!   existential binders over enumerable domains are instantiated per
//!   candidate, so `\E t \in v : v' = v \ {t}` stays inside `U_v`.
//! * the assignment set is iterated to a fixpoint (or the candidate budget,
//!   whichever comes first) and a variable whose fixpoint does not exist is
//!   simply **not framed** – it keeps today's honest refusal.
//!
//! # Why that is sound
//!
//! Membership is never taken on faith: a frame candidate is offered to the
//! solver guarded by `candidate \in v@k` on the **real** variable term, so an
//! over-approximate universe changes nothing about which behaviours exist.
//! What the universe must guarantee is the *other* direction – that no member
//! of `v@k` is missing – because a `\A x \in v` instantiated over a universe
//! that misses a member would skip it. The fixpoint guarantees it by
//! induction: `v@0`'s elements are `Init`'s assignment's elements, and every
//! `rhs`'s elements are in `U_v` by construction, so `v@k \subseteq U_v`
//! along every behaviour the transition allows. [`crate::bmc`] carries the
//! belt-and-suspenders form of that argument behind a paranoid flag: ask the
//! solver directly whether `Init /\ Trans_{<k} /\ ~(v@k \subseteq U_v)` is
//! satisfiable, and fail closed if it is.
//!
//! The walk is explicit-stack throughout: a lowered transition is
//! user-controlled input and this pass must not grow the native stack.

use std::collections::HashMap;
use std::rc::Rc;

use nixie_tla::kera::{Kera, KeraRef};
use nixie_tla::lower::subst_term;

/// The analysis result: for each framable set-valued variable, its candidate
/// universe as kernel terms (state reads left symbolic – the solver ties
/// them; only *binder* variables are instantiated, and only over enumerable
/// domains).
#[derive(Debug, Default, Clone)]
pub struct Frames {
    /// One universe per variable name, in derivation order (deduplicated by
    /// term identity).
    pub universe: HashMap<String, Vec<KeraRef>>,
    /// Candidate **key** universes for the `DOMAIN` of function-valued state
    /// variables (issue #20, step 5): `b' = [x \in S |-> e]` contributes
    /// `elements(S)`, `b' = [b EXCEPT ![k] = v]` contributes the inherited
    /// keys plus `k`, `b' \in [S -> T]` contributes `elements(S)`. A
    /// bounded quantifier over `DOMAIN b` then instantiates over these,
    /// guarded by membership in the **real** domain term – the same
    /// solver-mediated presence the set frames use.
    pub fun_universe: HashMap<String, Vec<KeraRef>>,
}

/// Why a variable could not be framed. Not an error – an unframed variable
/// keeps the previous behaviour, and the decline it produced.
#[derive(Debug, Clone, PartialEq, Eq)]
enum NoFrame {
    /// The universe outgrew the candidate budget.
    TooMany(usize),
}

/// The analysis input.
pub struct Input<'a> {
    /// The lowered `Init`.
    pub init: &'a KeraRef,
    /// The lowered (and skolemized) `Next`.
    pub next: &'a KeraRef,
    /// The set-valued state variables, by name.
    pub set_vars: Vec<String>,
    /// The function-valued state variables, by name – the subjects of the
    /// domain-key universes.
    pub fun_vars: Vec<String>,
    /// The candidate budget, the same ceiling the arena respects.
    pub max_candidates: usize,
}

/// Derive the frames, or the empty set where a variable cannot be framed.
#[must_use]
pub fn analyze(input: &Input<'_>) -> Frames {
    let mut state: HashMap<String, Result<Vec<KeraRef>, NoFrame>> = HashMap::new();
    for v in &input.set_vars {
        state.insert(v.clone(), Ok(Vec::new()));
    }
    for v in &input.fun_vars {
        state.entry(v.clone()).or_insert_with(|| Ok(Vec::new()));
    }
    // Which extractor an assignment's right-hand side gets: a set variable
    // contributes its elements, a function variable the keys of its domain.
    let fun_set: std::collections::HashSet<String> = input.fun_vars.iter().cloned().collect();
    let kinds = |v: &str| {
        if fun_set.contains(v) {
            VarKind::Fun
        } else {
            VarKind::Set
        }
    };
    // The initial assignment's elements seed every universe – into the same
    // map the element walk reads, so a transition's `v' = v \cup {..}`
    // inherits them. An `Init` that never mentions a set variable leaves it
    // at the empty universe, which is a frame – a weak one, grown by the
    // transition's assignments.
    let mut seeded = HashMap::new();
    collect_assignments(
        input.init,
        false,
        &state,
        &kinds,
        &mut seeded,
        input.max_candidates,
    );
    merge_into(&mut state, seeded, input.max_candidates);
    // Iterate the transition's assignments to a fixpoint. Termination: each
    // round only adds candidates, and a universe past the budget poisons its
    // variable for good.
    let rounds = input
        .set_vars
        .len()
        .saturating_mul(2)
        .saturating_add(input.fun_vars.len().saturating_mul(2))
        .saturating_add(2);
    for _ in 0..rounds {
        let mut grown = HashMap::new();
        collect_assignments(
            input.next,
            true,
            &state,
            &kinds,
            &mut grown,
            input.max_candidates,
        );
        if !merge_into(&mut state, grown, input.max_candidates) {
            break;
        }
    }
    let mut universes: HashMap<String, Vec<KeraRef>> = HashMap::new();
    let mut fun_universes: HashMap<String, Vec<KeraRef>> = HashMap::new();
    for (v, u) in state {
        if let Ok(elems) = u
            && !elems.is_empty()
        {
            if fun_set.contains(v.as_str()) {
                fun_universes.insert(v, elems);
            } else {
                universes.insert(v, elems);
            }
        }
    }
    // An empty universe is dropped: the walk cannot distinguish "empty" from
    // "unmentioned", and the conservative reading leaves the variable
    // unframed, declining as before.
    Frames {
        universe: universes,
        fun_universe: fun_universes,
    }
}

/// How a variable's assignment sites are read: the elements of the assigned
/// set, or the keys of the assigned function's domain.
#[derive(Clone, Copy, PartialEq, Eq)]
enum VarKind {
    Set,
    Fun,
}

/// Merge one round's collected candidates into the fixpoint state. `false`
/// when nothing changed – the fixpoint is reached.
fn merge_into(
    state: &mut HashMap<String, Result<Vec<KeraRef>, NoFrame>>,
    grown: HashMap<String, Vec<KeraRef>>,
    max_candidates: usize,
) -> bool {
    let mut changed = false;
    for (v, elems) in grown {
        if let Ok(cur) = state.entry(v.clone()).or_insert_with(|| Ok(Vec::new())) {
            // Deduplicated by value (`normalize_elements`'s key), not by
            // pointer: a round's inherited candidates come back as fresh
            // `Rc`s of values already present, and pointer identity would
            // grow the universe with value-duplicates until the budget
            // poisons a variable whose true universe is small.
            let mut seen: std::collections::HashSet<String> =
                cur.iter().map(|e| format!("{e:?}")).collect();
            let mut poisoned = false;
            for e in elems {
                let e = eval_literal(&e).unwrap_or(e);
                if !seen.insert(format!("{e:?}")) {
                    continue;
                }
                if cur.len() >= max_candidates {
                    poisoned = true;
                    break;
                }
                cur.push(e);
                changed = true;
            }
            if poisoned {
                state.insert(v, Err(NoFrame::TooMany(max_candidates)));
            }
        }
    }
    changed
}

/// Ground-evaluate one element to its literal, when it evaluates.
fn eval_literal(e: &KeraRef) -> Option<KeraRef> {
    let v = nixie_tla::Evaluator::new().eval(e).ok()?;
    value_literal(&v)
}

/// Walk a formula's conjunct/disjunct structure, instantiating enumerable
/// existential binders, and collect every set-variable assignment's element
/// terms into `out`.
fn collect_assignments(
    t: &KeraRef,
    next_state: bool,
    state: &HashMap<String, Result<Vec<KeraRef>, NoFrame>>,
    kinds: &dyn Fn(&str) -> VarKind,
    out: &mut HashMap<String, Vec<KeraRef>>,
    max_candidates: usize,
) {
    let mut work: Vec<&KeraRef> = vec![t];
    while let Some(cur) = work.pop() {
        match cur.as_ref() {
            Kera::And(xs) | Kera::Or(xs) => work.extend(xs.iter()),
            // An enumerable binder is instantiated per candidate: each
            // candidate's body is a behaviour the quantifier admits, so its
            // assignments are assignment sites. A binder over a domain with
            // no enumerable reading is left alone – its body is still walked
            // structurally, and any assignment under it that does not depend
            // on the binder is still collected (the symbolic reads stay
            // symbolic; presence is solver-mediated either way).
            Kera::Exists { var, set, body } | Kera::Forall { var, set, body } => {
                match elements(set, state, max_candidates) {
                    Some(dom) if dom.len() <= max_candidates => {
                        for d in dom {
                            let instantiated = subst_term(body, var, &d);
                            collect_assignments(
                                &instantiated,
                                next_state,
                                state,
                                kinds,
                                out,
                                max_candidates,
                            );
                        }
                    }
                    _ => work.push(body),
                }
            }
            // Both branches of an `IF` are behaviours; their assignments are
            // collected unconditionally, which only ever over-approximates
            // the universe – the guards are the solver's business.
            Kera::Ite(_, a, b) => {
                work.push(a);
                work.push(b);
            }
            Kera::Eq(lhs, rhs) => {
                collect_eq(lhs, rhs, next_state, state, kinds, out, max_candidates);
                collect_eq(rhs, lhs, next_state, state, kinds, out, max_candidates);
            }
            Kera::In(member, set) => {
                // The nondeterministic assignment shape `v' \in S` (in an
                // action) or `v \in S` (in `Init`): the candidates are the
                // domain's elements – for a function variable over
                // `[S -> T]`, the keys are `S`'s elements (the `\in`
                // `[S -> T]` encoding pins the domain to exactly `S`).
                if let Some(v) = primed_or_plain_var(member, next_state) {
                    let rhs = match (kinds(&v), set.as_ref()) {
                        (VarKind::Fun, Kera::FunSet { set: inner, .. }) => inner,
                        _ => set,
                    };
                    offer(&v, rhs, state, kinds, out, max_candidates);
                }
            }
            _ => {}
        }
    }
}

/// One side of an `=` is a (possibly primed, possibly tuple-decomposed)
/// variable and the other its assigned value.
fn collect_eq(
    lhs: &KeraRef,
    rhs: &KeraRef,
    next_state: bool,
    state: &HashMap<String, Result<Vec<KeraRef>, NoFrame>>,
    kinds: &dyn Fn(&str) -> VarKind,
    out: &mut HashMap<String, Vec<KeraRef>>,
    max_candidates: usize,
) {
    let Some(vs) = assigned_vars(lhs, next_state) else {
        return;
    };
    match vs.as_slice() {
        [(v, None)] => offer(v, rhs, state, kinds, out, max_candidates),
        // A tuple assignment `<<a', b'>> = <<e1, e2>>`: elementwise, when
        // the right side is a tuple of the same arity.
        _ => {
            if let Kera::Tuple(items) = rhs.as_ref()
                && items.len() == vs.len()
            {
                for ((v, _), item) in vs.iter().zip(items.iter()) {
                    offer(v, item, state, kinds, out, max_candidates);
                }
            }
        }
    }
}

/// The variables an `=` left-hand side assigns, with their position in a
/// tuple decomposition (`None` for a plain `v' = ..`).
fn assigned_vars(lhs: &KeraRef, next_state: bool) -> Option<Vec<(String, Option<usize>)>> {
    match lhs.as_ref() {
        Kera::Prime(inner) => match inner.as_ref() {
            Kera::Var(n) => Some(vec![(n.to_string(), None)]),
            Kera::Tuple(items) => {
                let mut out = Vec::with_capacity(items.len());
                for (i, it) in items.iter().enumerate() {
                    if let Kera::Prime(inner2) = it.as_ref()
                        && let Kera::Var(n) = inner2.as_ref()
                    {
                        out.push((n.to_string(), Some(i)));
                    } else {
                        return None;
                    }
                }
                Some(out)
            }
            _ => None,
        },
        // In `Init` there is no prime; a bare variable name on the left of
        // `=` is the assignment.
        Kera::Var(n) if !next_state => Some(vec![(n.to_string(), None)]),
        _ => None,
    }
}

/// The variable a (primed, in an action; plain, in `Init`) term is, when it
/// is one.
fn primed_or_plain_var(t: &KeraRef, next_state: bool) -> Option<String> {
    match t.as_ref() {
        Kera::Prime(inner) if next_state => match inner.as_ref() {
            Kera::Var(n) => Some(n.to_string()),
            _ => None,
        },
        Kera::Var(n) if !next_state => Some(n.to_string()),
        _ => None,
    }
}

/// Add the elements of `rhs` to variable `v`'s collected candidates.
fn offer(
    v: &str,
    rhs: &KeraRef,
    state: &HashMap<String, Result<Vec<KeraRef>, NoFrame>>,
    kinds: &dyn Fn(&str) -> VarKind,
    out: &mut HashMap<String, Vec<KeraRef>>,
    max_candidates: usize,
) {
    // Only framed state variables have universes.
    if !state.contains_key(v) {
        return;
    }
    let elems = match kinds(v) {
        VarKind::Set => elements(rhs, state, max_candidates),
        VarKind::Fun => dom_keys(rhs, state, max_candidates),
    };
    if let Some(elems) = elems {
        let cur = out.entry(v.to_string()).or_default();
        for e in elems {
            if !cur.iter().any(|c| Rc::ptr_eq(c, &e)) {
                cur.push(e);
            }
        }
    }
}

/// The candidate elements of a set-valued kernel term, or `None` when the
/// term has no enumerable reading.
///
/// Over-approximations are sound in one direction only – the universe may
/// offer candidates that are not members (presence is solver-mediated), so
/// an intersection keeps one side's candidates and a filter keeps its base's.
/// What it may never do is *miss* an element, which is why a shape without a
/// certain superset reading is `None`, and the variable stays unframed.
fn elements(
    t: &KeraRef,
    state: &HashMap<String, Result<Vec<KeraRef>, NoFrame>>,
    max_candidates: usize,
) -> Option<Vec<KeraRef>> {
    let mut out: Vec<KeraRef> = Vec::new();
    let mut work: Vec<&KeraRef> = vec![t];
    while let Some(cur) = work.pop() {
        match cur.as_ref() {
            Kera::SetEnum(xs) => out.extend(xs.iter().map(Rc::clone)),
            Kera::SetBin(op, a, b) => {
                use nixie_tla::kera::SetOp;
                match op {
                    SetOp::Union => {
                        work.push(a);
                        work.push(b);
                    }
                    // `a \cap b \subseteq a` and `a \ b \subseteq a`: the
                    // left side's candidates cover the result.
                    SetOp::Intersect | SetOp::Difference => work.push(a),
                }
            }
            // A set-valued variable read: its own universe (a variable whose
            // universe is not (yet) derivable offers none, which propagates
            // the refusal honestly).
            Kera::Var(n) => match state.get(n.as_str()) {
                Some(Ok(u)) => out.extend(u.iter().map(Rc::clone)),
                _ => return None,
            },
            // `DOMAIN f` in a set position: the function's domain keys –
            // the same extractor a function variable's assignment uses, so
            // `v' = v \cup DOMAIN b` and `b' = [x \in DOMAIN b |-> ..]`
            // read one table.
            Kera::Domain(f) => {
                let keys = dom_keys(f, state, max_candidates)?;
                out.extend(keys);
            }
            // A filter keeps a subset of its base; the base's candidates
            // cover it.
            Kera::Filter { set, .. } => work.push(set),
            // A variant filter (issue #17) keeps the payloads of one tag.
            // The binder it feeds ranges over **payloads**, so each
            // **same-tag** base candidate is wrapped in the tag's getter –
            // the kernel term for `VariantGetUnsafe(tag, candidate)`, which
            // the encoder reads through the datatype selector exactly as a
            // filtered member would be. Wrapping a wrong-tag candidate
            // instead would type the getter's payload as a fresh open
            // record – the merged row then carries a payload `sort_of`
            // refuses, and the frame dies at its own over-approximation.
            // The tag a `Variant` candidate carries is exactly the tag the
            // filter keeps, so selecting on it is exact, not a guess.
            Kera::VariantFilter { tag, set } => {
                let base = elements(set, state, max_candidates)?;
                if base.len() > max_candidates {
                    return None;
                }
                for b in base {
                    if let Kera::Variant { tag: t, .. } = b.as_ref()
                        && t == tag
                    {
                        out.push(
                            Kera::VariantGet {
                                tag: tag.clone(),
                                value: b,
                                or_else: None,
                            }
                            .rc(),
                        );
                    }
                }
            }
            // A map's elements are the mapped body per candidate of the
            // domain – instantiated, so the body's reads become concrete
            // where the binder made them symbolic.
            Kera::Map { var, set, expr } => {
                let dom = elements(set, state, max_candidates)?;
                if dom.len() > max_candidates {
                    return None;
                }
                for d in dom {
                    out.push(subst_term(expr, var, &d));
                }
            }
            // A ground range: enumerated. The evaluator gives the value; the
            // elements return as integer terms.
            Kera::Range(..) => {
                let r = nixie_tla::Evaluator::new()
                    .eval(cur)
                    .ok()
                    .and_then(|v| match v {
                        nixie_tla::Value::Set(s) => Some(s),
                        _ => None,
                    })?;
                if r.len() > max_candidates {
                    return None;
                }
                for v in r {
                    if let nixie_tla::Value::Int(i) = v {
                        out.push(Kera::Int(i.to_string()).rc());
                    } else {
                        return None;
                    }
                }
            }
            // Anything else – a function set, a powerset, a flattened union,
            // an opaque operator – has no certain-superset reading here.
            _ => return None,
        }
        if out.len() > max_candidates {
            return None;
        }
    }
    Some(normalize_elements(out))
}

/// Ground and deduplicate a candidate list.
///
/// An arithmetic element like `1 + 1` collected under an instantiated binder
/// is a *term* distinct from the literal `2` it equals, and pointer
/// deduplication keeps both – the fixpoint then grows a universe of
/// syntactically-distinct, value-identical candidates (`(1+1)+1` beside
/// `2+1`), which the solver pays for at every membership. Evaluating what
/// evaluates collapses them to their literals; what stays symbolic stays a
/// term. Deduplicated by value, so the universe counts *values*, not
/// spellings.
fn normalize_elements(elems: Vec<KeraRef>) -> Vec<KeraRef> {
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut out = Vec::with_capacity(elems.len());
    let mut eval = nixie_tla::Evaluator::new();
    for e in elems {
        let e = match eval.eval(&e) {
            Ok(v) => match value_literal(&v) {
                Some(k) => k,
                None => e,
            },
            Err(_) => e,
        };
        let key = format!("{e:?}");
        if seen.insert(key) {
            out.push(e);
        }
    }
    out
}

/// The kernel literal for a ground value, when it has one.
fn value_literal(v: &nixie_tla::Value) -> Option<KeraRef> {
    match v {
        nixie_tla::Value::Int(i) => Some(Kera::Int(i.to_string()).rc()),
        nixie_tla::Value::Str(s) => Some(Kera::Str(s.clone()).rc()),
        nixie_tla::Value::Bool(b) => Some(Kera::Bool(*b).rc()),
        _ => None,
    }
}

/// The names a frame universe is keyed by, for diagnostics.
#[must_use]
pub fn framed_vars(frames: &Frames) -> Vec<String> {
    let mut out: Vec<String> = frames.universe.keys().cloned().collect();
    out.sort();
    out
}

/// The candidate **domain keys** of a function-valued kernel term, or `None`
/// when the term's domain has no enumerable reading (issue #20, step 5).
///
/// The same one-directional contract as [`elements`]: the keys offered may
/// over-approximate the true domain (presence is solver-mediated, guarded by
/// membership in the real domain term), but may never miss one – which is
/// why an unreadable shape is `None` and the variable stays unframed.
fn dom_keys(
    t: &KeraRef,
    state: &HashMap<String, Result<Vec<KeraRef>, NoFrame>>,
    max_candidates: usize,
) -> Option<Vec<KeraRef>> {
    let mut out: Vec<KeraRef> = Vec::new();
    let mut work: Vec<&KeraRef> = vec![t];
    while let Some(cur) = work.pop() {
        match cur.as_ref() {
            // `[x \in S |-> e]` (and a recursive function over `S`): the
            // domain is exactly `S`.
            Kera::FunDef { set, .. } | Kera::RecFun { set, .. } => {
                let dom = elements(set, state, max_candidates)?;
                out.extend(dom);
            }
            // `f \in [S -> T]` pins the domain to exactly `S`.
            Kera::FunSet { set, .. } => {
                let dom = elements(set, state, max_candidates)?;
                out.extend(dom);
            }
            // `[f EXCEPT ![k] = v]`: the domain inherits `f`'s keys and adds
            // `k` (a store extends, never shrinks).
            Kera::Except { fun, index, .. } => {
                let base = dom_keys(fun, state, max_candidates)?;
                out.extend(base);
                out.push(Rc::clone(index));
            }
            // A function-valued variable read: its own key universe.
            Kera::Var(n) => match state.get(n.as_str()) {
                Some(Ok(u)) => out.extend(u.iter().map(Rc::clone)),
                _ => return None,
            },
            // `DOMAIN (DOMAIN f)` is not a TLA+ shape a function value has;
            // reading the inner function's keys directly would be wrong in
            // the missing-key direction. Refused.
            Kera::Domain(_) => return None,
            // A record literal: its domain is its field names.
            Kera::Record(fields) => {
                for (k, _) in fields {
                    out.push(Kera::Str(k.clone()).rc());
                }
            }
            // A tuple literal: its domain is `1..n`.
            Kera::Tuple(xs) => {
                for i in 1..=xs.len() {
                    out.push(Kera::Int(i.to_string()).rc());
                }
            }
            // Both branches of a conditional function.
            Kera::Ite(_, a, b) => {
                work.push(a);
                work.push(b);
            }
            _ => return None,
        }
        if out.len() > max_candidates {
            return None;
        }
    }
    Some(out)
}
