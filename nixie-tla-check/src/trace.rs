//! Reading a counterexample back out of the solver's model.
//!
//! A `Sat` answer to the bounded query *is* a counterexample, and until now
//! the checker threw it away: `Outcome::Violation` carried a step number and
//! nothing else. Two things were wrong with that, and the second is the
//! serious one.
//!
//! The first is that a violation with no trace is unactionable — "`Inv` fails
//! after 2 steps" does not say what the states were.
//!
//! The second is that the claim was never checked. `AGENTS.md` is explicit: *a
//! model you cannot concretely verify yields `Unknown`, never `Sat`*. The path
//! from a TLA+ specification to a verdict runs through lowering, type
//! inference, an encoding and a solver, and every hop but the last is
//! cross-checked against an independent implementation. The verdict itself was
//! taken on trust. Decoding the model and **replaying the trace through
//! `nixie-tla`'s evaluator** closes that: `Init` must hold in the first state,
//! `Next` between each consecutive pair, and the invariant must actually fail
//! in the last one. A counterexample that does not replay is not reported as a
//! violation.
//!
//! # How a value is decoded
//!
//! Sort-directed, and through [`Model::eval`] rather than by reading raw
//! assignments. That matters: the model assigns *variables*, and what a TLA+
//! state variable is worth may take a selector or a select to reach. Asking
//! the model to evaluate `f[i]` gets congruence and the theory's own
//! normalisation for free, where walking the assignment table would not.
//!
//! What is **not** decoded is declined by name, never guessed. An undecodable
//! state is an honest `Unknown`, because a trace that is partly invented
//! cannot be replayed and a violation that cannot be replayed is not one this
//! checker will claim.

use crate::sorts::struct_fields;
use nixie_core::{SortId, SortKind, TermId, TermKind, TermManager};
use nixie_solver::Model;
use nixie_tla::Value;
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// One state of a counterexample: every `VARIABLE`, by name.
///
/// A `HashMap` because it is what `nixie-tla`'s evaluator binds names from;
/// [`Trace`]'s `Display` sorts, so what a reader sees is still deterministic.
pub type State = HashMap<String, Value>;

/// A counterexample: the states a behaviour passes through.
///
/// `states[0]` satisfies `Init`, `states[k]` and `states[k+1]` are related by
/// `Next`, and the invariant fails in the last one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Trace {
    /// The states, in order. Never empty.
    pub states: Vec<State>,
}

impl Trace {
    /// The number of `Next` steps the trace takes.
    #[must_use]
    pub fn steps(&self) -> usize {
        self.states.len().saturating_sub(1)
    }
}

impl std::fmt::Display for Trace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, s) in self.states.iter().enumerate() {
            writeln!(f, "State {i}:")?;
            let mut names: Vec<&String> = s.keys().collect();
            names.sort();
            for name in names {
                if let Some(v) = s.get(name) {
                    writeln!(f, "  /\\ {name} = {v}")?;
                }
            }
        }
        Ok(())
    }
}

/// Why a model could not be read back as a TLA+ value.
///
/// The two are kept apart because they mean different things. **Undecided** is
/// the model declining to pin a value down, which happens whenever the query
/// never asked — and where any value will do, a value may be supplied.
/// **Unsupported** is this decoder having no reading for a shape, which no
/// choice can repair.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum DecodeError {
    /// The model left this term open: nothing in the query constrained it.
    #[error("{0}")]
    Undecided(String),
    /// No reading for this shape.
    #[error("{0}")]
    Unsupported(String),
}

/// Decode the value a term has in `model`, at its own sort.
///
/// `domain` is the companion domain term of a function-sorted name — an SMT
/// array is only a graph, so without it there is nothing to say which points
/// are in the function.
///
/// # Errors
///
/// Names the shape it cannot read. Never substitutes a value: a trace with an
/// invented state would replay as a violation that is not there.
pub fn decode(
    term: TermId,
    domain: Option<TermId>,
    model: &Model,
    tm: &mut TermManager,
) -> Result<Value, DecodeError> {
    let sort = tm
        .get(term)
        .map(|t| t.sort)
        .ok_or_else(|| DecodeError::Unsupported("a term with no sort".into()))?;
    decode_at(term, sort, domain, model, tm, 0)
}

/// How deep a decoded value may nest before the walk gives up.
///
/// A model's values are as deep as the specification's types, which are
/// user-written; bounded so a malformed one cannot spin.
const MAX_DEPTH: usize = 64;

/// How long a decoded sequence may be.
///
/// A model that says a sequence has a billion elements is not describing a
/// state a bounded check reached; it is a value nothing constrained. Refused
/// rather than materialised.
const MAX_SEQ_LEN: usize = 4096;

fn decode_at(
    term: TermId,
    sort: SortId,
    domain: Option<TermId>,
    model: &Model,
    tm: &mut TermManager,
    depth: usize,
) -> Result<Value, DecodeError> {
    if depth > MAX_DEPTH {
        return Err(DecodeError::Unsupported(format!(
            "a value nesting deeper than the limit of {MAX_DEPTH}"
        )));
    }
    let kind = tm
        .sorts
        .get(sort)
        .map(|s| s.kind.clone())
        .ok_or_else(|| DecodeError::Unsupported("a sort that is not registered".into()))?;
    match kind {
        SortKind::Bool => {
            let v = model.eval(term, tm);
            match tm.get(v).map(|t| t.kind.clone()) {
                Some(TermKind::True) => Ok(Value::Bool(true)),
                Some(TermKind::False) => Ok(Value::Bool(false)),
                _ => Err(DecodeError::Undecided(
                    "a Boolean the model did not decide".into(),
                )),
            }
        }
        SortKind::Int => {
            let v = model.eval(term, tm);
            match tm.get(v).map(|t| t.kind.clone()) {
                Some(TermKind::IntConst(n)) => i128::try_from(&n).map(Value::Int).map_err(|_| {
                    DecodeError::Unsupported(format!("the integer {n}, which does not fit i128"))
                }),
                _ => Err(DecodeError::Undecided(
                    "an integer the model did not decide".into(),
                )),
            }
        }
        SortKind::String => {
            let v = model.eval(term, tm);
            match tm.get(v).map(|t| t.kind.clone()) {
                Some(TermKind::StringLit(s)) => Ok(Value::Str(s)),
                _ => Err(DecodeError::Undecided(
                    "a string the model did not decide".into(),
                )),
            }
        }
        // A **sequence** before a record, because a sequence is a datatype
        // too — a length and an array — and `@sl`/`@sf` are reserved so the
        // two cannot be confused. It decodes to a TLA+ tuple, which is what a
        // sequence is.
        SortKind::Datatype(_) if crate::sorts::seq_element(sort, tm).is_some() => {
            let Some(elem) = crate::sorts::seq_element(sort, tm) else {
                return Err(DecodeError::Unsupported(
                    "a sequence with no element sort".into(),
                ));
            };
            let int = tm.sorts.int_sort;
            let arr = tm.sorts.array(int, elem);
            let len_t = tm.mk_dt_selector(crate::sorts::SEQ_LEN, term, int);
            let Value::Int(len) = decode_at(len_t, int, None, model, tm, depth + 1)? else {
                return Err(DecodeError::Undecided("a sequence length".into()));
            };
            // A negative or absurd length is not a sequence. Refused rather
            // than clamped: a trace with a made-up length is a trace of a
            // behaviour the specification does not have.
            let n = usize::try_from(len)
                .ok()
                .filter(|n| *n <= MAX_SEQ_LEN)
                .ok_or_else(|| DecodeError::Unsupported(format!("a sequence of length {len}")))?;
            // Through the window: `s[i]` is `fun[off + i]`, and the offset is
            // what `Tail` moves instead of copying elements.
            let off_t = tm.mk_dt_selector(crate::sorts::SEQ_OFF, term, int);
            let Value::Int(off) = decode_at(off_t, int, None, model, tm, depth + 1)? else {
                return Err(DecodeError::Undecided("a sequence offset".into()));
            };
            let fun = tm.mk_dt_selector(crate::sorts::SEQ_FUN, term, arr);
            let mut items = Vec::with_capacity(n);
            for i in 1..=n {
                let at_i = off
                    .checked_add(i128::try_from(i).map_err(|_| {
                        DecodeError::Unsupported("a sequence index past i128".into())
                    })?)
                    .ok_or_else(|| DecodeError::Unsupported("a sequence index past i128".into()))?;
                let idx = tm.mk_int(num_bigint::BigInt::from(at_i));
                let at = tm.mk_select(fun, idx);
                items.push(decode_at(at, elem, None, model, tm, depth + 1)?);
            }
            Ok(Value::Tuple(items))
        }
        // A tuple or a record. Which one is told by the selector names, not by
        // the sort: `crate::sorts` prefixes a tuple component `@t` and a record
        // field `@f` precisely so the two cannot be confused.
        SortKind::Datatype(_) => {
            let fields = struct_fields(sort, tm)
                .ok_or_else(|| DecodeError::Unsupported("a datatype with no constructor".into()))?;
            // If the model hands back a *constructor*, read its arguments
            // positionally. That is the case whenever the value came from
            // somewhere the model assigns no selectors for — a record sitting
            // inside a sequence, say, which is reached by reducing a `select`
            // over a `store` chain and so is a term the query never applied a
            // selector to.
            let built = model.eval(term, tm);
            let ctor_args = match tm.get(built).map(|t| t.kind.clone()) {
                Some(TermKind::DtConstructor { args, .. }) if args.len() == fields.len() => {
                    Some(args)
                }
                _ => None,
            };
            let mut parts: Vec<(String, Value)> = Vec::with_capacity(fields.len());
            for (i, (name, fs)) in fields.iter().enumerate() {
                let at = match &ctor_args {
                    Some(args) => *args.get(i).ok_or_else(|| {
                        DecodeError::Unsupported("a constructor with too few arguments".into())
                    })?,
                    None => tm.mk_dt_selector(name, term, *fs),
                };
                parts.push((
                    name.clone(),
                    decode_at(at, *fs, None, model, tm, depth + 1)?,
                ));
            }
            if parts.iter().all(|(n, _)| n.starts_with("@t")) {
                return Ok(Value::Tuple(parts.into_iter().map(|(_, v)| v).collect()));
            }
            let mut out = BTreeMap::new();
            for (n, v) in parts {
                let Some(field) = n.strip_prefix("@f") else {
                    return Err(DecodeError::Unsupported(format!(
                        "a datatype field named `{n}`"
                    )));
                };
                out.insert(field.to_string(), v);
            }
            Ok(Value::Record(out))
        }
        SortKind::Set(elem) => {
            let v = model.eval(term, tm);
            let mut out = BTreeSet::new();
            collect_set(v, elem, model, tm, depth, &mut out)?;
            Ok(Value::Set(out))
        }
        // An SMT array is a graph and nothing else, so the domain has to come
        // from the companion term. Every point of it is selected and decoded;
        // `Value::fun` then normalises a function on `1..n` back to a tuple,
        // which is what TLA+ says a sequence is.
        SortKind::Array { domain: dom, range } => {
            let Some(dterm) = domain else {
                return Err(DecodeError::Unsupported(
                    "a function whose domain was not modelled".into(),
                ));
            };
            let dv = model.eval(dterm, tm);
            let mut points = BTreeSet::new();
            collect_set(dv, dom, model, tm, depth, &mut points)?;
            // What the query decided about the graph is the `select` terms it
            // built, exactly as what it decided about a set is the membership
            // atoms. They are gathered first, because a `select` built here
            // would be a term the model has never seen: `Model::eval` has no
            // case for the array theory, so a fresh one evaluates to itself
            // and every point would look unconstrained.
            let mut graph = BTreeMap::new();
            for (idx_v, at) in selects_of(term, dom, model, tm, depth)? {
                if !points.contains(&idx_v) {
                    continue;
                }
                let value = decode_at(at, range, None, model, tm, depth + 1)?;
                graph.insert(idx_v, value);
            }
            for p in points {
                if graph.contains_key(&p) {
                    continue;
                }
                let idx = encode_index(&p, dom, tm)?;
                let at = tm.mk_select(term, idx);
                // A point the query never selected at is genuinely
                // unconstrained: the formula says nothing about `f[p]`, so
                // *every* value there extends the model. Completing it with
                // the sort's default is what turns a partial model into a
                // whole state — the same thing the solver's own `build_model`
                // does for an unconstrained constant — and it is the only way
                // a function-valued variable becomes a TLA+ value at all,
                // since TLA+ has no partial functions.
                //
                // This is the one place the decoder supplies something the
                // model did not say, and it is safe for a specific reason: the
                // trace is replayed. A completion that was not good enough
                // fails there, and the checker answers `Unknown` instead of
                // reporting a counterexample it cannot stand behind.
                let value = match decode_at(at, range, None, model, tm, depth + 1) {
                    Ok(v) => v,
                    Err(DecodeError::Undecided(why)) => {
                        default_at(range, tm, depth + 1).ok_or(DecodeError::Undecided(why))?
                    }
                    Err(e) => return Err(e),
                };
                graph.insert(p, value);
            }
            Ok(Value::fun(graph))
        }
        SortKind::Uninterpreted(_) => {
            // Only ever compared for equality, so the name of its model value
            // is the whole of it — and a name is what a TLA+ model value is.
            let v = model.eval(term, tm);
            match tm.get(v).map(|t| t.kind.clone()) {
                Some(TermKind::Var(sym)) => Ok(Value::Str(tm.resolve_str(sym).to_string())),
                _ => Err(DecodeError::Undecided(
                    "an uninterpreted value the model did not decide".into(),
                )),
            }
        }
        _ => Err(DecodeError::Unsupported(format!(
            "a value at the sort {}",
            crate::sorts::render_sort(sort, tm)
        ))),
    }
}

/// Read a set-sorted model value as its members.
///
/// The solver's set values are built from `set.empty`, `set.singleton` and
/// `set.union`, which is the normal form CVC5 uses for a set constant and the
/// one `Encoder::native_set_of` writes. Anything else is refused rather than
/// approximated: a set decoded with a member missing replays as a different
/// state.
fn collect_set(
    term: TermId,
    elem: SortId,
    model: &Model,
    tm: &mut TermManager,
    depth: usize,
    out: &mut BTreeSet<Value>,
) -> Result<(), DecodeError> {
    if depth > MAX_DEPTH {
        return Err(DecodeError::Unsupported(format!(
            "a set nesting deeper than the limit of {MAX_DEPTH}"
        )));
    }
    let mut stack = vec![(term, depth)];
    while let Some((t, d)) = stack.pop() {
        if d > MAX_DEPTH {
            return Err(DecodeError::Unsupported(format!(
                "a set nesting deeper than the limit of {MAX_DEPTH}"
            )));
        }
        match tm.get(t).map(|x| x.kind.clone()) {
            Some(TermKind::SetEmpty(_)) => {}
            Some(TermKind::SetSingleton(e)) => {
                out.insert(decode_at(e, elem, None, model, tm, d + 1)?);
            }
            Some(TermKind::SetUnion(a, b)) => {
                stack.push((a, d + 1));
                stack.push((b, d + 1));
            }
            // An opaque set — a set-valued `VARIABLE`, most of the time.
            // There is no model value to read, and that is not an oversight
            // in the solver: the finite-set theory is a ground *reduction*,
            // so what the query decided about a set is exactly the membership
            // atoms it built. Those are what the value is recovered from.
            _ => membership_of(t, elem, model, tm, d, out)?,
        }
    }
    Ok(())
}

/// Recover an opaque set's value from the membership atoms about it.
///
/// `set.member(e, s)` is a Boolean the model decides, and the reduction built
/// one for every element the query ever asked about. Collecting the ones that
/// came out true gives a concrete set that satisfies every membership
/// constraint in the query — which is what makes it a witness rather than a
/// guess.
///
/// Elements nothing asked about are genuinely unconstrained, so leaving them
/// out is *a* correct choice rather than the only one. That is safe here for a
/// reason worth stating: the trace is replayed afterwards. If the set this
/// picks were not good enough — a cardinality constraint it fails, say — the
/// replay rejects it and the checker answers `Unknown` rather than reporting a
/// counterexample it cannot stand behind.
fn membership_of(
    set: TermId,
    elem: SortId,
    model: &Model,
    tm: &mut TermManager,
    depth: usize,
    out: &mut BTreeSet<Value>,
) -> Result<(), DecodeError> {
    // Snapshot the bound first: `Model::eval` interns terms of its own, and a
    // scan that chased its own tail would never finish.
    let bound = tm.len();
    let mut atoms: Vec<(TermId, TermId)> = Vec::new();
    for i in 0..bound {
        let id = TermId(u32::try_from(i).map_err(|_| {
            DecodeError::Unsupported("a term manager larger than the index space".into())
        })?);
        if let Some(TermKind::SetMember(e, s)) = tm.get(id).map(|t| t.kind.clone())
            && s == set
        {
            atoms.push((id, e));
        }
    }
    for (atom, e) in atoms {
        // Skip the solver's own scaffolding. The finite-set reduction invents
        // *extensionality witnesses* — `@set_ext_a_b`, a value that must be in
        // one of two unequal sets and not the other — and the encoder invents
        // names of its own. None of them is a TLA+ value: `@` cannot appear in
        // a TLA+ identifier, which is exactly why both reserve it. A witness
        // that the model happens to place inside a set is an artifact of the
        // reduction, and putting it in the trace would describe a state the
        // specification cannot have.
        //
        // Dropping it is not assumed to be harmless. The trace is replayed
        // afterwards, so a set that came out wrong is caught there and the
        // answer is `Unknown` rather than a counterexample nobody can check.
        let named = model.eval(e, tm);
        if let Some(TermKind::Var(sym)) = tm.get(named).map(|t| t.kind.clone())
            && tm.resolve_str(sym).starts_with('@')
        {
            continue;
        }
        let v = model.eval(atom, tm);
        match tm.get(v).map(|t| t.kind.clone()) {
            Some(TermKind::True) => {
                out.insert(decode_at(e, elem, None, model, tm, depth + 1)?);
            }
            Some(TermKind::False) => {}
            _ => {
                return Err(DecodeError::Undecided(
                    "a set membership the model did not decide".into(),
                ));
            }
        }
    }
    Ok(())
}

/// Rebuild the SMT term for a decoded domain point, so it can index the graph.
///
/// Only the sorts a function domain can have here. A domain point that cannot
/// be rebuilt is refused: selecting at the wrong index would decode a function
/// that is not the one in the model.
fn encode_index(v: &Value, sort: SortId, tm: &mut TermManager) -> Result<TermId, DecodeError> {
    match v {
        Value::Int(i) => Ok(tm.mk_int(num_bigint::BigInt::from(*i))),
        Value::Bool(b) => Ok(tm.mk_bool(*b)),
        Value::Str(s) => Ok(tm.mk_string_lit(s)),
        _ => Err(DecodeError::Unsupported(format!(
            "a function domain point at the sort {}",
            crate::sorts::render_sort(sort, tm)
        ))),
    }
}

/// Rebuild a decoded value as an SMT term at `sort` — the inverse of
/// [`decode`].
///
/// Used to **block** a counterexample: asserting that the states are not these
/// states is how a second, different counterexample is found. Blocking only
/// ever *adds* constraints, so it can remove behaviours and never invent one —
/// which is why a partial answer here is safe, and why the shapes it cannot
/// rebuild are simply left out of the clause rather than guessed at.
///
/// `None` for a shape with no term form: a set or a function, whose value
/// lives in the query's membership and `select` terms rather than in anything
/// this can reconstruct, and any value whose sort disagrees with it.
#[must_use]
pub fn encode_value(v: &Value, sort: SortId, tm: &mut TermManager) -> Option<TermId> {
    let kind = tm.sorts.get(sort).map(|s| s.kind.clone())?;
    match (v, &kind) {
        (Value::Bool(b), SortKind::Bool) => Some(tm.mk_bool(*b)),
        (Value::Int(i), SortKind::Int) => Some(tm.mk_int(num_bigint::BigInt::from(*i))),
        (Value::Str(t), SortKind::String) => Some(tm.mk_string_lit(t)),
        // A value of uninterpreted sort *is* its name — that is what an
        // uninterpreted sort means — and the name came out of the model, so
        // rebuilding the variable finds the very term the model named.
        (Value::Str(name), SortKind::Uninterpreted(_)) => Some(tm.mk_var(name, sort)),
        (Value::Tuple(_) | Value::Record(_), SortKind::Datatype(_)) => {
            let fields = struct_fields(sort, tm)?;
            let name = tm.sorts.datatype_name(sort)?.to_string();
            let mut args = Vec::with_capacity(fields.len());
            for (field, fs) in &fields {
                let part = match v {
                    Value::Tuple(xs) => {
                        let i: usize = field.strip_prefix("@t")?.parse().ok()?;
                        xs.get(i.checked_sub(1)?)?
                    }
                    Value::Record(fs2) => fs2.get(field.strip_prefix("@f")?)?,
                    _ => return None,
                };
                args.push(encode_value(part, *fs, tm)?);
            }
            Some(tm.mk_dt_constructor(&name, args, sort))
        }
        _ => None,
    }
}

/// A canonical value at `sort`, for a point the query left open.
///
/// Only the sorts whose values are enumerable from the sort alone. An
/// uninterpreted sort deliberately has none: its values are only ever compared
/// for equality, so there is no canonical one to pick and inventing a name
/// would invent a distinction.
fn default_at(sort: SortId, tm: &mut TermManager, depth: usize) -> Option<Value> {
    if depth > MAX_DEPTH {
        return None;
    }
    match tm.sorts.get(sort).map(|s| s.kind.clone())? {
        SortKind::Bool => Some(Value::Bool(false)),
        SortKind::Int => Some(Value::Int(0)),
        SortKind::String => Some(Value::Str(String::new())),
        SortKind::Set(_) => Some(Value::Set(BTreeSet::new())),
        SortKind::Array { .. } => Some(Value::fun(BTreeMap::new())),
        SortKind::Datatype(_) => {
            let fields = struct_fields(sort, tm)?;
            let mut parts = Vec::with_capacity(fields.len());
            for (name, fs) in &fields {
                parts.push((name.clone(), default_at(*fs, tm, depth + 1)?));
            }
            if parts.iter().all(|(n, _)| n.starts_with("@t")) {
                return Some(Value::Tuple(parts.into_iter().map(|(_, v)| v).collect()));
            }
            let mut out = BTreeMap::new();
            for (n, v) in parts {
                out.insert(n.strip_prefix("@f")?.to_string(), v);
            }
            Some(Value::Record(out))
        }
        _ => None,
    }
}

/// The graph points the query actually asked about, as (index, `select` term).
///
/// `Model::eval` has no case for `select`, so the value at a point can only be
/// read from a `select` term the query itself built and the model therefore
/// decided. Gathering them is the array-theory counterpart of
/// [`membership_of`], and for the same reason: a model determines a value
/// exactly where something asked for one.
fn selects_of(
    array: TermId,
    dom: SortId,
    model: &Model,
    tm: &mut TermManager,
    depth: usize,
) -> Result<Vec<(Value, TermId)>, DecodeError> {
    let bound = tm.len();
    let mut found: Vec<(TermId, TermId)> = Vec::new();
    for i in 0..bound {
        let id = TermId(u32::try_from(i).map_err(|_| {
            DecodeError::Unsupported("a term manager larger than the index space".into())
        })?);
        if let Some(TermKind::Select(a, idx)) = tm.get(id).map(|t| t.kind.clone())
            && a == array
        {
            found.push((idx, id));
        }
    }
    let mut out = Vec::with_capacity(found.len());
    for (idx, sel) in found {
        // An index the model left open cannot be placed, so the point it
        // stands for is left to the domain walk and its default.
        match decode_at(idx, dom, None, model, tm, depth + 1) {
            Ok(v) => out.push((v, sel)),
            Err(DecodeError::Undecided(_)) => {}
            Err(e) => return Err(e),
        }
    }
    Ok(out)
}
