//! Fairness assumptions on the lasso (issue #47).
//!
//! A `SPECIFICATION` is often written `Init /\ [][Next]_vars /\ WF_vars(Next)`,
//! or with the per-process idiom `\A self \in Node : WF_vars(step(self))`. A
//! lasso search that ignored the conjunct would report an **unfair** lasso –
//! one that stutters forever with an action enabled, say – as a behaviour of
//! the specification, and so as a counterexample to a liveness property the
//! specification keeps. Up to now the checker declined a temporal property
//! under fairness, by name. This module assumes it.
//!
//! # What a fairness condition says of a lasso
//!
//! On a lasso – a prefix, then a cycle repeated forever – `WF_v(A)` and
//! `SF_v(A)` are statements about the cycle alone:
//!
//! ```text
//! WF_v(A) is violated  iff  A is enabled at EVERY cycle state  and  no cycle step is an <A>_v step
//! SF_v(A) is violated  iff  A is enabled at SOME cycle state  and  no cycle step is an <A>_v step
//! ```
//!
//! (`ENABLED <A>_v` at a state `s` is "some next state `s''` has
//! `A(s, s'') /\ s'' != s` on the subscript's variables"; `<A>_v` is the
//! same with the step actually taken.) A lasso is a behaviour of the
//! specification only if no fairness conjunct is violated, so the lasso
//! search must report a violating lasso **only when it is fair**.
//!
//! # Both are checked exactly, on the concrete cycle
//!
//! The one statement about a cycle a bounded query can make exactly is a
//! **positive** one: `__fair_taken_i' = __fair_taken_i \/ (InLoop' /\
//! <A>_v)` accumulates over the unrolling and, at the close, says whether a
//! cycle step took the action (an existential inside `A` is in positive
//! polarity there, which the skolemizing pass handles exactly). What a
//! fairness assumption must *exclude* is the negation of such a statement –
//! "enabled somewhere in the cycle and taken nowhere", or "enabled
//! everywhere and taken nowhere" – and `ENABLED` is a statement about
//! **all** next states: `A(s, s'')` with a free `s''` is satisfied by any
//! `s''` where the action fails, so a free shadow copy of the state claims
//! "not enabled" wherever the solver likes. (A first version tried exactly
//! that for strong fairness; it excluded nothing, and every candidate
//! reached the concrete check below.)
//!
//! So a fairness instance constrains the symbolic query only through
//! `taken`, and every candidate lasso is **examined** on its concrete cycle
//! (`Bmc::fairness_of`): `taken` by the evaluator on every cycle step,
//! and `ENABLED` by the solver on each cycle state, the state pinned into
//! `A` as literals ([`enabled`]). A lasso found unfair is ruled out by a
//! clause with the evidence the examination produced: for `WF`, every lasso
//! whose cycle stays within the states just found enabling (they all
//! enable, concretely); for `SF`, every lasso whose cycle **contains** one
//! of them; and, in both, that takes no step of the action. The search
//! resumes at the same depth.
//!
//! The direction of each step is the safe one. A reported lasso satisfied
//! every assumption on its concrete cycle; an assumption that could not be
//! evaluated exactly is `Unknown`, never dropped; an unfair lasso that could
//! not be ruled out is `Unknown` too, never reported and never dismissed.
//!
//! # Quantified fairness
//!
//! `\A p \in P : WF_v(A(p))` is instantiated per candidate of `P` – one
//! instance each, guarded by `c \in P` – so `P` must have statically known
//! members (a literal, a pinned `CONSTANT`, a ground range); a domain
//! without them is declined by name, as `\A` over an unconstrained set
//! always is here.

use std::collections::HashMap;
use std::rc::Rc;

use nixie_core::{SortId, SortKind, TermManager};
use nixie_tla::kera::{Kera, KeraRef, Name};
use nixie_tla::lower::{Syms, skolemize_with_syms_at};
use nixie_tla::{Evaluator, Lowerer, Value};
use nixie_tla_syntax::ast::{FairnessKind, Ident, Junct, Pattern, QuantKind};
use nixie_tla_syntax::{Expr, ExprKind, FairnessClause, Module};

use crate::encode::Encoder;
use crate::trace::State;

/// The prefix of every auxiliary variable this module adds to the rewritten
/// specification: hidden from the trace like the lasso's own bookkeeping.
pub const AUX_PREFIX: &str = "__fair_";

/// Weak (`WF`) or strong (`SF`) fairness.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    /// `WF_v(A)`: continuously enabled, then taken infinitely often.
    Weak,
    /// `SF_v(A)`: enabled infinitely often, then taken infinitely often.
    Strong,
}

/// One fairness assumption the lasso search makes: `WF_v(A)` or `SF_v(A)`
/// for one action, with the quantifiers of `\A p \in P : …` instantiated.
#[derive(Debug, Clone)]
pub struct Instance {
    /// Weak or strong.
    pub kind: Kind,
    /// The clause this instance instantiates, briefly rendered.
    pub rendered: String,
    /// The binders instantiated: `(name, its value)`, what the evaluator
    /// binds to read [`Instance::step`] on a concrete state.
    pub bindings: Vec<(Name, Value)>,
    /// `c \in P`, one per instantiated binder group: the instance is an
    /// assumption for a real member only.
    pub guards: Vec<KeraRef>,
    /// The action alone: `A` with the binders instantiated.
    pub action: KeraRef,
    /// The subscript as a state function.
    pub subscript: KeraRef,
    /// `⟨A⟩_v`: the action, and the subscript's variables changing.
    pub step: KeraRef,
}

/// A stack entry of [`decompose`]: the clause (or part of one) still to
/// read, in its module, under the quantifiers scoped above it.
type Pending<'a> = (&'a Module, &'a Expr, Vec<(&'a Pattern, &'a Expr)>);

/// One `WF`/`SF` node of a clause, with the quantifiers above it.
struct Raw<'a> {
    kind: Kind,
    subscript: &'a Expr,
    action: &'a Expr,
    binders: Vec<(&'a Pattern, &'a Expr)>,
    home: &'a Module,
}

/// Split a clause into its fairness nodes, each with the quantifiers that
/// scope it. `\A p \in P : WF_v(A(p)) /\ SF_w(B(p))` is two.
fn decompose<'a>(clause: &FairnessClause<'a>) -> Result<Vec<Raw<'a>>, String> {
    let mut out = Vec::new();
    let mut stack: Vec<Pending<'a>> = vec![(clause.home, clause.expr, Vec::new())];
    while let Some((home, e, binders)) = stack.pop() {
        match &e.kind {
            ExprKind::Paren(inner) | ExprKind::Label { body: inner, .. } => {
                stack.push((home, inner, binders));
            }
            ExprKind::Quant {
                kind: QuantKind::Forall,
                bounds,
                body,
            } => {
                let mut scoped = binders;
                for b in bounds {
                    for p in &b.patterns {
                        scoped.push((p, &b.domain));
                    }
                }
                stack.push((home, body, scoped));
            }
            ExprKind::Junction {
                kind: Junct::And,
                items,
            } => {
                for item in items.iter().rev() {
                    stack.push((home, item, binders.clone()));
                }
            }
            ExprKind::Infix { op, lhs, rhs, .. } if op == "/\\" => {
                stack.push((home, rhs, binders.clone()));
                stack.push((home, lhs, binders));
            }
            ExprKind::Fairness {
                kind,
                subscript,
                body,
            } => out.push(Raw {
                kind: if kind == &FairnessKind::Weak {
                    Kind::Weak
                } else {
                    Kind::Strong
                },
                subscript: subscript.as_ref(),
                action: body.as_ref(),
                binders,
                home,
            }),
            ExprKind::UnboundedQuant {
                kind: QuantKind::Forall,
                ..
            } => {
                return Err(format!(
                    "`{}` quantifies a fairness condition over an unbounded set; the members to \
                     instantiate it per process are not known",
                    clause.rendered
                ));
            }
            _ => {
                return Err(format!(
                    "`{}` is not a fairness condition",
                    nixie_tla_syntax::behavior::brief(e)
                ));
            }
        }
    }
    Ok(out)
}

/// Lower every clause to the instances the lasso encoding assumes.
///
/// `low` is the specification's own lowerer (so a `.cfg`'s substitutions
/// reach the clause's names) and `root` the module the check reads roles in.
///
/// # Errors
///
/// The first construct that cannot be assumed faithfully, by name: a
/// fairness domain without statically known members, a tuple pattern over
/// a non-tuple candidate, a primed subscript, a lowering error.
pub fn lower<'a>(
    clauses: &[FairnessClause<'a>],
    low: &mut Lowerer<'a>,
    root: &'a Module,
) -> Result<Vec<Instance>, String> {
    let mut out: Vec<Instance> = Vec::new();
    let mut eval = Evaluator::new();
    for clause in clauses {
        for raw in decompose(clause)? {
            let mut lowered = |e: &'a Expr| {
                low.lower_expr_in(root, raw.home, e)
                    .map_err(|e| format!("`{}`: {e}", clause.rendered))
            };
            let subscript = lowered(raw.subscript)?;
            if crate::bmc::mentions_prime(&subscript) {
                return Err(format!(
                    "`{}` has a primed subscript; the subscript of a fairness condition is a \
                     state function",
                    clause.rendered
                ));
            }
            // The domains, once; their candidates are what the clause is
            // instantiated over.
            let mut domains = Vec::with_capacity(raw.binders.len());
            for (pattern, domain) in &raw.binders {
                let d = lowered(domain)?;
                let candidates = crate::frames::closed_elements(
                    &d,
                    crate::encode::DEFAULT_MAX_CANDIDATES,
                )
                .ok_or_else(|| {
                    format!(
                        "`{}` quantifies fairness over a set with no statically known members; \
                         the instances to assume it per member are not known",
                        clause.rendered
                    )
                })?;
                domains.push((*pattern, d, candidates));
            }
            // Instantiate: every combination of the binder groups' candidates.
            let mut combos: Vec<Vec<(&Pattern, KeraRef)>> = vec![Vec::new()];
            for (pattern, _, candidates) in &domains {
                let mut next = Vec::new();
                for c in &combos {
                    for cand in candidates {
                        let mut c = c.clone();
                        c.push((*pattern, Rc::clone(cand)));
                        next.push(c);
                    }
                }
                combos = next;
            }
            for combo in combos {
                let mut guards = Vec::new();
                let mut bindings: Vec<(Name, Value)> = Vec::new();
                for ((pattern, domain, _), (_, cand)) in domains.iter().zip(&combo) {
                    guards.push(Kera::In(Rc::clone(cand), Rc::clone(domain)).rc());
                    let parts: Vec<KeraRef> = match (pattern, cand.as_ref()) {
                        (Pattern::Name(_), _) => vec![Rc::clone(cand)],
                        (Pattern::Tuple(ids), Kera::Tuple(xs)) if ids.len() == xs.len() => {
                            xs.iter().map(Rc::clone).collect()
                        }
                        (Pattern::Tuple(_), _) => {
                            return Err(format!(
                                "`{}` binds a tuple pattern over a candidate that is not a \
                                 tuple of the same arity",
                                clause.rendered
                            ));
                        }
                    };
                    for (id, part) in idents(pattern).zip(&parts) {
                        let value = eval
                            .eval(part)
                            .map_err(|e| format!("`{}`: {e}", clause.rendered))?;
                        bindings.push((Name(id.name.clone()), value));
                        low.bind_constant(&id.name, Rc::clone(part));
                    }
                }
                let action = low.lower_expr_in(root, raw.home, raw.action);
                // Withdraw the bindings before anything else is lowered.
                for (name, _) in &bindings {
                    low.unbind_constant(name.as_str());
                }
                let action = action.map_err(|e| format!("`{}`: {e}", clause.rendered))?;
                let step = Kera::And(vec![Rc::clone(&action), changed(&subscript)]).rc();
                out.push(Instance {
                    kind: raw.kind,
                    rendered: clause.rendered.clone(),
                    bindings,
                    guards,
                    action,
                    subscript: Rc::clone(&subscript),
                    step,
                });
            }
        }
    }
    Ok(out)
}

/// The identifiers a bound pattern names, in order.
fn idents(pattern: &Pattern) -> impl Iterator<Item = &Ident> {
    let names: Vec<&Ident> = match pattern {
        Pattern::Name(id) => vec![id],
        Pattern::Tuple(ids) => ids.iter().collect(),
    };
    names.into_iter()
}

/// `v' # v` for a subscript: for a tuple, **some** component changes. It
/// is the exact negation of `UNCHANGED v` – `<<A>>_<<a, b>>` is
/// `A /\ (a' # a \/ b' # b)` in TLA+ – and the first version here
/// required every component to change. With the usual `vars == <<x, y>>`
/// that read a step as taken only when both variables moved, so an action
/// that moves one of them was never "taken" on its own cycle: enabled at
/// every state of it and taken nowhere is the definition of a `WF`
/// violation, and a fair lasso was ruled out as unfair.
fn changed(subscript: &KeraRef) -> KeraRef {
    let differs =
        |x: &KeraRef| Kera::Not(Kera::Eq(Kera::Prime(Rc::clone(x)).rc(), Rc::clone(x)).rc()).rc();
    if let Kera::Tuple(items) = subscript.as_ref() {
        return Kera::Or(items.iter().map(differs).collect()).rc();
    }
    differs(subscript)
}

/// What a concrete examination of a candidate lasso found about its fairness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    /// Every assumption holds of the lasso's cycle.
    Satisfied,
    /// An assumption is violated: the lasso is not a behaviour of the
    /// specification. Per violated instance, the cycle states the examination
    /// **found enabling** its action – all of them for `WF`, some for `SF` –
    /// which is what a block may generalize from: for `WF`, any lasso whose
    /// cycle stays within those states; for `SF`, any lasso whose cycle
    /// contains one of them; and, in both, that takes no step of the
    /// instance's action – unfair by the same evidence.
    Violated {
        /// `(instance, cycle positions that enable its action)`.
        by: Vec<(usize, Vec<usize>)>,
        /// Which clause, and why, for the diagnostic.
        why: String,
    },
}

/// Whether each fairness instance is *assumed* of a state: its guards hold.
/// A candidate the domain did not admit makes no assumption.
///
/// # Errors
///
/// The first guard the evaluator cannot decide.
fn assumed(instances: &[Instance], state: &State) -> Result<Vec<bool>, String> {
    let mut ev = Evaluator::new();
    let mut out = Vec::with_capacity(instances.len());
    for inst in instances {
        let mut holds = true;
        for g in &inst.guards {
            match ev.eval_state(g, state) {
                Ok(Value::Bool(b)) => holds &= b,
                Ok(v) => {
                    return Err(format!(
                        "`{}`: its domain membership evaluated to {v}, not a Boolean",
                        inst.rendered
                    ));
                }
                Err(e) => {
                    return Err(format!(
                        "`{}`: its domain membership could not be evaluated: {e}",
                        inst.rendered
                    ));
                }
            }
        }
        out.push(holds);
    }
    Ok(out)
}

/// Whether each instance's action is taken on a concrete step `(a, b)`.
///
/// # Errors
///
/// The first step the evaluator cannot decide.
fn taken_on(instances: &[Instance], a: &State, b: &State) -> Result<Vec<bool>, String> {
    let mut ev = Evaluator::new();
    let mut out = Vec::with_capacity(instances.len());
    for inst in instances {
        let mut env = a.clone();
        for (name, value) in &inst.bindings {
            env.insert(name.as_str().to_string(), value.clone());
        }
        match ev.eval_action(&inst.step, &env, b) {
            Ok(Value::Bool(b)) => out.push(b),
            Ok(v) => {
                return Err(format!(
                    "`{}`: its action evaluates to {v} on a cycle step, not a Boolean",
                    inst.rendered
                ));
            }
            Err(e) => {
                return Err(format!(
                    "`{}`: its action could not be evaluated on a cycle step: {e}",
                    inst.rendered
                ));
            }
        }
    }
    Ok(out)
}

/// The kernel literal for a decoded TLA+ value at `sort`, with the sorts the
/// literal's own nodes cannot supply declared to `encoder` (`{}` and the
/// binder of a function literal).
///
/// `None` for a value with no literal form at its sort – the honest refusal
/// that makes pinning fail, and with it the check, by name.
fn value_literal(
    v: &Value,
    sort: SortId,
    tm: &mut TermManager,
    encoder: &mut Encoder,
    fresh: &mut u32,
) -> Option<KeraRef> {
    let kind = tm.sorts.get(sort).map(|s| s.kind.clone())?;
    let out = match (v, &kind) {
        (Value::Bool(b), _) => Kera::Bool(*b).rc(),
        (Value::Int(i), _) => Kera::Int(i.to_string()).rc(),
        (Value::Str(s), SortKind::String) => Kera::Str(s.clone()).rc(),
        // A value of an uninterpreted sort is its name, as it was when the
        // specification declared it.
        (Value::Str(name), SortKind::Uninterpreted(_)) => Kera::Var(Name(name.clone())).rc(),
        (Value::Set(xs), SortKind::Set(e)) => {
            let mut parts = Vec::with_capacity(xs.len());
            for x in xs {
                parts.push(value_literal(x, *e, tm, encoder, fresh)?);
            }
            let node = Kera::SetEnum(parts).rc();
            encoder.declare_node_sort(&node, sort);
            node
        }
        // A sequence is a tuple at a sequence sort; the encoder reads the
        // sort off the node.
        (Value::Tuple(xs), SortKind::Datatype(_))
            if crate::sorts::seq_element(sort, tm).is_some() =>
        {
            let elem = crate::sorts::seq_element(sort, tm)?;
            let mut parts = Vec::with_capacity(xs.len());
            for x in xs {
                parts.push(value_literal(x, elem, tm, encoder, fresh)?);
            }
            let node = Kera::Tuple(parts).rc();
            encoder.declare_node_sort(&node, sort);
            node
        }
        (Value::Fun(map), SortKind::Array { domain, range }) => {
            // `[k \in {k1, …} |-> IF k = k1 THEN v1 ELSE … ]`: the keys are
            // the whole domain, so the last `ELSE` is never read.
            *fresh += 1;
            let var = Name(format!("{AUX_PREFIX}k{fresh}"));
            let var_node = Kera::Var(var.clone()).rc();
            encoder.declare_node_sort(&var_node, *domain);
            let mut keys = Vec::with_capacity(map.len());
            let mut body: Option<KeraRef> = None;
            for (k, val) in map.iter().rev() {
                let kl = value_literal(k, *domain, tm, encoder, fresh)?;
                let vl = value_literal(val, *range, tm, encoder, fresh)?;
                keys.push(kl.clone());
                let test = Kera::Eq(var_node.clone(), kl).rc();
                body = Some(match body {
                    None => Kera::Ite(Rc::clone(&test), Rc::clone(&vl), vl).rc(),
                    Some(rest) => Kera::Ite(test, vl, rest).rc(),
                });
            }
            let body = body?;
            encoder.declare_node_sort(&body, *range);
            let set = Kera::SetEnum(keys).rc();
            encoder.declare_node_sort(&set, tm.sorts.set(*domain));
            let node = Kera::FunDef { var, set, body }.rc();
            encoder.declare_node_sort(&node, sort);
            node
        }
        (Value::Tuple(xs), SortKind::Datatype(_)) => {
            let fields = crate::sorts::struct_fields(sort, tm)?;
            let mut parts = Vec::with_capacity(xs.len());
            for (i, x) in xs.iter().enumerate() {
                let (_, fs) = fields.get(i)?;
                parts.push(value_literal(x, *fs, tm, encoder, fresh)?);
            }
            let node = Kera::Tuple(parts).rc();
            encoder.declare_node_sort(&node, sort);
            node
        }
        (Value::Record(fs), SortKind::Datatype(_)) => {
            let fields = crate::sorts::struct_fields(sort, tm)?;
            let mut parts = Vec::with_capacity(fs.len());
            for (name, x) in fs {
                let (_, fsort) = fields
                    .iter()
                    .find(|(f, _)| f.strip_prefix("@f") == Some(name.as_str()))?;
                parts.push((name.clone(), value_literal(x, *fsort, tm, encoder, fresh)?));
            }
            let node = Kera::Record(parts).rc();
            encoder.declare_node_sort(&node, sort);
            node
        }
        (Value::Variant(tag, payload), SortKind::Datatype(_)) => {
            let payload_sort = crate::sorts::variant_ctor_payload(sort, tag, tm)?;
            let value = value_literal(payload, payload_sort, tm, encoder, fresh)?;
            let node = Kera::Variant {
                tag: tag.clone(),
                value,
            }
            .rc();
            encoder.declare_node_sort(&node, sort);
            node
        }
        _ => return None,
    };
    Some(out)
}

/// The kernel literal of every name of a decoded state that the fairness
/// checks pin: the variables and the constants, not a skolem witness (which
/// stands for "some member at this step" – the existential is the query's to
/// answer anew) and not the lasso's or this module's own bookkeeping.
///
/// # Errors
///
/// The first value with no literal form, by name.
pub fn literals_of(
    state: &State,
    encoder: &mut Encoder,
    tm: &mut TermManager,
) -> Result<HashMap<Name, KeraRef>, String> {
    let mut lits: HashMap<Name, KeraRef> = HashMap::new();
    let mut fresh = 0u32;
    for (name, value) in state {
        // A skolem witness is "some member at this step": the existential it
        // stands for is the query's to answer anew. The lasso's own
        // bookkeeping is not the specification's state.
        if nixie_tla::lower::is_skolem_witness(name)
            || name.starts_with(crate::temporal::SAVED)
            || name.starts_with(crate::temporal::TEMPORAL)
            || name.starts_with(crate::temporal::IN_LOOP)
            || name.starts_with(AUX_PREFIX)
        {
            continue;
        }
        let Some(var) = encoder.var_at(name, 0) else {
            continue;
        };
        let Some(sort) = tm.get(var).map(|d| d.sort) else {
            continue;
        };
        let Some(lit) = value_literal(value, sort, tm, encoder, &mut fresh) else {
            return Err(format!(
                "the value of `{name}` in a loop state has no literal form, so the state \
                 cannot be pinned into the fairness condition's action"
            ));
        };
        lits.insert(Name(name.clone()), lit);
    }
    Ok(lits)
}

/// What an `ENABLED` query needs beyond the state and the action: the
/// search's own skolem names, assumptions and budget, and its depth – the
/// query is encoded one step past it, where no variable of the unrolling
/// lives.
pub struct EnabledQuery<'a> {
    /// The symbolic set names a positive existential may be skolemized over.
    pub syms: Syms,
    /// The assumptions as encoded for the search in progress.
    pub assumed: &'a [nixie_core::TermId],
    /// The search's conflict budget, if any.
    pub limit: Option<u64>,
    /// The depth of the search this candidate came from.
    pub depth: u32,
}

/// The concrete half of a `WF` check: pin `state` into `action` and ask the
/// solver whether a next state satisfies it.
///
/// # Errors
///
/// A value with no literal form, an encoding failure, or a solver that
/// could not decide – each `Unknown`'s to report, never a guess.
pub fn enabled(
    encoder: &mut Encoder,
    action: &KeraRef,
    state: &State,
    query: &EnabledQuery<'_>,
    tm: &mut TermManager,
) -> Result<bool, String> {
    let step = query.depth.saturating_add(1);
    let lits = literals_of(state, encoder, tm)?;
    let pinned = nixie_tla::lower::pin_unprimed(action, &lits);
    // An existential inside the action is the question's to answer: positive
    // polarity, exactly as `Next` itself is skolemized.
    let pinned = skolemize_with_syms_at(&pinned, true, &query.syms);
    let term = encoder.encode_at(&pinned, step, tm).map_err(|e| {
        format!("the fairness condition's action does not encode on a loop state: {e}")
    })?;
    let mut solver = nixie_solver::Solver::new();
    if let Some(limit) = query.limit {
        solver.set_conflict_limit(limit);
    }
    for a in query.assumed {
        solver.assert(*a, tm);
    }
    for c in encoder.side_constraints().to_vec() {
        solver.assert(c, tm);
    }
    solver.assert(term, tm);
    match solver.check(tm) {
        nixie_solver::SolverResult::Sat => Ok(true),
        nixie_solver::SolverResult::Unsat => Ok(false),
        nixie_solver::SolverResult::Unknown => Err(
            "the solver could not decide whether a fairness condition's action is enabled in a \
             loop state"
                .into(),
        ),
    }
}

/// Evaluate a lasso's fairness on its concrete cycle: `cycle` are the cycle
/// states (positions `l..k-1` of the trace, so `cycle[i] -> cycle[i+1]` is a
/// step and the last returns to the first), `enabled_at` answers `ENABLED`
/// for an instance index and a state.
///
/// # Errors
///
/// The first instance or step that cannot be decided.
pub fn examine(
    instances: &[Instance],
    cycle: &[State],
    mut enabled_at: impl FnMut(usize, &State) -> Result<bool, String>,
) -> Result<Verdict, String> {
    let assumed = assumed(instances, &cycle[0])?;
    let mut taken = vec![false; instances.len()];
    for pair in cycle.windows(2) {
        let here = taken_on(instances, &pair[0], &pair[1])?;
        for (t, h) in taken.iter_mut().zip(here) {
            *t |= h;
        }
    }
    // The closing step: the last state's successor is the first.
    let closing = taken_on(instances, cycle.last().expect("non-empty"), &cycle[0])?;
    for (t, h) in taken.iter_mut().zip(closing) {
        *t |= h;
    }
    let mut by: Vec<(usize, Vec<usize>)> = Vec::new();
    let mut why: Vec<String> = Vec::new();
    for (i, inst) in instances.iter().enumerate() {
        if !assumed[i] || taken[i] {
            continue;
        }
        let mut enabling = Vec::new();
        for (p, st) in cycle.iter().enumerate() {
            if enabled_at(i, st)? {
                enabling.push(p);
            }
        }
        let violated = match inst.kind {
            Kind::Weak => enabling.len() == cycle.len(),
            Kind::Strong => !enabling.is_empty(),
        };
        if violated {
            by.push((i, enabling));
            why.push(format!(
                "`{}`: the action is enabled at {} of the loop's {} state(s) and taken on no \
                 loop step",
                inst.rendered,
                by.last().map_or(0, |(_, e)| e.len()),
                cycle.len()
            ));
        }
    }
    if by.is_empty() {
        return Ok(Verdict::Satisfied);
    }
    Ok(Verdict::Violated {
        by,
        why: why.join("; "),
    })
}
