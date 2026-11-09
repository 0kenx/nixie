//! Ground QF_ANIA decision procedure.
//!
//! Handles formulas whose arrays are defined by constant `store` towers and
//! whose free integer variables (indices and similar) lie in finite boxes.
//! Under each concrete assignment we evaluate the full term DAG – including
//! nested `select`, `ite`, `abs`-as-ite, and multi-factor products – via
//! read-over-write on the store maps.
//!
//! Works on purified assertions (`c = select(A,i)` interfaces + pure arith)
//! and on residual `ite`/`select` still present under arith after purification.

use crate::nl_dispatch::NlDispatchResult;
use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::sort::SortKind;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::ToPrimitive;
use std::collections::{HashMap, HashSet};

/// Soft cap on visited partial assignments. Pruning usually keeps
/// real work far below this for constrained formulas.
const MAX_LEAVES: u64 = 5_000_000;

/// Try to decide ground-store + finite-box ANIA.
pub fn try_decide_ground_ania(
    assertions: &[TermId],
    manager: &TermManager,
) -> Option<NlDispatchResult> {
    let mut arrays: HashMap<TermId, ArrayInterp> = HashMap::new();
    let mut interfaces: Vec<Interface> = Vec::new();
    // `v = t` where `t` is evaluable once indices are bound (nullary define-fun).
    let mut definitions: Vec<(TermId, TermId)> = Vec::new();
    let mut bounds: HashMap<TermId, (Option<i64>, Option<i64>)> = HashMap::new();
    let mut atoms: Vec<Atom> = Vec::new();
    let mut bool_atoms: Vec<TermId> = Vec::new(); // must eval to true
    let mut free_ints: HashSet<TermId> = HashSet::new();
    let mut cond_defs: Vec<(TermId, TermId, TermId)> = Vec::new();

    for &a in assertions {
        collect_assertion(
            a,
            manager,
            &mut arrays,
            &mut interfaces,
            &mut definitions,
            &mut bounds,
            &mut atoms,
            &mut bool_atoms,
            &mut free_ints,
            &mut cond_defs,
        )?;
    }

    if arrays.is_empty() || (atoms.is_empty() && bool_atoms.is_empty()) {
        return None;
    }

    // Every select (in atoms or interfaces) must read a defined array.
    for atom in &atoms {
        ensure_selects_defined(atom.lhs, manager, &arrays)?;
        ensure_selects_defined(atom.rhs, manager, &arrays)?;
    }
    for &b in &bool_atoms {
        ensure_selects_defined(b, manager, &arrays)?;
    }
    for iface in &interfaces {
        if !arrays.contains_key(&iface.array) {
            return None;
        }
        collect_int_vars(iface.index, manager, &mut free_ints);
    }
    for &(_, rhs) in &definitions {
        ensure_selects_defined(rhs, manager, &arrays)?;
        collect_int_vars(rhs, manager, &mut free_ints);
    }
    // Soundness: a conditional-definition guard (`Implies(p, (= v body))` from
    // encoder-lifted `ite`) that depends on a free Boolean variable can never
    // be resolved by this integer-only enumeration, leaving `v` unbound and
    // any atom reading it silently satisfied. Refuse to decide in that case.
    if cond_defs.iter().any(|(p, _v, b)| {
        references_free_bool_var(*p, manager) || references_free_bool_var(*b, manager)
    }) {
        return None;
    }

    // Index / free int vars need finite boxes.  Iterate in canonical
    // (`TermId`) order, NOT `HashSet` order: the set is randomly seeded per
    // process, and the enumeration order of `domains` decides which corner
    // of the box the leaf budget meets first – an iteration-order-dependent
    // sat/unknown verdict is a per-process coin flip on the same binary.
    let mut ordered_free_ints: Vec<TermId> = free_ints.iter().copied().collect();
    ordered_free_ints.sort_unstable_by_key(|&t| t.0);
    let mut domains: Vec<(TermId, i64, i64)> = Vec::new();
    for &v in &ordered_free_ints {
        // Skip vars determined by interface selects, definitional eqs, or
        // conditional (encoder-lifted `ite`) definitions.
        if interfaces.iter().any(|i| i.const_var == v) {
            continue;
        }
        if definitions.iter().any(|(lhs, _)| *lhs == v) {
            continue;
        }
        if cond_defs.iter().any(|(_, var, _)| *var == v) {
            continue;
        }
        let (lo, hi) = bounds.get(&v).copied().unwrap_or((None, None));
        let lo = lo?;
        let hi = hi?;
        if hi < lo {
            return Some(NlDispatchResult::Unsat);
        }
        domains.push((v, lo, hi));
    }
    // Prefer smaller domains first for stronger early pruning.  The tiebreak
    // on `TermId` makes the order total: a stable sort over a randomly
    // ordered input would otherwise keep per-process `HashSet` order on ties.
    domains.sort_by_key(|&(v, lo, hi)| (i128::from(hi) - i128::from(lo), v.0));

    // Heap-stack search with early pruning: once enough vars are bound to
    // evaluate an atom, reject partial assignments immediately (critical when
    // e.g. `(select A i) = c` with sparse table values kills most of 1..N).
    let mut env = HashMap::new();
    let mut leaves = 0u64;
    match search_rec(
        0,
        &domains,
        &interfaces,
        &definitions,
        &cond_defs,
        &atoms,
        &bool_atoms,
        &arrays,
        manager,
        &mut env,
        &mut leaves,
    ) {
        Some(true) => {
            let interp = interpretation(assertions, manager, &arrays, &env)?;
            if !crate::nl_eval::holds_under(assertions, manager, &interp) {
                return None;
            }
            let mut assignments = HashMap::new();
            for (term, val) in env {
                assignments.insert(term, BigRational::from_integer(val));
            }
            Some(NlDispatchResult::sat_with(assignments))
        }
        Some(false) => Some(NlDispatchResult::Unsat),
        None => None, // exhausted leaf budget
    }
}

/// Try to decide a *pure* nonlinear-integer formula by exhaustive finite-domain
/// enumeration. Diagnostic stub for now.
pub fn try_decide_finite_domain_nia(
    assertions: &[TermId],
    manager: &TermManager,
) -> Option<NlDispatchResult> {
    /// `true` iff `term` is concretely evaluable by the shared `eval_int`/
    /// `eval_bool` machinery once its integer variables are bound.  Rejects
    /// anything those evaluators do not handle (`div`, `mod`, uninterpreted
    /// `apply`, `select`, …) so we never report a spurious verdict, and rejects
    /// free Boolean variables (which this finite-domain search does not
    /// enumerate).
    fn fully_evaluable(term: TermId, manager: &TermManager) -> bool {
        let mut stack = vec![term];
        let mut seen = HashSet::new();
        while let Some(id) = stack.pop() {
            if !seen.insert(id) {
                continue;
            }
            let Some(n) = manager.get(id) else {
                return false;
            };
            match &n.kind {
                TermKind::IntConst(_) | TermKind::True | TermKind::False => {}
                TermKind::Var(_) => {
                    if n.sort != manager.sorts.int_sort {
                        return false;
                    }
                }
                TermKind::Neg(a) | TermKind::Not(a) => stack.push(*a),
                TermKind::Add(xs) | TermKind::Mul(xs) | TermKind::And(xs) | TermKind::Or(xs) => {
                    stack.extend(xs.iter().copied());
                }
                TermKind::Distinct(xs) => stack.extend(xs.iter().copied()),
                TermKind::Sub(a, b)
                | TermKind::Eq(a, b)
                | TermKind::Le(a, b)
                | TermKind::Lt(a, b)
                | TermKind::Ge(a, b)
                | TermKind::Gt(a, b)
                | TermKind::Implies(a, b) => {
                    stack.push(*a);
                    stack.push(*b);
                }
                TermKind::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermKind::Let { bindings, body } => {
                    for &(_, v) in bindings.iter() {
                        stack.push(v);
                    }
                    stack.push(*body);
                }
                // div / mod / apply / select / store / quantifiers / … – not
                // concretely evaluable here.
                _ => return false,
            }
        }
        true
    }

    let mut arrays: HashMap<TermId, ArrayInterp> = HashMap::new();
    let mut interfaces: Vec<Interface> = Vec::new();
    let mut definitions: Vec<(TermId, TermId)> = Vec::new();
    let mut bounds: HashMap<TermId, (Option<i64>, Option<i64>)> = HashMap::new();
    let mut atoms: Vec<Atom> = Vec::new();
    let mut bool_atoms: Vec<TermId> = Vec::new();
    let mut free_ints: HashSet<TermId> = HashSet::new();
    let mut cond_defs: Vec<(TermId, TermId, TermId)> = Vec::new();
    for &a in assertions {
        collect_assertion(
            a,
            manager,
            &mut arrays,
            &mut interfaces,
            &mut definitions,
            &mut bounds,
            &mut atoms,
            &mut bool_atoms,
            &mut free_ints,
            &mut cond_defs,
        )?;
    }
    // This path is for *pure* integer arithmetic; defer ground-store formulas
    // (arrays) to [`try_decide_ground_ania`].
    if !arrays.is_empty() {
        return None;
    }
    // Any purification interface (`c = (select A i)`) must read a *defined*
    // array – but `arrays` is empty here (no stores), so an uninterpreted
    // array select cannot be concretely evaluated. Refuse to decide rather
    // than report a false verdict.
    if interfaces.iter().any(|i| !arrays.contains_key(&i.array)) {
        return None;
    }
    if atoms.is_empty() && bool_atoms.is_empty() {
        return None;
    }
    // Soundness gate: every atom/bool_atom must reduce to a concrete Boolean
    // once its integer variables are bound.  An unevaluable atom (div/mod/
    // apply/…) would make `eval_atom` return `false` for every assignment and
    // yield a false `Unsat`; refuse to decide instead.
    for atom in &atoms {
        if !fully_evaluable(atom.lhs, manager) || !fully_evaluable(atom.rhs, manager) {
            return None;
        }
    }
    for &b in &bool_atoms {
        if !fully_evaluable(b, manager) {
            return None;
        }
    }
    // Conditional-definition guards (`Implies(p, (= v body))` from encoder-
    // lifted `ite`) must also be concretely decidable once the enumerated
    // integers are bound. A guard that references a free Boolean variable
    // (never enumerated here) could neither fire nor be refuted, leaving `v`
    // unbound and the atom that reads it silently satisfied – a false `Sat`.
    for &(premise, _var, body) in &cond_defs {
        if !fully_evaluable(premise, manager) || !fully_evaluable(body, manager) {
            return None;
        }
    }
    // Every free integer variable must carry a small arithmetic box, else the
    // search space is not finite (or too large) – bail to the caller.
    // Canonical (`TermId`) iteration order for determinism – see the matching
    // comment in [`try_decide_ground_ania`].
    let mut ordered_free_ints: Vec<TermId> = free_ints.iter().copied().collect();
    ordered_free_ints.sort_unstable_by_key(|&t| t.0);
    let mut domains: Vec<(TermId, i64, i64)> = Vec::new();
    let mut total: u64 = 1;
    for &v in &ordered_free_ints {
        if interfaces.iter().any(|i| i.const_var == v)
            || definitions.iter().any(|(l, _)| *l == v)
            || cond_defs.iter().any(|(_, var, _)| *var == v)
        {
            continue;
        }
        let (lo, hi) = bounds.get(&v).copied().unwrap_or((None, None));
        let lo = lo?;
        let hi = hi?;
        if hi < lo {
            return Some(NlDispatchResult::Unsat);
        }
        let size = u64::try_from(i128::from(hi) - i128::from(lo) + 1).ok()?;
        total = total.checked_mul(size)?;
        if total > MAX_LEAVES {
            return None;
        }
        domains.push((v, lo, hi));
    }
    // Smaller domains first → stronger early pruning (total order – see
    // [`try_decide_ground_ania`]).
    domains.sort_by_key(|&(v, lo, hi)| (i128::from(hi) - i128::from(lo), v.0));

    let mut env = HashMap::new();
    let mut leaves = 0u64;
    match search_rec(
        0,
        &domains,
        &interfaces,
        &definitions,
        &cond_defs,
        &atoms,
        &bool_atoms,
        &arrays,
        manager,
        &mut env,
        &mut leaves,
    ) {
        Some(true) => {
            let interp = interpretation(assertions, manager, &arrays, &env)?;
            if !crate::nl_eval::holds_under(assertions, manager, &interp) {
                return None;
            }
            let mut assignments = HashMap::new();
            for (term, val) in env {
                assignments.insert(term, BigRational::from_integer(val));
            }
            Some(NlDispatchResult::sat_with(assignments))
        }
        Some(false) => Some(NlDispatchResult::Unsat),
        None => None, // exhausted the leaf budget
    }
}

fn realize_interfaces(
    interfaces: &[Interface],
    definitions: &[(TermId, TermId)],
    arrays: &HashMap<TermId, ArrayInterp>,
    manager: &TermManager,
    env: &mut HashMap<TermId, BigInt>,
) -> bool {
    for iface in interfaces {
        let Some(index) = eval_int(iface.index, manager, arrays, env) else {
            continue;
        };
        let Some(array) = arrays.get(&iface.array) else {
            continue;
        };
        let value = index
            .to_i64()
            .and_then(|i| array.entries.get(&i).cloned())
            .or_else(|| array.default.clone());
        if let Some(value) = value {
            if env.get(&iface.const_var).is_some_and(|old| *old != value) {
                return false;
            }
            env.insert(iface.const_var, value);
        }
    }
    for &(variable, body) in definitions {
        if let Some(value) = eval_int(body, manager, arrays, env) {
            if env.get(&variable).is_some_and(|old| *old != value) {
                return false;
            }
            env.insert(variable, value);
        }
    }
    true
}

fn realize_cond_defs(
    definitions: &[(TermId, TermId, TermId)],
    arrays: &HashMap<TermId, ArrayInterp>,
    manager: &TermManager,
    env: &mut HashMap<TermId, BigInt>,
) -> bool {
    for &(guard, variable, body) in definitions {
        if eval_bool(guard, manager, arrays, env) != Some(true) {
            continue;
        }
        if let Some(value) = eval_int(body, manager, arrays, env) {
            if env.get(&variable).is_some_and(|old| *old != value) {
                return false;
            }
            env.insert(variable, value);
        }
    }
    true
}

fn partial_atoms_ok(
    atoms: &[Atom],
    bool_atoms: &[TermId],
    arrays: &HashMap<TermId, ArrayInterp>,
    manager: &TermManager,
    env: &HashMap<TermId, BigInt>,
) -> Option<bool> {
    let mut complete = true;
    for atom in atoms {
        match eval_atom(atom, manager, arrays, env) {
            Some(false) => return Some(false),
            Some(true) => {}
            None => complete = false,
        }
    }
    for &term in bool_atoms {
        match eval_bool(term, manager, arrays, env) {
            Some(false) => return Some(false),
            Some(true) => {}
            None => complete = false,
        }
    }
    complete.then_some(true)
}

/// `Some(true)` sat, `Some(false)` unsat (subtree exhausted), `None` budget.
#[allow(clippy::too_many_arguments)]
fn search_rec(
    pos: usize,
    domains: &[(TermId, i64, i64)],
    interfaces: &[Interface],
    definitions: &[(TermId, TermId)],
    cond_defs: &[(TermId, TermId, TermId)],
    atoms: &[Atom],
    bool_atoms: &[TermId],
    arrays: &HashMap<TermId, ArrayInterp>,
    manager: &TermManager,
    env: &mut HashMap<TermId, BigInt>,
    leaves: &mut u64,
) -> Option<bool> {
    enum Frame {
        Visit(usize, HashMap<TermId, BigInt>),
        Next {
            position: usize,
            base: HashMap<TermId, BigInt>,
            value: i64,
            last: i64,
        },
    }
    let mut stack = vec![Frame::Visit(pos, env.clone())];
    let mut incomplete = false;
    while let Some(frame) = stack.pop() {
        let (position, mut candidate) = match frame {
            Frame::Next {
                position,
                base,
                value,
                last,
            } => {
                let mut candidate = base.clone();
                candidate.insert(domains.get(position)?.0, BigInt::from(value));
                if value < last {
                    stack.push(Frame::Next {
                        position,
                        base,
                        value: value.checked_add(1)?,
                        last,
                    });
                }
                stack.push(Frame::Visit(position + 1, candidate));
                continue;
            }
            Frame::Visit(position, candidate) => (position, candidate),
        };
        *leaves = leaves.checked_add(1)?;
        if *leaves > MAX_LEAVES {
            return None;
        }
        let mut consistent = true;
        loop {
            let before = candidate.len();
            if !realize_interfaces(interfaces, definitions, arrays, manager, &mut candidate)
                || !realize_cond_defs(cond_defs, arrays, manager, &mut candidate)
            {
                consistent = false;
                break;
            }
            if candidate.len() == before {
                break;
            }
        }
        if !consistent {
            continue;
        }
        let truth = partial_atoms_ok(atoms, bool_atoms, arrays, manager, &candidate);
        if truth == Some(false) {
            continue;
        }
        if position == domains.len() {
            // Every collected definition must be interpreted too. An unresolved
            // leaf is neither a model nor evidence that this box is unsatisfiable.
            let definitions_complete = definitions.iter().all(|&(v, b)| {
                eval_int(b, manager, arrays, &candidate)
                    .zip(candidate.get(&v))
                    .is_some_and(|(x, y)| x == *y)
            }) && interfaces.iter().all(|i| {
                let Some(index) = eval_int(i.index, manager, arrays, &candidate) else {
                    return false;
                };
                let Some(array) = arrays.get(&i.array) else {
                    return false;
                };
                let value = index
                    .to_i64()
                    .and_then(|index| array.entries.get(&index))
                    .or(array.default.as_ref());
                value
                    .zip(candidate.get(&i.const_var))
                    .is_some_and(|(a, b)| a == b)
            }) && cond_defs.iter().all(
                |&(guard, v, b)| match eval_bool(guard, manager, arrays, &candidate) {
                    Some(false) => true,
                    Some(true) => eval_int(b, manager, arrays, &candidate)
                        .zip(candidate.get(&v))
                        .is_some_and(|(x, y)| x == *y),
                    None => false,
                },
            );
            if truth == Some(true) && definitions_complete {
                *env = candidate;
                return Some(true);
            }
            incomplete = true;
            continue;
        }
        let &(_, lo, hi) = domains.get(position)?;
        if lo <= hi {
            stack.push(Frame::Next {
                position,
                base: candidate,
                value: lo,
                last: hi,
            });
        }
    }
    if incomplete { None } else { Some(false) }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ArrayInterp {
    /// `None` = unknown base (a declared array variable the interpretation
    /// does not constrain). Reads of unwritten indices then have no value,
    /// which propagates as a deferred (`None`) evaluation – Sat-only: a model
    /// can be witnessed when every read hits a written index, but no `Unsat`
    /// may rest on an index the interpretation never wrote. Mirrors v0.3.2's
    /// `nl_eval::Value::Mapping` `read_root` returning `None` for an unknown
    /// root, and the same discipline as `try_model_based_nia_search` (34e854fc).
    default: Option<BigInt>,
    entries: HashMap<i64, BigInt>,
}

#[derive(Clone, Debug)]
struct Interface {
    const_var: TermId,
    array: TermId,
    index: TermId,
}

#[derive(Clone, Debug)]
struct Atom {
    kind: CmpKind,
    lhs: TermId,
    rhs: TermId,
}

#[derive(Clone, Copy, Debug)]
enum CmpKind {
    Eq,
    Le,
    Lt,
    Ge,
    Gt,
}

#[allow(clippy::too_many_arguments)]
fn collect_assertion(
    term: TermId,
    manager: &TermManager,
    arrays: &mut HashMap<TermId, ArrayInterp>,
    interfaces: &mut Vec<Interface>,
    definitions: &mut Vec<(TermId, TermId)>,
    bounds: &mut HashMap<TermId, (Option<i64>, Option<i64>)>,
    atoms: &mut Vec<Atom>,
    bool_atoms: &mut Vec<TermId>,
    free_ints: &mut HashSet<TermId>,
    cond_defs: &mut Vec<(TermId, TermId, TermId)>,
) -> Option<()> {
    let mut stack = vec![term];
    let mut seen = HashSet::new();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermKind::And(args) = &manager.get(term)?.kind {
            stack.extend(args.iter().rev().copied());
        } else {
            collect_atom(
                term,
                manager,
                arrays,
                interfaces,
                definitions,
                bounds,
                atoms,
                bool_atoms,
                free_ints,
                cond_defs,
            )?;
        }
    }
    Some(())
}

#[allow(clippy::too_many_arguments)]
fn collect_atom(
    term: TermId,
    manager: &TermManager,
    arrays: &mut HashMap<TermId, ArrayInterp>,
    interfaces: &mut Vec<Interface>,
    definitions: &mut Vec<(TermId, TermId)>,
    bounds: &mut HashMap<TermId, (Option<i64>, Option<i64>)>,
    atoms: &mut Vec<Atom>,
    bool_atoms: &mut Vec<TermId>,
    free_ints: &mut HashSet<TermId>,
    cond_defs: &mut Vec<(TermId, TermId, TermId)>,
) -> Option<()> {
    let t = manager.get(term)?;
    match &t.kind {
        TermKind::True => Some(()),
        TermKind::Not(_) | TermKind::Or(_) | TermKind::Implies(_, _) => {
            // A conditional definition `Implies(p, (= v body))` with `v` a free
            // integer variable (the encoder lifts non-Bool `ite` into exactly
            // this shape) is recorded separately so the search can derive `v`
            // once `p`'s variables are bound, instead of treating it as an
            // opaque Boolean.  Anything else is a plain Boolean constraint.
            if let TermKind::Implies(p, q) = &t.kind
                && let Some((v, body)) = parse_cond_definition(*q, manager)
            {
                free_ints.insert(v);
                collect_int_vars(*p, manager, free_ints);
                collect_int_vars(body, manager, free_ints);
                cond_defs.push((*p, v, body));
                return Some(());
            }
            // Boolean constraint that must hold (e.g. negated predicates,
            // disjunctions, or non-definitional implications).
            collect_int_vars(term, manager, free_ints);
            bool_atoms.push(term);
            Some(())
        }
        TermKind::Eq(lhs, rhs) => {
            if is_array_sorted(manager, *lhs) || is_array_sorted(manager, *rhs) {
                let (var, def) = if is_array_var(manager, *lhs) {
                    (*lhs, *rhs)
                } else if is_array_var(manager, *rhs) {
                    (*rhs, *lhs)
                } else {
                    return None;
                };
                let value = eval_array_def(def, manager)?;
                if arrays.get(&var).is_some_and(|old| old != &value) {
                    return None;
                }
                arrays.insert(var, value);
                return Some(());
            }
            if let Some(iface) = parse_interface(manager, *lhs, *rhs) {
                interfaces.push(iface);
                return Some(());
            }
            // Definitional equality from nullary define-fun:
            //   P = (* (select A i) (select B i))
            // Bind P when the rhs is evaluable; do not search over P.
            if let Some((v, body)) = parse_definition(manager, *lhs, *rhs) {
                definitions.push((v, body));
                collect_int_vars(body, manager, free_ints);
                return Some(());
            }
            if let Some((v, lo, hi)) = parse_bound_eq(manager, *lhs, *rhs) {
                tighten(bounds, v, lo, hi);
                free_ints.insert(v);
            }
            collect_int_vars(*lhs, manager, free_ints);
            collect_int_vars(*rhs, manager, free_ints);
            atoms.push(Atom {
                kind: CmpKind::Eq,
                lhs: *lhs,
                rhs: *rhs,
            });
            Some(())
        }
        TermKind::Le(a, b) | TermKind::Lt(a, b) | TermKind::Ge(a, b) | TermKind::Gt(a, b) => {
            if let Some((v, lo, hi)) = parse_bound_cmp(manager, term) {
                tighten(bounds, v, lo, hi);
                free_ints.insert(v);
            }
            let kind = match &t.kind {
                TermKind::Le(_, _) => CmpKind::Le,
                TermKind::Lt(_, _) => CmpKind::Lt,
                TermKind::Ge(_, _) => CmpKind::Ge,
                _ => CmpKind::Gt,
            };
            collect_int_vars(*a, manager, free_ints);
            collect_int_vars(*b, manager, free_ints);
            atoms.push(Atom {
                kind,
                lhs: *a,
                rhs: *b,
            });
            Some(())
        }
        _ => None,
    }
}

fn collect_int_vars(term: TermId, manager: &TermManager, out: &mut HashSet<TermId>) {
    let mut stack = vec![term];
    let mut seen = HashSet::new();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let Some(n) = manager.get(id) else { continue };
        match &n.kind {
            TermKind::Var(_) if n.sort == manager.sorts.int_sort => {
                out.insert(id);
            }
            TermKind::Add(xs) | TermKind::Mul(xs) | TermKind::And(xs) | TermKind::Or(xs) => {
                stack.extend(xs.iter().copied())
            }
            TermKind::Neg(a) | TermKind::Not(a) => stack.push(*a),
            TermKind::Sub(a, b)
            | TermKind::Div(a, b)
            | TermKind::Mod(a, b)
            | TermKind::Eq(a, b)
            | TermKind::Le(a, b)
            | TermKind::Lt(a, b)
            | TermKind::Ge(a, b)
            | TermKind::Gt(a, b)
            | TermKind::Select(a, b) => {
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Ite(c, a, b) | TermKind::Store(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Let { bindings, body } => {
                for &(_, v) in bindings.iter() {
                    stack.push(v);
                }
                stack.push(*body);
            }
            TermKind::Apply { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
}

fn ensure_selects_defined(
    term: TermId,
    manager: &TermManager,
    arrays: &HashMap<TermId, ArrayInterp>,
) -> Option<()> {
    let mut stack = vec![term];
    let mut seen = HashSet::new();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let n = manager.get(id)?;
        match &n.kind {
            TermKind::Select(arr, idx) => {
                if !arrays.contains_key(arr) {
                    return None;
                }
                stack.push(*idx);
            }
            TermKind::Add(xs) | TermKind::Mul(xs) => stack.extend(xs.iter().copied()),
            TermKind::Neg(a) | TermKind::Not(a) => stack.push(*a),
            TermKind::Sub(a, b)
            | TermKind::Div(a, b)
            | TermKind::Mod(a, b)
            | TermKind::Eq(a, b)
            | TermKind::Le(a, b)
            | TermKind::Lt(a, b)
            | TermKind::Ge(a, b)
            | TermKind::Gt(a, b) => {
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Let { bindings, body } => {
                for &(_, v) in bindings.iter() {
                    stack.push(v);
                }
                stack.push(*body);
            }
            TermKind::And(xs) | TermKind::Or(xs) => stack.extend(xs.iter().copied()),
            TermKind::Distinct(xs) => stack.extend(xs.iter().copied()),
            TermKind::Implies(a, b) => {
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Var(_) | TermKind::IntConst(_) | TermKind::True | TermKind::False => {}
            _ => return None,
        }
    }
    Some(())
}

/// Build the shared exact, heap-stack evaluator's interpretation. Constant
/// arrays are recognized by the reserved constructor, never by a name substring.
fn interpretation(
    terms: &[TermId],
    manager: &TermManager,
    arrays: &HashMap<TermId, ArrayInterp>,
    env: &HashMap<TermId, BigInt>,
) -> Option<crate::nl_eval::Interpretation> {
    use crate::nl_eval::{Interpretation, Value};
    let mut result = Interpretation::empty();
    for (&term, value) in env {
        result.pin_int(term, value.clone());
    }
    for (&root, array) in arrays {
        for (&index, value) in &array.entries {
            result.pin_cell(
                root,
                BigRational::from_integer(index.into()),
                Value::Num(BigRational::from_integer(value.clone())),
            );
        }
        if let Some(value) = &array.default {
            result.pin_fallback(root, Value::Num(BigRational::from_integer(value.clone())));
        }
    }
    let mut seen = HashSet::new();
    let mut stack: Vec<_> = terms.iter().copied().map(|term| (term, false)).collect();
    while let Some((id, finish)) = stack.pop() {
        let node = manager.get(id)?;
        if finish {
            if let TermKind::Apply { func, args } = &node.kind
                && manager.resolve_str(*func) == nixie_core::reserved::CONST_ARRAY_FUNC
            {
                let [value] = args.as_slice() else {
                    return None;
                };
                let value = crate::nl_eval::evaluate(*value, manager, &result)?;
                result.pin_fallback(id, value);
            }
        } else if seen.insert(id) {
            stack.push((id, true));
            stack.extend(
                nixie_core::ast::traversal::get_children(&node.kind)
                    .into_iter()
                    .map(|child| (child, false)),
            );
        }
    }
    Some(result)
}

pub(crate) fn eval_int(
    term: TermId,
    manager: &TermManager,
    arrays: &HashMap<TermId, ArrayInterp>,
    env: &HashMap<TermId, BigInt>,
) -> Option<BigInt> {
    let interp = interpretation(&[term], manager, arrays, env)?;
    let value = crate::nl_eval::evaluate(term, manager, &interp)?;
    let number = value.as_num()?;
    number.is_integer().then(|| number.to_integer())
}

pub(crate) fn eval_bool(
    term: TermId,
    manager: &TermManager,
    arrays: &HashMap<TermId, ArrayInterp>,
    env: &HashMap<TermId, BigInt>,
) -> Option<bool> {
    let interp = interpretation(&[term], manager, arrays, env)?;
    crate::nl_eval::evaluate(term, manager, &interp)?.as_truth()
}

fn eval_atom(
    atom: &Atom,
    manager: &TermManager,
    arrays: &HashMap<TermId, ArrayInterp>,
    env: &HashMap<TermId, BigInt>,
) -> Option<bool> {
    let l = eval_int(atom.lhs, manager, arrays, env)?;
    let r = eval_int(atom.rhs, manager, arrays, env)?;
    Some(match atom.kind {
        CmpKind::Eq => l == r,
        CmpKind::Le => l <= r,
        CmpKind::Lt => l < r,
        CmpKind::Ge => l >= r,
        CmpKind::Gt => l > r,
    })
}

fn parse_interface(manager: &TermManager, a: TermId, b: TermId) -> Option<Interface> {
    let one = |c, s| {
        let cn = manager.get(c)?;
        let sn = manager.get(s)?;
        if !matches!(cn.kind, TermKind::Var(_)) {
            return None;
        }
        let TermKind::Select(arr, idx) = &sn.kind else {
            return None;
        };
        Some(Interface {
            const_var: c,
            array: *arr,
            index: *idx,
        })
    };
    one(a, b).or_else(|| one(b, a))
}

/// `v = t` where `v` is a variable and `t` is a non-variable evaluable term
/// (nullary define-fun body: product of selects, ite, …).
/// Whether `v` (a variable) occurs anywhere in `term`.
fn term_occurs_var(manager: &TermManager, term: TermId, v: TermId) -> bool {
    let mut stack = vec![term];
    let mut seen = HashSet::new();
    while let Some(id) = stack.pop() {
        if id == v {
            return true;
        }
        if !seen.insert(id) {
            continue;
        }
        let Some(n) = manager.get(id) else { continue };
        match &n.kind {
            TermKind::IntConst(_)
            | TermKind::RealConst(_)
            | TermKind::True
            | TermKind::False
            | TermKind::Var(_) => {}
            TermKind::Neg(a) | TermKind::Not(a) => stack.push(*a),
            TermKind::Add(xs)
            | TermKind::Mul(xs)
            | TermKind::And(xs)
            | TermKind::Or(xs)
            | TermKind::Distinct(xs) => stack.extend(xs.iter().copied()),
            TermKind::Sub(a, b)
            | TermKind::Eq(a, b)
            | TermKind::Le(a, b)
            | TermKind::Lt(a, b)
            | TermKind::Ge(a, b)
            | TermKind::Gt(a, b)
            | TermKind::Implies(a, b) => {
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Let { bindings, body } => {
                for &(_, val) in bindings.iter() {
                    stack.push(val);
                }
                stack.push(*body);
            }
            _ => {
                // Conservatively unreachable for the evaluator's term
                // language; `is_evaluable_arith` has already rejected
                // anything the walkers below cannot read.
            }
        }
    }
    false
}

fn parse_definition(manager: &TermManager, a: TermId, b: TermId) -> Option<(TermId, TermId)> {
    let one = |v, body| {
        as_var(manager, v)?;
        // The defined variable must be INTEGER-sorted: this stage realizes
        // definitions through `eval_int`, so a Boolean-sorted "definition"
        // (`(= b φ)`, the purification interface shape) could never bind —
        // its realization returns `None` at every leaf and the search
        // rejected every candidate (a false `Unsat`).  Boolean interface
        // equalities are the nonlinear grounding's business
        // (`ground_bool_interface_eqs`), not this enumerator's.
        if manager
            .get(v)
            .is_none_or(|n| n.sort != manager.sorts.int_sort)
        {
            return None;
        }
        // Body must not itself be a bare variable or numeral-only (those are
        // ordinary eqs / bounds).
        if as_var(manager, body).is_some() || eval_ground_int(body, manager).is_some() {
            return None;
        }
        // Must be evaluable under a concrete index env (select/ite/mul/…).
        if !is_evaluable_arith(body, manager) {
            return None;
        }
        // Must be ACYCLIC: the defined variable may not occur in the body.
        // `(= (* x x) x)` parses as the "definition" `x := x*x` on its var
        // side; swallowing it removed the constraint from the atom list and
        // skipped `x`'s domain, so the finite-domain search accepted with an
        // EMPTY witness and the printed model defaulted every value (an
        // invalid model behind a correct verdict, 2026-09-10).  A genuine
        // definition never mentions the variable it defines.
        if term_occurs_var(manager, body, v) {
            return None;
        }
        Some((v, body))
    };
    one(a, b).or_else(|| one(b, a))
}

fn is_evaluable_arith(term: TermId, manager: &TermManager) -> bool {
    let mut stack = vec![term];
    let mut seen = HashSet::new();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let Some(n) = manager.get(id) else {
            return false;
        };
        match &n.kind {
            TermKind::IntConst(_) | TermKind::Var(_) => {}
            TermKind::Neg(a) | TermKind::Not(a) => stack.push(*a),
            TermKind::Add(xs) | TermKind::Mul(xs) | TermKind::And(xs) | TermKind::Or(xs) => {
                stack.extend(xs.iter().copied())
            }
            TermKind::Sub(a, b)
            | TermKind::Div(a, b)
            | TermKind::Mod(a, b)
            | TermKind::Eq(a, b)
            | TermKind::Le(a, b)
            | TermKind::Lt(a, b)
            | TermKind::Ge(a, b)
            | TermKind::Gt(a, b)
            | TermKind::Select(a, b) => {
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Let { bindings, body } => {
                for &(_, v) in bindings.iter() {
                    stack.push(v);
                }
                stack.push(*body);
            }
            _ => return false,
        }
    }
    true
}

fn is_array_sorted(manager: &TermManager, t: TermId) -> bool {
    manager.get(t).is_some_and(|n| {
        manager
            .sorts
            .get(n.sort)
            .is_some_and(|s| matches!(s.kind, SortKind::Array { .. }))
    })
}

fn is_array_var(manager: &TermManager, t: TermId) -> bool {
    manager
        .get(t)
        .is_some_and(|n| matches!(n.kind, TermKind::Var(_)) && is_array_sorted(manager, t))
}

pub(crate) fn eval_array_def(term: TermId, manager: &TermManager) -> Option<ArrayInterp> {
    let mut cur = term;
    let mut entries_rev: Vec<(i64, BigInt)> = Vec::new();
    loop {
        let n = manager.get(cur)?;
        match &n.kind {
            TermKind::Store(arr, idx, val) => {
                let i = eval_ground_int(*idx, manager)?;
                let v = eval_int(*val, manager, &HashMap::new(), &HashMap::new())?;
                entries_rev.push((i, v));
                cur = *arr;
            }
            TermKind::Apply { func, args } => {
                let name = manager.resolve_str(*func);
                if name == nixie_core::reserved::CONST_ARRAY_FUNC && args.len() == 1 {
                    let d = eval_int(args[0], manager, &HashMap::new(), &HashMap::new())?;
                    let mut entries = HashMap::new();
                    for (i, v) in entries_rev.into_iter().rev() {
                        entries.insert(i, v);
                    }
                    return Some(ArrayInterp {
                        default: Some(d),
                        entries,
                    });
                }
                return None;
            }
            // A store tower (or bare read) bottoming out at a declared array
            // variable: keep the written entries and mark the base unknown.
            // Read-over-write still resolves written indices; unwritten ones
            // have no value (defer, Sat-only). Mirrors v0.3.2's
            // `nl_eval::Value::Mapping` with an unknown root.
            TermKind::Var(_) => {
                let mut entries = HashMap::new();
                for (i, v) in entries_rev.into_iter().rev() {
                    entries.insert(i, v);
                }
                return Some(ArrayInterp {
                    default: None,
                    entries,
                });
            }
            _ => return None,
        }
    }
}

/// Evaluate a `select` over a store tower at a ground integer index
/// (read-over-write) to a definite integer. Returns `None` when the read
/// hits an unwritten index of an unknown base (a declared array var), or the
/// term is not such a `select` – Sat-only: callers must defer rather than
/// fabricate a value. Used by `nl_model_search` to fold array reads into the
/// arithmetic search (porting v0.3.2's `nl_eval` select handling).
pub(crate) fn eval_select_term(select: TermId, manager: &TermManager) -> Option<BigInt> {
    let t = manager.get(select)?;
    let TermKind::Select(arr, idx) = t.kind else {
        return None;
    };
    let i = eval_ground_int(idx, manager)?;
    let interp = eval_array_def(arr, manager)?;
    interp
        .entries
        .get(&i)
        .cloned()
        .or_else(|| interp.default.clone())
}

pub(crate) fn eval_ground_int(term: TermId, manager: &TermManager) -> Option<i64> {
    eval_int(term, manager, &HashMap::new(), &HashMap::new())?.to_i64()
}

fn parse_bound_eq(
    manager: &TermManager,
    lhs: TermId,
    rhs: TermId,
) -> Option<(TermId, Option<i64>, Option<i64>)> {
    if let (Some(v), Some(k)) = (as_var(manager, lhs), eval_ground_int(rhs, manager)) {
        return Some((v, Some(k), Some(k)));
    }
    if let (Some(v), Some(k)) = (as_var(manager, rhs), eval_ground_int(lhs, manager)) {
        return Some((v, Some(k), Some(k)));
    }
    None
}

fn parse_bound_cmp(
    manager: &TermManager,
    term: TermId,
) -> Option<(TermId, Option<i64>, Option<i64>)> {
    let n = manager.get(term)?;
    match &n.kind {
        TermKind::Ge(a, b) => {
            if let (Some(v), Some(k)) = (as_var(manager, *a), eval_ground_int(*b, manager)) {
                return Some((v, Some(k), None));
            }
        }
        TermKind::Gt(a, b) => {
            if let (Some(v), Some(k)) = (as_var(manager, *a), eval_ground_int(*b, manager)) {
                return Some((v, Some(k.checked_add(1)?), None));
            }
        }
        TermKind::Le(a, b) => {
            if let (Some(v), Some(k)) = (as_var(manager, *a), eval_ground_int(*b, manager)) {
                return Some((v, None, Some(k)));
            }
        }
        TermKind::Lt(a, b) => {
            if let (Some(v), Some(k)) = (as_var(manager, *a), eval_ground_int(*b, manager)) {
                return Some((v, None, Some(k.checked_sub(1)?)));
            }
        }
        _ => {}
    }
    None
}

fn as_var(manager: &TermManager, t: TermId) -> Option<TermId> {
    manager
        .get(t)
        .and_then(|n| matches!(n.kind, TermKind::Var(_)).then_some(t))
}

/// Parse `Implies(p, q)` conclusion `q` as a definitional equality `(= v body)`
/// with `v` a free integer variable (either side). Returns `(v, body)`.
/// This is the shape produced when the encoder lifts a non-Bool `ite` term to
/// a fresh constant plus guarded equalities.
fn parse_cond_definition(q: TermId, manager: &TermManager) -> Option<(TermId, TermId)> {
    let n = manager.get(q)?;
    let TermKind::Eq(a, b) = &n.kind else {
        return None;
    };
    let a_var = as_var(manager, *a);
    let b_var = as_var(manager, *b);
    match (a_var, b_var) {
        (Some(v), None) => {
            // Acyclicity, same as `parse_definition`: a conditional
            // "definition" whose body mentions the variable it defines is a
            // constraint, not a definition.
            if term_occurs_var(manager, *b, v) {
                return None;
            }
            Some((v, *b))
        }
        (None, Some(v)) => {
            if term_occurs_var(manager, *a, v) {
                return None;
            }
            Some((v, *a))
        }
        _ => None,
    }
}

/// `true` iff `term` mentions a free Boolean-sorted variable. The finite-domain
/// searches enumerate only integer variables, so a Boolean variable that an
/// atom, a Boolean constraint, or an encoder-lifted-`ite` guard depends on can
/// neither be pinned nor refuted – its dependent term stays unbound and would
/// be silently satisfied. Callers must refuse to decide in that case.
fn references_free_bool_var(term: TermId, manager: &TermManager) -> bool {
    let mut stack = vec![term];
    let mut seen = HashSet::new();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let Some(n) = manager.get(id) else { continue };
        match &n.kind {
            TermKind::Var(_) => {
                if n.sort == manager.sorts.bool_sort {
                    return true;
                }
            }
            TermKind::Neg(a) | TermKind::Not(a) => stack.push(*a),
            TermKind::Add(xs) | TermKind::Mul(xs) | TermKind::And(xs) | TermKind::Or(xs) => {
                stack.extend(xs.iter().copied());
            }
            TermKind::Distinct(xs) => stack.extend(xs.iter().copied()),
            TermKind::Sub(a, b)
            | TermKind::Eq(a, b)
            | TermKind::Le(a, b)
            | TermKind::Lt(a, b)
            | TermKind::Ge(a, b)
            | TermKind::Gt(a, b)
            | TermKind::Implies(a, b) => {
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Let { bindings, body } => {
                for &(_, v) in bindings.iter() {
                    stack.push(v);
                }
                stack.push(*body);
            }
            _ => {}
        }
    }
    false
}

fn tighten(
    bounds: &mut HashMap<TermId, (Option<i64>, Option<i64>)>,
    v: TermId,
    lo: Option<i64>,
    hi: Option<i64>,
) {
    let e = bounds.entry(v).or_insert((None, None));
    if let Some(l) = lo {
        e.0 = Some(e.0.map_or(l, |x| x.max(l)));
    }
    if let Some(h) = hi {
        e.1 = Some(e.1.map_or(h, |x| x.min(h)));
    }
}

/// True if any assertion contains a `store`.
pub fn assertions_contain_store(assertions: &[TermId], manager: &TermManager) -> bool {
    assertions.iter().any(|&a| term_contains_store(a, manager))
}

fn term_contains_store(term: TermId, manager: &TermManager) -> bool {
    let mut stack = vec![term];
    let mut seen = HashSet::new();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let Some(n) = manager.get(id) else { continue };
        match &n.kind {
            TermKind::Store(_, _, _) => return true,
            TermKind::And(xs) | TermKind::Or(xs) | TermKind::Add(xs) | TermKind::Mul(xs) => {
                stack.extend(xs.iter().copied())
            }
            TermKind::Eq(a, b)
            | TermKind::Le(a, b)
            | TermKind::Lt(a, b)
            | TermKind::Ge(a, b)
            | TermKind::Gt(a, b)
            | TermKind::Sub(a, b)
            | TermKind::Select(a, b) => {
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Neg(a) | TermKind::Not(a) => stack.push(*a),
            TermKind::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Apply { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    false
}

/// Concretely evaluate every assertion under an environment of integer
/// values; `true` only when *all* of them evaluate to `Some(true)`.
///
/// Public verification helper shared by the nonlinear dispatch stages: a
/// candidate model is a sound `Sat` witness exactly when this returns
/// `true` (an assertion that cannot be evaluated is *not* satisfied –
/// the caller must treat the model as unverified).
#[must_use]
pub fn eval_assertions_true(
    assertions: &[TermId],
    manager: &TermManager,
    env: &HashMap<TermId, BigInt>,
) -> bool {
    let arrays: HashMap<TermId, ArrayInterp> = HashMap::new();
    assertions
        .iter()
        .all(|&a| eval_bool(a, manager, &arrays, env).unwrap_or(false))
}

#[cfg(test)]
mod publication_regressions {
    use super::*;

    #[allow(clippy::too_many_arguments)]
    fn search(
        manager: &TermManager,
        domains: &[(TermId, i64, i64)],
        interfaces: &[Interface],
        definitions: &[(TermId, TermId)],
        conditional: &[(TermId, TermId, TermId)],
        atoms: &[Atom],
        arrays: &HashMap<TermId, ArrayInterp>,
    ) -> (Option<bool>, HashMap<TermId, BigInt>) {
        let mut env = HashMap::new();
        let answer = search_rec(
            0,
            domains,
            interfaces,
            definitions,
            conditional,
            atoms,
            &[],
            arrays,
            manager,
            &mut env,
            &mut 0,
        );
        (answer, env)
    }

    #[test]
    fn sibling_assignments_recompute_derived_values() {
        let mut tm = TermManager::new();
        let x = tm.mk_var("x", tm.sorts.int_sort);
        let y = tm.mk_var("y", tm.sorts.int_sort);
        let one = tm.mk_int(1);
        let two = tm.mk_int(2);
        let next = tm.mk_add(vec![x, one]);
        let (answer, env) = search(
            &tm,
            &[(x, 0, 1)],
            &[],
            &[(y, next)],
            &[],
            &[Atom {
                kind: CmpKind::Eq,
                lhs: y,
                rhs: two,
            }],
            &HashMap::new(),
        );
        assert_eq!(answer, Some(true));
        assert_eq!(env.get(&x), Some(&BigInt::from(1)));
        assert_eq!(env.get(&y), Some(&BigInt::from(2)));
    }

    #[test]
    fn unresolved_atoms_and_zero_division_are_not_verdicts() {
        let mut tm = TermManager::new();
        let y = tm.mk_var("y", tm.sorts.int_sort);
        let zero = tm.mk_int(0);
        let one = tm.mk_int(1);
        let guard = tm.mk_false();
        let atom = Atom {
            kind: CmpKind::Eq,
            lhs: y,
            rhs: one,
        };
        assert_eq!(
            search(
                &tm,
                &[],
                &[],
                &[],
                &[(guard, y, zero)],
                &[atom],
                &HashMap::new()
            )
            .0,
            None
        );
        let division = tm.mk_div(one, zero);
        let atom = Atom {
            kind: CmpKind::Ge,
            lhs: division,
            rhs: zero,
        };
        assert_eq!(
            search(&tm, &[], &[], &[], &[], &[atom], &HashMap::new()).0,
            None
        );
    }

    #[test]
    fn conflicting_definitions_and_interfaces_are_checked() {
        let mut tm = TermManager::new();
        let y = tm.mk_var("y", tm.sorts.int_sort);
        let zero = tm.mk_int(0);
        let one = tm.mk_int(1);
        let yes = tm.mk_true();
        assert_eq!(
            search(
                &tm,
                &[],
                &[],
                &[(y, zero), (y, one)],
                &[],
                &[],
                &HashMap::new()
            )
            .0,
            Some(false)
        );
        assert_eq!(
            search(
                &tm,
                &[],
                &[],
                &[],
                &[(yes, y, zero), (yes, y, one)],
                &[],
                &HashMap::new()
            )
            .0,
            Some(false)
        );
        let sort = tm.sorts.array(tm.sorts.int_sort, tm.sorts.int_sort);
        let array = tm.mk_var("a", sort);
        let arrays = HashMap::from([(
            array,
            ArrayInterp {
                default: Some(1.into()),
                entries: HashMap::new(),
            },
        )]);
        let interface = Interface {
            const_var: y,
            array,
            index: zero,
        };
        assert_eq!(
            search(&tm, &[], &[interface], &[(y, zero)], &[], &[], &arrays).0,
            Some(false)
        );
    }

    #[test]
    fn array_definitions_do_not_overwrite_or_guess_constructor_names() {
        let mut tm = TermManager::new();
        let sort = tm.sorts.array(tm.sorts.int_sort, tm.sorts.int_sort);
        let array = tm.mk_var("a", sort);
        let zero = tm.mk_int(0);
        let one = tm.mk_int(1);
        let a0 = tm.mk_apply(nixie_core::reserved::CONST_ARRAY_FUNC, vec![zero], sort);
        let a1 = tm.mk_apply(nixie_core::reserved::CONST_ARRAY_FUNC, vec![one], sort);
        let first = tm.mk_eq(array, a0);
        let second = tm.mk_eq(array, a1);
        let read = tm.mk_select(array, zero);
        let atom = tm.mk_eq(read, one);
        assert!(try_decide_ground_ania(&[first, second, atom], &tm).is_none());
        let fake = tm.mk_apply("user_constant", vec![one], sort);
        assert!(eval_array_def(fake, &tm).is_none());
    }

    #[test]
    fn exact_values_and_large_indices_survive_array_evaluation() {
        let mut tm = TermManager::new();
        let sort = tm.sorts.array(tm.sorts.int_sort, tm.sorts.int_sort);
        let big: BigInt = BigInt::from(1) << 130;
        let value = tm.mk_int(big.clone());
        let array = tm.mk_apply(nixie_core::reserved::CONST_ARRAY_FUNC, vec![value], sort);
        let read = tm.mk_select(array, value);
        assert_eq!(
            eval_int(read, &tm, &HashMap::new(), &HashMap::new()),
            Some(big.clone())
        );
        assert_eq!(
            eval_array_def(array, &tm).and_then(|a| a.default),
            Some(big)
        );
        let high = tm.mk_int(i64::MAX);
        let x = tm.mk_var("x", tm.sorts.int_sort);
        let above = tm.mk_gt(x, high);
        assert!(parse_bound_cmp(&tm, above).is_none());
        let low = tm.mk_int(i64::MIN);
        let below = tm.mk_lt(x, low);
        assert!(parse_bound_cmp(&tm, below).is_none());
    }

    #[test]
    fn deep_integer_evaluation_uses_the_heap() {
        std::thread::Builder::new()
            .stack_size(1024 * 1024)
            .spawn(|| {
                let mut tm = TermManager::new();
                let x = tm.mk_var("x", tm.sorts.int_sort);
                let one = tm.mk_int(1);
                let mut term = x;
                for _ in 0..20_000 {
                    term = tm.mk_sub(term, one);
                }
                let env = HashMap::from([(x, BigInt::from(20_000))]);
                assert_eq!(eval_int(term, &tm, &HashMap::new(), &env), Some(0.into()));
            })
            .expect("thread")
            .join()
            .expect("heap evaluation");
    }
}
