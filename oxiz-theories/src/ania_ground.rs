//! Ground QF_ANIA decision for constant store-chains + finite index boxes.
//!
//! Works on **purified** assertions:
//! - `A = store(... (as const) d ...)` array definitions
//! - `c = select(A, i)` interface equalities from arithmetic purification
//! - pure arithmetic on `c` and index vars
//!
//! Free selects (no store def) are out of scope here — pure NIA on interface
//! constants remains sound for those.

use crate::nlsat::NlDispatchResult;
use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::sort::SortKind;
use std::collections::{HashMap, HashSet};

const MAX_INDEX_PRODUCT: u64 = 50_000;

/// Try to decide ground store + bounded-index ANIA (post-purification shape).
pub fn try_decide_ground_ania(
    assertions: &[TermId],
    manager: &TermManager,
) -> Option<NlDispatchResult> {
    let mut arrays: HashMap<TermId, ArrayInterp> = HashMap::new();
    let mut interfaces: Vec<Interface> = Vec::new(); // c = select(A, idx)
    let mut bounds: HashMap<TermId, (Option<i64>, Option<i64>)> = HashMap::new();
    let mut arith_atoms: Vec<ArithAtom> = Vec::new();

    for &a in assertions {
        collect_assertion(
            a,
            manager,
            &mut arrays,
            &mut interfaces,
            &mut bounds,
            &mut arith_atoms,
        )?;
    }

    if arrays.is_empty() || interfaces.is_empty() || arith_atoms.is_empty() {
        return None;
    }

    // Every interface select must read a defined array; index must be var or numeral.
    let mut index_vars: Vec<TermId> = Vec::new();
    for iface in &interfaces {
        if !arrays.contains_key(&iface.array) {
            return None;
        }
        if let Some(v) = as_var(manager, iface.index) {
            if !index_vars.contains(&v) {
                index_vars.push(v);
            }
        } else if eval_ground_int(iface.index, manager).is_none() {
            return None;
        }
    }

    let mut domains: Vec<(TermId, i64, i64)> = Vec::new();
    let mut product: u64 = 1;
    for &v in &index_vars {
        let (lo, hi) = bounds.get(&v).copied().unwrap_or((None, None));
        let lo = lo?;
        let hi = hi?;
        if hi < lo {
            return Some(NlDispatchResult::Unsat);
        }
        let w = (hi - lo + 1) as u64;
        product = product.saturating_mul(w);
        if product > MAX_INDEX_PRODUCT {
            return None;
        }
        domains.push((v, lo, hi));
    }

    let mut idxs: Vec<i64> = domains.iter().map(|(_, lo, _)| *lo).collect();
    loop {
        let mut env: HashMap<TermId, BigInt> = HashMap::new();
        for (i, &(v, _, _)) in domains.iter().enumerate() {
            env.insert(v, BigInt::from(idxs[i]));
        }
        // Realize each interface const via store evaluation.
        let mut ok = true;
        for iface in &interfaces {
            let idx_val = if let Some(v) = as_var(manager, iface.index) {
                env.get(&v).cloned().ok_or(())
            } else {
                eval_ground_int(iface.index, manager)
                    .map(BigInt::from)
                    .ok_or(())
            };
            let Ok(idx_val) = idx_val else {
                ok = false;
                break;
            };
            let Some(i64v) = idx_val.to_i64() else {
                ok = false;
                break;
            };
            let interp = &arrays[&iface.array];
            let sel = interp
                .entries
                .get(&i64v)
                .cloned()
                .unwrap_or_else(|| interp.default.clone());
            env.insert(iface.const_var, sel);
        }
        if ok {
            let mut cache = HashMap::new();
            let mut all_hold = true;
            for atom in &arith_atoms {
                if !eval_atom(atom, manager, &env, &mut cache) {
                    all_hold = false;
                    break;
                }
            }
            if all_hold {
                return Some(NlDispatchResult::Sat);
            }
        }

        if domains.is_empty() {
            return Some(NlDispatchResult::Unsat);
        }
        let mut pos = 0;
        loop {
            if pos >= domains.len() {
                return Some(NlDispatchResult::Unsat);
            }
            idxs[pos] += 1;
            if idxs[pos] <= domains[pos].2 {
                break;
            }
            idxs[pos] = domains[pos].1;
            pos += 1;
        }
    }
}

#[derive(Clone, Debug)]
struct ArrayInterp {
    default: BigInt,
    entries: HashMap<i64, BigInt>,
}

#[derive(Clone, Debug)]
struct Interface {
    const_var: TermId,
    array: TermId,
    index: TermId,
}

#[derive(Clone, Debug)]
struct ArithAtom {
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

fn collect_assertion(
    term: TermId,
    manager: &TermManager,
    arrays: &mut HashMap<TermId, ArrayInterp>,
    interfaces: &mut Vec<Interface>,
    bounds: &mut HashMap<TermId, (Option<i64>, Option<i64>)>,
    atoms: &mut Vec<ArithAtom>,
) -> Option<()> {
    let t = manager.get(term)?;
    match &t.kind {
        TermKind::And(args) => {
            for &a in args {
                collect_assertion(a, manager, arrays, interfaces, bounds, atoms)?;
            }
            Some(())
        }
        TermKind::True => Some(()),
        TermKind::Eq(lhs, rhs) => {
            if is_array_sorted(manager, *lhs) || is_array_sorted(manager, *rhs) {
                let (var, def) = if is_array_var(manager, *lhs) {
                    (*lhs, *rhs)
                } else if is_array_var(manager, *rhs) {
                    (*rhs, *lhs)
                } else {
                    return None;
                };
                let interp = eval_array_def(def, manager)?;
                arrays.insert(var, interp);
                return Some(());
            }
            if let Some(iface) = parse_interface(manager, *lhs, *rhs) {
                interfaces.push(iface);
                return Some(());
            }
            if let Some((v, lo, hi)) = parse_bound_eq(manager, *lhs, *rhs) {
                tighten(bounds, v, lo, hi);
                return Some(());
            }
            // Pure arith equality (may mention purified consts / mul).
            if is_pure_arith_term(*lhs, manager) && is_pure_arith_term(*rhs, manager) {
                atoms.push(ArithAtom {
                    kind: CmpKind::Eq,
                    lhs: *lhs,
                    rhs: *rhs,
                });
                return Some(());
            }
            None
        }
        TermKind::Le(a, b) | TermKind::Lt(a, b) | TermKind::Ge(a, b) | TermKind::Gt(a, b) => {
            if let Some((v, lo, hi)) = parse_bound_cmp(manager, term) {
                tighten(bounds, v, lo, hi);
                // Bounds on purified select-consts are also arith atoms.
                if !as_var(manager, *a).is_some_and(|v| {
                    // index var bounds only — already recorded
                    interfaces.iter().all(|i| i.const_var != v)
                }) {
                    // if lhs is interface const, keep as atom
                }
            }
            let kind = match &t.kind {
                TermKind::Le(_, _) => CmpKind::Le,
                TermKind::Lt(_, _) => CmpKind::Lt,
                TermKind::Ge(_, _) => CmpKind::Ge,
                _ => CmpKind::Gt,
            };
            // Always keep numeric comparisons as atoms when both sides pure arith
            // (includes bounds on select-consts like (>= c 1)).
            if is_pure_arith_term(*a, manager) && is_pure_arith_term(*b, manager) {
                // Skip pure index-var bounds already in `bounds` map (optional).
                // Keeping them as atoms is fine and simpler.
                atoms.push(ArithAtom {
                    kind,
                    lhs: *a,
                    rhs: *b,
                });
                return Some(());
            }
            None
        }
        _ => None,
    }
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

fn is_pure_arith_term(term: TermId, manager: &TermManager) -> bool {
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
            TermKind::Neg(a) => stack.push(*a),
            TermKind::Add(xs) | TermKind::Mul(xs) => stack.extend(xs.iter().copied()),
            TermKind::Sub(a, b) | TermKind::Div(a, b) | TermKind::Mod(a, b) => {
                stack.push(*a);
                stack.push(*b);
            }
            // No select/apply/store/ite in pure arith after purification.
            _ => return false,
        }
    }
    true
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

fn eval_array_def(term: TermId, manager: &TermManager) -> Option<ArrayInterp> {
    let mut cur = term;
    let mut entries_rev: Vec<(i64, BigInt)> = Vec::new();
    loop {
        let n = manager.get(cur)?;
        match &n.kind {
            TermKind::Store(arr, idx, val) => {
                let i = eval_ground_int(*idx, manager)?;
                let v = eval_ground_int(*val, manager)?;
                entries_rev.push((i, BigInt::from(v)));
                cur = *arr;
            }
            TermKind::Apply { func, args } => {
                let name = manager.resolve_str(*func);
                if name.contains("const") && args.len() == 1 {
                    let d = eval_ground_int(args[0], manager)?;
                    let mut entries = HashMap::new();
                    for (i, v) in entries_rev.into_iter().rev() {
                        entries.insert(i, v);
                    }
                    return Some(ArrayInterp {
                        default: BigInt::from(d),
                        entries,
                    });
                }
                return None;
            }
            _ => return None,
        }
    }
}

fn eval_ground_int(term: TermId, manager: &TermManager) -> Option<i64> {
    let n = manager.get(term)?;
    match &n.kind {
        TermKind::IntConst(k) => k.to_i64(),
        TermKind::Neg(inner) => Some(-eval_ground_int(*inner, manager)?),
        _ => None,
    }
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
                return Some((v, Some(k + 1), None));
            }
        }
        TermKind::Le(a, b) => {
            if let (Some(v), Some(k)) = (as_var(manager, *a), eval_ground_int(*b, manager)) {
                return Some((v, None, Some(k)));
            }
        }
        TermKind::Lt(a, b) => {
            if let (Some(v), Some(k)) = (as_var(manager, *a), eval_ground_int(*b, manager)) {
                return Some((v, None, Some(k - 1)));
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

fn eval_term(
    term: TermId,
    manager: &TermManager,
    env: &HashMap<TermId, BigInt>,
    cache: &mut HashMap<TermId, BigInt>,
) -> Option<BigInt> {
    if let Some(v) = cache.get(&term) {
        return Some(v.clone());
    }
    if let Some(v) = env.get(&term) {
        return Some(v.clone());
    }
    let n = manager.get(term)?;
    let val = match &n.kind {
        TermKind::IntConst(k) => k.clone(),
        TermKind::Neg(a) => -eval_term(*a, manager, env, cache)?,
        TermKind::Add(xs) => {
            let mut s = BigInt::zero();
            for &x in xs {
                s += eval_term(x, manager, env, cache)?;
            }
            s
        }
        TermKind::Mul(xs) => {
            let mut p = BigInt::from(1);
            for &x in xs {
                p *= eval_term(x, manager, env, cache)?;
            }
            p
        }
        TermKind::Sub(a, b) => {
            eval_term(*a, manager, env, cache)? - eval_term(*b, manager, env, cache)?
        }
        TermKind::Var(_) => return None,
        _ => return None,
    };
    cache.insert(term, val.clone());
    Some(val)
}

fn eval_atom(
    atom: &ArithAtom,
    manager: &TermManager,
    env: &HashMap<TermId, BigInt>,
    cache: &mut HashMap<TermId, BigInt>,
) -> bool {
    let Some(l) = eval_term(atom.lhs, manager, env, cache) else {
        return false;
    };
    let Some(r) = eval_term(atom.rhs, manager, env, cache) else {
        return false;
    };
    match atom.kind {
        CmpKind::Eq => l == r,
        CmpKind::Le => l <= r,
        CmpKind::Lt => l < r,
        CmpKind::Ge => l >= r,
        CmpKind::Gt => l > r,
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
