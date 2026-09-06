//! Iterative ground-constant folding (the "encode-depth rescue" pass).
//!
//! `fold_ground` collapses every *fully ground* arithmetic/Boolean
//! subterm of `term` to its constant value, so that trivially-foldable
//! inputs are never measured — and refused — at their unfolded structural
//! depth by the encode-depth guard (see `nixie-solver`'s
//! `ENCODE_DEPTH_LIMIT` and the deep-nesting finding in
//! `bench/obligation/README.md`).
//!
//! # Cost contract
//!
//! * One explicit-stack post-order walk, memoized per unique `TermId`:
//!   linear in the number of *unique* DAG nodes (sublinear in the expanded
//!   tree whenever the input shares subterms), zero native recursion —
//!   stack-safe on arbitrarily deep input.
//! * One final [`TermManager::substitute`] (itself iterative and
//!   capture-avoiding) rebuilds every ancestor of a collapsed node in a
//!   single pass. There is deliberately no per-`TermKind` rebuild match
//!   here: `substitute` is the single exhaustive rebuild primitive, and a
//!   parallel match is a soundness hazard (see `map_terms`'s doc for the
//!   history of `transform_children`).
//!
//! # Semantics contract
//!
//! In addition to ground collapse, associative chains are *normalized*:
//! same-operator, same-sort children are spliced flat and their constants
//! combined exactly — Int sums/products in `BigInt`, Real sums via checked
//! `Rational64` (on overflow the partial sum is kept and later constants
//! stay as arguments — same value, no loss), and wraparound BV
//! `xor`/`add`/`mul` in exact modular arithmetic.  A 5 000-deep constant
//! `bvxor` chain over a variable collapses to `x ⊕ C`; `(+ 1 (+ 1 … x))`
//! becomes `(+ C x)`.
//!
//! * Integer folding is exact and unbounded (`BigInt`), which is *more*
//!   precise than the `i64`-backed [`crate::rewrite::arith`] rules.
//! * Rational folding is `Rational64` with checked arithmetic; any
//!   operation that would overflow leaves the node unfolded (the same
//!   honest-skip policy as `ArithRewriter`), never a wrapped constant.
//! * Partial operations stay unfolded: division/modulo by zero is left
//!   for the theory solvers to blame.
//! * `div`/`mod` on integers follow SMT-LIB Euclidean semantics
//!   (`0 <= r < |b|`).
//! * Binder bodies (`Forall`/`Exists`/`Let`/`Match`) are not descended
//!   into. Ground subterms are binder-independent, so folding there would
//!   be sound, but assert-time input has already been let-expanded and is
//!   quantifier-treated elsewhere; the conservative skip keeps this pass
//!   out of binder bookkeeping entirely.
//! * Only *total* constant-valued shortcuts fire (e.g. `and(false, x)`);
//!   structure-changing simplifications (dropping a `true` from an `and`)
//!   are left to the main simplifier, which runs once the term is known
//!   to be shallow.

use crate::ast::bv_fold::{bv_add, bv_wrap_unsigned};
use crate::ast::traversal::get_children;
use crate::ast::{TermId, TermKind, TermManager};
use crate::prelude::FxHashMap;
use crate::sort::Sort;
use num_bigint::BigInt;
use num_rational::Rational64;
use num_traits::{CheckedAdd, CheckedDiv, CheckedMul, One, Signed, Zero};
use smallvec::SmallVec;

/// Collapse all fully-ground arithmetic/Boolean subterms of `term` to
/// constants. Returns `term` unchanged when nothing folds.
pub fn fold_ground(term: TermId, manager: &mut TermManager) -> TermId {
    // Folded form of every visited node (== the node itself when it does
    // not collapse). Shared DAG nodes are folded exactly once.
    let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
    // Only the nodes that actually collapsed, for the single rebuild.
    let mut pairs: FxHashMap<TermId, TermId> = FxHashMap::default();
    let mut stack: Vec<TermId> = vec![term];
    while let Some(&top) = stack.last() {
        if memo.contains_key(&top) {
            stack.pop();
            continue;
        }
        let Some(node) = manager.get(top).cloned() else {
            stack.pop();
            continue;
        };
        if matches!(
            node.kind,
            TermKind::Forall { .. }
                | TermKind::Exists { .. }
                | TermKind::Let { .. }
                | TermKind::Match { .. }
        ) {
            // Leave binder bodies untouched (see module docs).
            memo.insert(top, top);
            stack.pop();
            continue;
        }
        let kids = get_children(&node.kind);
        let mut pushed = false;
        for &c in kids.iter() {
            if !memo.contains_key(&c) {
                stack.push(c);
                pushed = true;
            }
        }
        if pushed {
            continue;
        }
        let folded_kids: SmallVec<[TermId; 4]> = kids.iter().map(|&c| memo[&c]).collect();
        let folded = fold_node(&node.kind, node.sort, &folded_kids, manager);
        let new_id = folded.unwrap_or(top);
        memo.insert(top, new_id);
        if new_id != top {
            pairs.insert(top, new_id);
        }
        stack.pop();
    }
    if pairs.is_empty() {
        term
    } else {
        manager.substitute(term, &pairs)
    }
}

/// SMT-LIB Euclidean division on `BigInt`: quotient/remainder with the
/// remainder in `[0, |b|)` (implemented on inherent ops — the
/// `num-integer` trait is not uniformly in scope for `BigInt` here).
fn big_div_euclid(a: &BigInt, b: &BigInt) -> BigInt {
    let mut q = a / b;
    let mut r = a - &q * b;
    if r.sign() == num_bigint::Sign::Minus {
        if b.sign() == num_bigint::Sign::Plus {
            q -= 1;
        } else {
            q += 1;
        }
        r += b.abs();
    }
    let _ = &mut r;
    q
}

fn big_rem_euclid(a: &BigInt, b: &BigInt) -> BigInt {
    let mut r = a - &(a / b) * b;
    if r.sign() == num_bigint::Sign::Minus {
        r += b.abs();
    }
    r
}

fn int_val(kid: TermId, manager: &TermManager) -> Option<BigInt> {
    match &manager.get(kid)?.kind {
        TermKind::IntConst(n) => Some(n.clone()),
        _ => None,
    }
}

fn rat_val(kid: TermId, manager: &TermManager) -> Option<Rational64> {
    match &manager.get(kid)?.kind {
        TermKind::IntConst(n) => {
            let v: i64 = n.try_into().ok()?;
            Some(Rational64::from_integer(v))
        }
        TermKind::RealConst(r) => Some(*r),
        _ => None,
    }
}

fn as_int(kid: TermId, manager: &TermManager) -> Option<&BigInt> {
    match &manager.get(kid)?.kind {
        TermKind::IntConst(n) => Some(n),
        _ => None,
    }
}

/// Rational view of a constant child (Int constants coerced when they fit
/// `i64`; the honest-skip policy of `ArithRewriter`).
fn as_rat(kid: TermId, manager: &TermManager) -> Option<Rational64> {
    match &manager.get(kid)?.kind {
        TermKind::IntConst(n) => {
            let v: i64 = n.try_into().ok()?;
            Some(Rational64::from_integer(v))
        }
        TermKind::RealConst(r) => Some(*r),
        _ => None,
    }
}

fn as_bool(kid: TermId, manager: &TermManager) -> Option<bool> {
    match &manager.get(kid)?.kind {
        TermKind::True => Some(true),
        TermKind::False => Some(false),
        _ => None,
    }
}

fn sort_is(
    manager: &TermManager,
    sort: crate::sort::SortId,
    f: fn(&crate::sort::Sort) -> bool,
) -> bool {
    manager.sorts.get(sort).is_some_and(f)
}

/// Exact equality of two *constant* children. Mixed Int/Real pairs are
/// decidable without any coercion: a `Rational64` equals an integer `n`
/// only when its denominator is 1, and then its numerator (bounded by
/// `i64::MAX` in magnitude) can be compared against `n` exactly.
fn consts_equal(a: TermId, b: TermId, manager: &TermManager) -> Option<bool> {
    let na = manager.get(a)?;
    let nb = manager.get(b)?;
    match (&na.kind, &nb.kind) {
        (TermKind::IntConst(x), TermKind::IntConst(y)) => Some(x == y),
        (TermKind::RealConst(x), TermKind::RealConst(y)) => Some(x == y),
        (TermKind::IntConst(n), TermKind::RealConst(r))
        | (TermKind::RealConst(r), TermKind::IntConst(n)) => {
            if *r.denom() == 1 {
                Some(n == &BigInt::from(*r.numer()))
            } else {
                // A non-integer rational is never equal to an integer.
                Some(false)
            }
        }
        (TermKind::True, TermKind::True) | (TermKind::False, TermKind::False) => Some(true),
        (TermKind::True, TermKind::False) | (TermKind::False, TermKind::True) => Some(false),
        _ => None,
    }
}

fn compare_nums(a: TermId, b: TermId, manager: &TermManager) -> Option<std::cmp::Ordering> {
    let na = manager.get(a)?;
    let nb = manager.get(b)?;
    match (&na.kind, &nb.kind) {
        (TermKind::IntConst(x), TermKind::IntConst(y)) => Some(x.cmp(y)),
        _ => {
            let x = as_rat(a, manager)?;
            let y = as_rat(b, manager)?;
            Some(x.cmp(&y))
        }
    }
}

/// Fold one node whose children are already folded (`kids` holds their
/// folded ids). Returns `None` when the node does not collapse to a
/// constant-valued term.
fn fold_node(
    kind: &TermKind,
    sort: crate::sort::SortId,
    kids: &[TermId],
    manager: &mut TermManager,
) -> Option<TermId> {
    match kind {
        TermKind::Add(_) => {
            // Associative-chain normalization: splice same-op, same-sort
            // children into one flat argument list, then combine the
            // constants exactly.  This subsumes the fully-ground collapse
            // and additionally rescues chains with a variable base —
            // `(+ 1 (+ 1 … x))` normalizes to `(+ 600 x)` — so the
            // encode-depth guard measures the *normalized* term, not the
            // unfolded chain.
            let is_int = sort_is(manager, sort, Sort::is_int);
            let disc = std::mem::discriminant(kind);
            let mut flat: Vec<TermId> = Vec::with_capacity(kids.len());
            let mut spliced = false;
            for &k in kids {
                let child = manager
                    .get(k)
                    .filter(|n| std::mem::discriminant(&n.kind) == disc && n.sort == sort);
                if let Some(TermKind::Add(cs)) = child.map(|n| &n.kind) {
                    flat.extend_from_slice(cs);
                    spliced = true;
                } else {
                    flat.push(k);
                }
            }
            let mut non_const: Vec<TermId> = Vec::with_capacity(flat.len());
            let mut int_sum = BigInt::from(0);
            let mut rat_sum = Rational64::zero();
            let mut rat_overflow = false;
            let mut const_count = 0usize;
            for &k in flat.iter() {
                if is_int {
                    if let Some(v) = int_val(k, manager) {
                        int_sum += v;
                        const_count += 1;
                        continue;
                    }
                } else if !rat_overflow && let Some(v) = rat_val(k, manager) {
                    // Real: checked combine; on overflow keep the partial
                    // sum as one constant and stop combining (the remaining
                    // constants stay as arguments — same value, no loss).
                    match rat_sum.checked_add(&v) {
                        Some(s) => {
                            rat_sum = s;
                            const_count += 1;
                            continue;
                        }
                        None => rat_overflow = true,
                    }
                }
                non_const.push(k);
            }
            if const_count == flat.len() && !flat.is_empty() {
                // Fully ground: the exact constant.
                if is_int {
                    Some(manager.mk_int(int_sum))
                } else {
                    Some(manager.mk_real(rat_sum))
                }
            } else {
                let mut args = non_const;
                if is_int {
                    if !int_sum.is_zero() || args.is_empty() {
                        args.push(manager.mk_int(int_sum));
                    }
                } else if !rat_sum.is_zero() || args.is_empty() {
                    args.push(manager.mk_real(rat_sum));
                }
                if args.len() == 1 {
                    return Some(args[0]);
                }
                let unchanged = !spliced
                    && args.len() == kids.len()
                    && args.iter().zip(kids.iter()).all(|(&a, &b)| a == b);
                if unchanged {
                    None
                } else {
                    Some(manager.mk_add(args))
                }
            }
        }
        TermKind::Sub(_, _) if kids.len() == 2 => {
            if sort_is(manager, sort, Sort::is_int) {
                let a = as_int(kids[0], manager)?;
                let b = as_int(kids[1], manager)?;
                Some(manager.mk_int(a - b))
            } else {
                let a = as_rat(kids[0], manager)?;
                let b = as_rat(kids[1], manager)?;
                let neg_b = Rational64::new(b.numer().checked_neg()?, *b.denom());
                Some(manager.mk_real(a.checked_add(&neg_b)?))
            }
        }
        TermKind::Neg(_) if kids.len() == 1 => {
            if sort_is(manager, sort, Sort::is_int) {
                Some(manager.mk_int(-(as_int(kids[0], manager)?).clone()))
            } else {
                let r = as_rat(kids[0], manager)?;
                Some(manager.mk_real(Rational64::new(r.numer().checked_neg()?, *r.denom())))
            }
        }
        TermKind::Mul(_) => {
            if sort_is(manager, sort, Sort::is_int) {
                let mut product = BigInt::from(1);
                for &k in kids {
                    product *= as_int(k, manager)?;
                }
                Some(manager.mk_int(product))
            } else {
                let mut product = Rational64::from_integer(1);
                for &k in kids {
                    product = product.checked_mul(&as_rat(k, manager)?)?;
                }
                Some(manager.mk_real(product))
            }
        }
        TermKind::BvXor(_, _) | TermKind::BvAdd(_, _) | TermKind::BvMul(_, _)
            if kids.len() == 2 =>
        {
            // Associative-chain normalization for wraparound BV ops:
            // `(x ⊕ c1) ⊕ c2` flattens to `[x, c1, c2]` and combines the
            // constants exactly, so a 5 000-deep constant-xor chain over a
            // variable collapses to `x ⊕ C` before the depth guard runs.
            let width = manager.sorts.get(sort).and_then(Sort::bitvec_width)?;
            let disc = std::mem::discriminant(kind);
            let mut flat: Vec<TermId> = Vec::with_capacity(4);
            let mut spliced = false;
            for &k in kids {
                let child = manager
                    .get(k)
                    .filter(|n| std::mem::discriminant(&n.kind) == disc && n.sort == sort);
                match child.map(|n| &n.kind) {
                    Some(TermKind::BvXor(a, b))
                    | Some(TermKind::BvAdd(a, b))
                    | Some(TermKind::BvMul(a, b)) => {
                        flat.push(*a);
                        flat.push(*b);
                        spliced = true;
                    }
                    _ => flat.push(k),
                }
            }
            let mut acc: Option<BigInt> = None;
            let mut non_const: Vec<TermId> = Vec::with_capacity(flat.len());
            for &k in flat.iter() {
                let cv = manager.get(k).and_then(|n| match &n.kind {
                    TermKind::BitVecConst { value, width: w } if *w == width => Some(value.clone()),
                    _ => None,
                });
                match cv {
                    Some(v) => {
                        acc = Some(match acc {
                            Some(a) => match kind {
                                TermKind::BvXor(..) => a ^ v,
                                TermKind::BvAdd(..) => bv_add(&a, &v, width),
                                _ => bv_wrap_unsigned(&(a * v), width),
                            },
                            None => v,
                        });
                    }
                    None => non_const.push(k),
                }
            }
            // Annihilator: x * 0 = 0.
            if matches!(kind, TermKind::BvMul(..)) && acc.as_ref().is_some_and(|a| a.is_zero()) {
                return Some(manager.mk_bitvec(BigInt::from(0), width));
            }
            let mk = |m: &mut TermManager, a: TermId, b: TermId| match kind {
                TermKind::BvXor(..) => m.mk_bv_xor(a, b),
                TermKind::BvAdd(..) => m.mk_bv_add(a, b),
                _ => m.mk_bv_mul(a, b),
            };
            let identity_zero = matches!(kind, TermKind::BvXor(..) | TermKind::BvAdd(..));
            let const_is_identity = |c: &BigInt| c.is_zero() || (!identity_zero && c.is_one());
            match (non_const.len(), acc) {
                (0, Some(c)) => Some(manager.mk_bitvec(c, width)),
                (1, None) => Some(non_const[0]),
                (1, Some(c)) => {
                    if const_is_identity(&c) {
                        Some(non_const[0])
                    } else {
                        let cc = manager.mk_bitvec(c, width);
                        Some(mk(manager, non_const[0], cc))
                    }
                }
                (_, acc) => {
                    if !spliced && acc.is_none() {
                        return None; // structurally unchanged binary node
                    }
                    let mut t = non_const[0];
                    for &k in non_const[1..].iter() {
                        t = mk(manager, t, k);
                    }
                    if let Some(c) = acc
                        && !const_is_identity(&c)
                    {
                        let cc = manager.mk_bitvec(c, width);
                        t = mk(manager, t, cc);
                    }
                    Some(t)
                }
            }
        }
        TermKind::Div(_, _) if kids.len() == 2 => {
            if sort_is(manager, sort, Sort::is_int) {
                let a = as_int(kids[0], manager)?;
                let b = as_int(kids[1], manager)?;
                if b.is_zero() {
                    return None; // partial: leave for the theory to blame
                }
                Some(manager.mk_int(big_div_euclid(a, b)))
            } else {
                let a = as_rat(kids[0], manager)?;
                let b = as_rat(kids[1], manager)?;
                if b.is_zero() {
                    return None;
                }
                Some(manager.mk_real(a.checked_div(&b)?))
            }
        }
        TermKind::Mod(_, _) if kids.len() == 2 => {
            // SMT-LIB `mod` is Int-only; result in [0, |b|).
            let a = as_int(kids[0], manager)?;
            let b = as_int(kids[1], manager)?;
            if b.is_zero() {
                return None;
            }
            Some(manager.mk_int(big_rem_euclid(a, b)))
        }
        TermKind::Lt(_, _) | TermKind::Le(_, _) | TermKind::Gt(_, _) | TermKind::Ge(_, _)
            if kids.len() == 2 =>
        {
            let ord = compare_nums(kids[0], kids[1], manager)?;
            let holds = match kind {
                TermKind::Lt(_, _) => ord == std::cmp::Ordering::Less,
                TermKind::Le(_, _) => ord != std::cmp::Ordering::Greater,
                TermKind::Gt(_, _) => ord == std::cmp::Ordering::Greater,
                TermKind::Ge(_, _) => ord != std::cmp::Ordering::Less,
                _ => return None,
            };
            Some(if holds {
                manager.mk_true()
            } else {
                manager.mk_false()
            })
        }
        TermKind::Eq(_, _) if kids.len() == 2 => {
            if kids[0] == kids[1] {
                // Structurally identical terms are equal.
                return Some(manager.mk_true());
            }
            consts_equal(kids[0], kids[1], manager).map(|eq| {
                if eq {
                    manager.mk_true()
                } else {
                    manager.mk_false()
                }
            })
        }
        TermKind::Not(_) if kids.len() == 1 => {
            let b = as_bool(kids[0], manager)?;
            Some(if b {
                manager.mk_false()
            } else {
                manager.mk_true()
            })
        }
        TermKind::And(_) => {
            // Total shortcuts only: a single false child decides the value;
            // an all-constant set evaluates. Dropping a `true` child would
            // need a structural rebuild — left to the main simplifier.
            let mut any_false = false;
            let mut all_true = true;
            let mut all_const = true;
            for &k in kids {
                match as_bool(k, manager) {
                    Some(true) => {}
                    Some(false) => any_false = true,
                    None => all_const = false,
                }
                if as_bool(k, manager) != Some(true) {
                    all_true = false;
                }
            }
            if any_false {
                Some(manager.mk_false())
            } else if all_const && all_true {
                Some(manager.mk_true())
            } else {
                None
            }
        }
        TermKind::Or(_) => {
            let mut any_true = false;
            let mut all_false = true;
            let mut all_const = true;
            for &k in kids {
                match as_bool(k, manager) {
                    Some(true) => any_true = true,
                    Some(false) => {}
                    None => all_const = false,
                }
                if as_bool(k, manager) != Some(false) {
                    all_false = false;
                }
            }
            if any_true {
                Some(manager.mk_true())
            } else if all_const && all_false {
                Some(manager.mk_false())
            } else {
                None
            }
        }
        TermKind::Xor(_, _) if kids.len() == 2 => {
            let a = as_bool(kids[0], manager)?;
            let b = as_bool(kids[1], manager)?;
            Some(if a ^ b {
                manager.mk_true()
            } else {
                manager.mk_false()
            })
        }
        TermKind::Implies(_, _) if kids.len() == 2 => {
            let a = as_bool(kids[0], manager)?;
            let b = as_bool(kids[1], manager)?;
            Some(if !a || b {
                manager.mk_true()
            } else {
                manager.mk_false()
            })
        }
        TermKind::Ite(_, _, _) if kids.len() == 3 => {
            // Constant condition selects the (already folded) branch.
            match as_bool(kids[0], manager) {
                Some(true) => Some(kids[1]),
                Some(false) => Some(kids[2]),
                None => None,
            }
        }
        TermKind::Distinct(_) => {
            if kids.len() < 2 {
                return None;
            }
            if kids.len() == 2 && kids[0] == kids[1] {
                return Some(manager.mk_false());
            }
            // Every child must be a comparable constant.
            let mut all_const = true;
            for &k in kids {
                let is_const = manager.get(k).is_some_and(|n| {
                    matches!(
                        n.kind,
                        TermKind::IntConst(_)
                            | TermKind::RealConst(_)
                            | TermKind::True
                            | TermKind::False
                    )
                });
                if !is_const {
                    all_const = false;
                    break;
                }
            }
            if !all_const {
                return None;
            }
            for i in 0..kids.len() {
                for j in (i + 1)..kids.len() {
                    match consts_equal(kids[i], kids[j], manager) {
                        Some(true) => return Some(manager.mk_false()),
                        Some(false) => {}
                        None => return None,
                    }
                }
            }
            Some(manager.mk_true())
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::traversal::compute_depth;

    fn mk_var(manager: &mut TermManager, name: &str) -> TermId {
        manager.mk_var(name, manager.sorts.int_sort)
    }

    fn int_const_is(term: TermId, manager: &TermManager, expect: &BigInt) {
        assert!(
            matches!(&manager.get(term).map(|n| &n.kind), Some(TermKind::IntConst(n)) if n == expect),
            "expected IntConst({expect}), got {:?}",
            manager.get(term).map(|n| &n.kind)
        );
    }

    #[test]
    fn deep_right_nested_constant_add_chain_collapses() {
        let mut manager = TermManager::new();
        // (+ 1 (+ 1 (+ 1 ... 0))) at depth 600: previously refused by the
        // encode-depth guard as a >512-deep term even though it folds to 600.
        let mut term = manager.mk_int(0);
        let one = manager.mk_int(1);
        for _ in 0..600 {
            term = manager.mk_add([one, term]);
        }
        assert!(compute_depth(term, &manager) > 512);
        let folded = fold_ground(term, &mut manager);
        int_const_is(folded, &manager, &BigInt::from(600));
    }

    #[test]
    fn deep_variable_add_chain_normalizes_to_one_constant() {
        let mut manager = TermManager::new();
        let x = mk_var(&mut manager, "x");
        let one = manager.mk_int(1);
        let mut term = x;
        for _ in 0..600 {
            term = manager.mk_add([one, term]);
        }
        let folded = fold_ground(term, &mut manager);
        // (+ 1 (+ 1 … x)) => (+ x 600): nesting gone, one folded constant.
        let c = manager.mk_int(600);
        let expect = manager.mk_add([x, c]);
        assert_eq!(folded, expect);
        assert!(compute_depth(folded, &manager) <= 3);
    }

    #[test]
    fn deep_bv_xor_constant_chain_collapses() {
        let mut manager = TermManager::new();
        let w = 32;
        let bv_sort = manager.sorts.bitvec(w);
        let x = manager.mk_var("x", bv_sort);
        // (bvxor (bvxor x c1) c2) … with the constants XOR-ing to K.
        let mut term = x;
        let mut k: i64 = 0;
        for i in 0..600u64 {
            let c = ((i * 7 + 3) % 1000) as i64;
            k ^= c;
            let cc = manager.mk_bitvec(c, w);
            term = manager.mk_bv_xor(term, cc);
        }
        let folded = fold_ground(term, &mut manager);
        let kc = manager.mk_bitvec(k, w);
        let expect = manager.mk_bv_xor(x, kc);
        assert_eq!(folded, expect, "chain must collapse to x ⊕ K");
        assert!(compute_depth(folded, &manager) <= 3);
    }

    #[test]
    fn bv_chain_identities() {
        let mut manager = TermManager::new();
        let w = 8;
        let bv_sort = manager.sorts.bitvec(w);
        let x = manager.mk_var("x", bv_sort);
        // (bvxor x 0) => x
        let z = manager.mk_bitvec(0, w);
        let t = manager.mk_bv_xor(x, z);
        assert_eq!(fold_ground(t, &mut manager), x);
        // (bvmul x 1) => x ; (bvmul x 0) => 0
        let one = manager.mk_bitvec(1, w);
        let t = manager.mk_bv_mul(x, one);
        assert_eq!(fold_ground(t, &mut manager), x);
        let t = manager.mk_bv_mul(x, z);
        assert_eq!(fold_ground(t, &mut manager), z);
        // (bvadd (bvadd x 250) 10) => (bvadd x 4): 260 wraps mod 2^8.
        let c250 = manager.mk_bitvec(250, w);
        let c10 = manager.mk_bitvec(10, w);
        let inner = manager.mk_bv_add(x, c250);
        let t = manager.mk_bv_add(inner, c10);
        let folded = fold_ground(t, &mut manager);
        let c4 = manager.mk_bitvec(4, w);
        let expect = manager.mk_bv_add(x, c4);
        assert_eq!(folded, expect);
    }

    #[test]
    fn bigint_constants_fold_exactly() {
        let mut manager = TermManager::new();
        // Two constants beyond i64 must not be truncated or skipped.
        let big = BigInt::from(i64::MAX) * 2u32 + 1u32;
        let a = manager.mk_int(big.clone());
        let b = manager.mk_int(1u32);
        let sum = manager.mk_add([a, b]);
        let folded = fold_ground(sum, &mut manager);
        int_const_is(folded, &manager, &(big + 1u32));
    }

    #[test]
    fn rational_overflow_skips_instead_of_wrapping() {
        let mut manager = TermManager::new();
        let huge = manager.mk_real(Rational64::new(i64::MAX / 2 + 1, 1));
        let sum = manager.mk_add([huge, huge]);
        let folded = fold_ground(sum, &mut manager);
        assert_eq!(folded, sum, "overflowing rational fold must be skipped");
    }

    #[test]
    fn euclidean_div_mod_on_negatives() {
        let mut manager = TermManager::new();
        // (a, b, a div b, a mod b) under SMT-LIB Euclidean semantics.
        let cases: &[(i64, i64, i64, i64)] = &[
            (-7, 5, -2, 3),
            (7, -5, -1, 2),
            (-7, -5, 2, 3),
            (12, 4, 3, 0),
        ];
        for &(a, b, q, r) in cases {
            let ca = manager.mk_int(a);
            let cb = manager.mk_int(b);
            let div = manager.mk_div(ca, cb);
            let folded = fold_ground(div, &mut manager);
            int_const_is(folded, &manager, &BigInt::from(q));
            let mo = manager.mk_mod(ca, cb);
            let folded = fold_ground(mo, &mut manager);
            int_const_is(folded, &manager, &BigInt::from(r));
        }
    }

    #[test]
    fn division_by_zero_stays_unfolded() {
        let mut manager = TermManager::new();
        let c1 = manager.mk_int(1);
        let c0 = manager.mk_int(0);
        let div = manager.mk_div(c1, c0);
        assert_eq!(fold_ground(div, &mut manager), div);
        let mo = manager.mk_mod(c1, c0);
        assert_eq!(fold_ground(mo, &mut manager), mo);
    }

    #[test]
    fn bool_shortcuts_and_ite() {
        let mut manager = TermManager::new();
        let x = mk_var(&mut manager, "x");
        // and(false, x) => false even though x is not ground.
        let f = manager.mk_false();
        let and = manager.mk_and([f, x]);
        let folded = fold_ground(and, &mut manager);
        assert!(matches!(
            manager.get(folded).map(|n| &n.kind),
            Some(TermKind::False)
        ));
        // ite(true, deep-chain, x) => deep-chain (itself folded).
        let mut chain = manager.mk_int(0);
        let one = manager.mk_int(1);
        for _ in 0..600 {
            chain = manager.mk_add([one, chain]);
        }
        let t = manager.mk_true();
        let ite = manager.mk_ite(t, chain, x);
        let folded = fold_ground(ite, &mut manager);
        int_const_is(folded, &manager, &BigInt::from(600));
    }

    #[test]
    fn binder_bodies_are_not_folded() {
        let mut manager = TermManager::new();
        let mut chain = manager.mk_int(0);
        let one = manager.mk_int(1);
        for _ in 0..600 {
            chain = manager.mk_add([one, chain]);
        }
        let six = manager.mk_int(600);
        let body = manager.mk_eq(chain, six);
        let forall = manager.mk_forall([("x", manager.sorts.int_sort)], body);
        let folded = fold_ground(forall, &mut manager);
        assert_eq!(folded, forall, "binder bodies must be skipped");
    }

    #[test]
    fn comparisons_and_mixed_real_fold() {
        let mut manager = TermManager::new();
        // (< 1 2.0) over mixed Int/Real views folds to true.
        let c1 = manager.mk_int(1);
        let r2 = manager.mk_real(Rational64::from_integer(2));
        let lt = manager.mk_lt(c1, r2);
        let folded = fold_ground(lt, &mut manager);
        assert!(matches!(
            manager.get(folded).map(|n| &n.kind),
            Some(TermKind::True)
        ));
        // real chain: 1/2 + 1/2 = 1
        let half = manager.mk_real(Rational64::new(1, 2));
        let sum = manager.mk_add([half, half]);
        let folded = fold_ground(sum, &mut manager);
        assert!(
            matches!(&manager.get(folded).map(|n| &n.kind), Some(TermKind::RealConst(r)) if *r == Rational64::from_integer(1))
        );
    }

    #[test]
    fn distinct_over_constants_folds() {
        let mut manager = TermManager::new();
        let c1 = manager.mk_int(1);
        let c2 = manager.mk_int(2);
        let c3 = manager.mk_int(3);
        let d = manager.mk_distinct([c1, c2, c3]);
        let folded = fold_ground(d, &mut manager);
        assert!(matches!(
            manager.get(folded).map(|n| &n.kind),
            Some(TermKind::True)
        ));
        let d2 = manager.mk_distinct([c1, c2, c1]);
        let folded = fold_ground(d2, &mut manager);
        assert!(matches!(
            manager.get(folded).map(|n| &n.kind),
            Some(TermKind::False)
        ));
    }
}
