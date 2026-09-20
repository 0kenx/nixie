//! Deep-assertion splitting — the term-level fix for the deep-encoding
//! class (`docs/studies/2026-09-19-smt-perf-gap-attribution.md`).
//!
//! A term whose non-skeleton nesting exceeds
//! [`ENCODE_DEPTH_LIMIT`](super::ENCODE_DEPTH_LIMIT) used to be recorded
//! unencoded and answered `Unknown` (the guard rightly protects the
//! recursive Tseitin encoder and the other native-recursive walks from
//! stack overflow).  Measured cost: the whole `nec-smt` family — one
//! assertion nesting 2537 deep through `let`/`ite`/`=` spines — answers
//! an instant spurious `unknown` on nine standing-table instances.
//!
//! The split: **lift deep subterms to fresh constants**.  Every node
//! sitting at least `BATCH` levels below the root of a too-deep term,
//! below which the tree is still deeper than `BATCH`, is replaced by a
//! fresh constant `dsplit!<term-id>` and its subterm is asserted as a
//! defining equation `(= dsplit!<id> <subterm>)`.  Equi-satisfiable by
//! construction (a fresh constant plus its definition denotes exactly
//! the subterm), so the transformation changes neither `sat` nor
//! `unsat` — it only trades depth for width.  The top piece ends at
//! most `BATCH` deep; each defining equation is re-queued and re-split
//! until every piece fits — a chain of depth `d` resolves in
//! `ceil(d / BATCH)` rounds.
//!
//! Every walk here is iterative (`traversal::get_children` +
//! explicit-stack memoized scans, `TermManager::substitute` for the
//! rebuild): the pass must itself be safe on the very terms it exists
//! to fix.  The AGENTS.md stack rule, applied to the cure and not just
//! the disease.

use nixie_core::ast::traversal::get_children;
use nixie_core::ast::{TermId, TermManager};
use rustc_hash::FxHashMap;

/// Whether the deep-split rescue is enabled (**default off**, env-gated,
/// cached — never a per-assert `getenv`; the env-probe regression
/// lesson).  The split is sound and unit-tested, but it currently buys
/// no verdict: the classes it unlocks (nec-smt's 2537-deep spines) are
/// then owned by a *second* pathology — the arithmetic layer's pivot
/// storm on the split's wide equality chains (profiled: `pivot` /
/// `find_violating` / `slice_contains`, thousands of conflict-free
/// pivots; see the study's twenty-second follow-up).  Flipping this on
/// before that fix lands trades a 0.2 s spurious `unknown` for a 20 s
/// searched `unknown` — honest, but strictly slower.  The arith arc
/// flips it with the eq-chain fix.
pub(super) fn enabled() -> bool {
    #[cfg(feature = "std")]
    {
        static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        *ON.get_or_init(|| std::env::var_os("NIXIE_DEEP_SPLIT").is_some())
    }
    #[cfg(not(feature = "std"))]
    {
        false
    }
}

/// Cut spacing: the maximum structural spine depth of any split piece.
/// Kept well under [`ENCODE_DEPTH_LIMIT`](super::ENCODE_DEPTH_LIMIT)
/// (512) so every piece's skeleton-aware guard measure — which never
/// exceeds its structural depth — passes with margin.
const BATCH: u32 = 200;

/// Piece acceptance bound: a piece at most this deep needs no further
/// splitting (the guard limit is 512 and its skeleton-aware measure
/// never exceeds the structural depth, so 480 passes with margin).
/// Distinct from `BATCH` — the *cut spacing*: a cut at depth ≥ `BATCH`
/// can leave the top piece up to a couple of levels deeper than
/// `BATCH`, which is still far inside `ACCEPT` (measured the hard way:
/// re-cutting a `BATCH`+2-deep piece fires no candidate — its children
/// are exactly `BATCH`-high — and the splitter wrongly gave up).
const ACCEPT: u32 = 480;

/// Total lift budget per top-level assertion.  The splitter exists for
/// deep-*narrow* spines (chains through `ite`/`=`/`let`); a pathological
/// DAG could otherwise mint unboundedly many definitions.  On budget
/// exhaustion the caller keeps the old honest behaviour (`Unknown`).
const MAX_LIFTS: usize = 20_000;

/// Split a too-deep assertion into shallow, equi-satisfiable pieces.
/// `None` = budget exhausted (caller falls back to the
/// unencoded-`Unknown` path); `Some` always contains at least the
/// rebuilt top piece.
pub(super) fn split_deep(term: TermId, manager: &mut TermManager) -> Option<Vec<TermId>> {
    let mut out: Vec<TermId> = Vec::new();
    let mut queue: Vec<TermId> = vec![term];
    let mut lifts = 0usize;
    while let Some(t) = queue.pop() {
        if depth_at_most(t, ACCEPT, manager) {
            out.push(t);
            continue;
        }
        let (top, defs) = cut_once(t, manager);
        lifts += defs.len();
        if defs.is_empty() || lifts > MAX_LIFTS {
            // No cut fired (a shape the scans measure through sharing)
            // or the budget died: the caller's `Unknown` is the honest
            // answer, never a guess.
            return None;
        }
        queue.push(top);
        queue.extend(defs);
    }
    Some(out)
}

/// Whether `root`'s longest root-to-leaf chain is at most `limit`
/// (structural depth; shared subterms visited at their shallowest;
/// early exit).  Conservative in the caller's favour: the depth guard's
/// measure never exceeds the structural depth, so
/// `structural ≤ BATCH ⇒ guard passes`.
fn depth_at_most(root: TermId, limit: u32, manager: &TermManager) -> bool {
    let mut best: FxHashMap<TermId, u32> = FxHashMap::default();
    let mut stack: Vec<(TermId, u32)> = vec![(root, 1)];
    while let Some((t, d)) = stack.pop() {
        if d > limit {
            return false;
        }
        if let Some(&seen) = best.get(&t)
            && seen <= d
        {
            continue;
        }
        best.insert(t, d);
        let Some(node) = manager.get(t) else {
            continue;
        };
        for child in get_children(&node.kind) {
            stack.push((child, d + 1));
        }
    }
    true
}

/// Subtree heights, shared-node-aware, explicit post-order stack.
/// height(node) = 1 + max(child heights); leaves = 1.
fn heights(root: TermId, manager: &TermManager) -> FxHashMap<TermId, u32> {
    let mut height: FxHashMap<TermId, u32> = FxHashMap::default();
    let mut stack: Vec<(TermId, usize)> = vec![(root, 0)];
    while let Some(&mut (t, ref mut next)) = stack.last_mut() {
        if height.contains_key(&t) {
            stack.pop();
            continue;
        }
        let Some(node) = manager.get(t) else {
            height.insert(t, 1);
            stack.pop();
            continue;
        };
        let children = get_children(&node.kind);
        if *next >= children.len() {
            let mut h = 1u32;
            for child in &children {
                h = h.max(height.get(child).copied().unwrap_or(1).saturating_add(1));
            }
            height.insert(t, h);
            stack.pop();
        } else {
            let child = children[*next];
            *next += 1;
            if !height.contains_key(&child) {
                stack.push((child, 0));
            }
        }
    }
    height
}

/// One splitting round over `root` (structurally deeper than `BATCH`):
/// cut candidates are nodes at depth ≥ `BATCH` whose subtree still
/// bottoms out below `BATCH` more levels — each is lifted to a fresh
/// constant; the top is rebuilt through [`TermManager::substitute`]
/// (iterative, hash-consed; untouched subtrees stay shared).
fn cut_once(root: TermId, manager: &mut TermManager) -> (TermId, Vec<TermId>) {
    let height = heights(root, manager);
    let mut cuts: FxHashMap<TermId, TermId> = FxHashMap::default();
    let mut defs: Vec<TermId> = Vec::new();
    {
        let mut seen: FxHashMap<TermId, u32> = FxHashMap::default();
        let mut stack: Vec<(TermId, u32)> = vec![(root, 1)];
        while let Some((t, d)) = stack.pop() {
            if let Some(&visited) = seen.get(&t)
                && visited <= d
            {
                continue;
            }
            seen.insert(t, d);
            let Some(node) = manager.get(t) else {
                continue;
            };
            let children = get_children(&node.kind);
            let deep_below = children
                .iter()
                .any(|&c| height.get(&c).copied().unwrap_or(1) > BATCH);
            if d >= BATCH && deep_below {
                // Lift: the fresh constant is named by the node's term id
                // — deterministic, and the same subterm met in a later
                // round or assertion lifts to the very same definition.
                let fresh = manager.mk_var(&format!("dsplit!t{}", t.0), node.sort);
                cuts.insert(t, fresh);
                defs.push(manager.mk_eq(fresh, t));
                continue;
            }
            for child in children {
                stack.push((child, d + 1));
            }
        }
    }
    if cuts.is_empty() {
        return (root, Vec::new());
    }
    let top = manager.substitute(root, &cuts);
    (top, defs)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deep_chain_splits_into_shallow_pieces() {
        let mut manager = TermManager::new();
        let int = manager.sorts.int_sort;
        let bool_ = manager.sorts.bool_sort;
        let c0 = manager.mk_var("c0", int);
        let c1 = manager.mk_var("c1", int);
        let b0 = manager.mk_var("b0", bool_);
        let mut chain = c0;
        for _ in 0..600 {
            chain = manager.mk_ite(b0, c1, chain);
        }
        let eq = manager.mk_eq(c0, chain);
        let pieces = split_deep(eq, &mut manager).expect("a 601-deep chain must split");
        assert!(
            pieces.len() >= 2,
            "expected multiple pieces, got {}",
            pieces.len()
        );
        for (i, p) in pieces.iter().enumerate() {
            assert!(
                depth_at_most(*p, ACCEPT, &manager),
                "piece {i} still deeper than ACCEPT"
            );
        }
    }
}
