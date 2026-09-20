//! Iterative bottom-up term simplification.
//!
//! Split out of `ast/manager/query.rs`. See `super::substitute`'s module
//! doc comment for the general rationale (an explicit heap stack instead of
//! native recursion, replacing the removed `MAX_QUERY_RECURSION_DEPTH`
//! cap).
//!
//! `simplify`'s conversion is considerably simpler than `substitute`'s:
//! only a small, fixed set of Boolean/arithmetic `TermKind`s ever recurses
//! into its children at all. The prior recursive implementation's catch-all
//! arm was `Some(_) => id`, returning everything else -- bit-vector/string/
//! FP operators, function applications, algebraic datatypes, and every
//! binder (`Forall`/`Exists`/`Let`/`Match`) -- completely untouched,
//! *without even visiting their children*. Since binders are never
//! descended into, there is no capture-avoidance to preserve here, unlike
//! `substitute`.

use super::TermManager;
use crate::ast::term::{TermId, TermKind};
#[allow(unused_imports)]
use crate::prelude::*;
use num_bigint::BigInt;
use smallvec::SmallVec;

/// Fuel for one `ctx_simplify` call: every recursive step decrements;
/// zero means "return unsimplified" — the pass degrades to the identity,
/// never to a wrong answer.
const CTX_FUEL_BUDGET: u32 = 200_000;
/// The growth guard's multiplier: a result beyond this multiple of the
/// input's DAG size is discarded (the input kept).
const CTX_GROWTH_LIMIT: usize = 4;

impl TermManager {
    /// Re-share a term for PRINTING: the DAG's multiply-referenced
    /// compound subtrees are lifted into `let` bindings, so printing the
    /// body and the bindings (with the stock printer) produces
    /// `let`-shared SMT-LIB text instead of tree-unfolding the sharing —
    /// which is exponential for fan-out chains (the nec-smt residual:
    /// 662 DAG nodes whose tree unfolding never finishes printing;
    /// `2026-09-19-smt-perf-gap-attribution.md`'s printer addendum).
    ///
    /// Returns `(bindings, body)` with `bindings` ordered
    /// children-before-parents (each binding's term may reference the
    /// names bound before it); printing
    /// `(let ((n1 b1)) (let ((n2 b2)) ... body))` is the shared
    /// spelling.  Two safety properties:
    /// * **Name capture is impossible**: candidate names are chosen
    ///   from the term's own symbol vocabulary's complement (every free
    ///   variable and function symbol name in the DAG is collected
    ///   first), so a user variable cannot collide with a binding name.
    /// * **Only compound subtrees bind** (size ≥
    ///   `MIN_SHARED_SUBTREE_SIZE`): shared leaves (variables,
    ///   constants) keep their plain spelling, so small terms print
    ///   exactly as before — the pass engages only where the unfolding
    ///   would actually repeat real content.
    pub fn share_for_printing(&mut self, root: TermId) -> (Vec<(String, TermId)>, TermId) {
        /// A subtree smaller than this is never let-bound: re-printing a
        /// shared leaf or a tiny atom is cheaper than a binding, and the
        /// threshold keeps ordinary terms' printed form unchanged.
        const MIN_SHARED_SUBTREE_SIZE: usize = 2;
        /// Bound on the number of bindings: pathological inputs must not
        /// mint unbounded names.
        const MAX_SHARED_BINDINGS: usize = 1000;

        // ---- 1. DAG walk: in-degree-with-multiplicity, subtree size,
        //         and the symbol vocabulary (for capture-free naming). ----
        let mut refs: FxHashMap<TermId, usize> = FxHashMap::default();
        let mut size: FxHashMap<TermId, usize> = FxHashMap::default();
        let mut vocab: FxHashSet<crate::interner::Spur> = FxHashSet::default();
        // DAG walk, two-phase (Expand/Combine) so sizes combine in TRUE
        // post-order — children's sizes are always inserted before their
        // parents read them.  (A reversed pre-order is NOT post-order:
        // this analysis's first version combined parents first, reading
        // `unwrap_or(1)` for not-yet-sized children — every size was
        // undercounted, the candidate order was not topological, and the
        // bindings' RHS kept un-cut shared subtrees whose printing
        // exploded.  The bug's signature: a 407-DAG-node RHS printing
        // gigabytes.)
        enum Frame {
            Expand(TermId),
            Combine(TermId),
        }
        let mut stack: Vec<Frame> = vec![Frame::Expand(root)];
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Expand(t) => {
                    if !seen.insert(t) {
                        continue;
                    }
                    let Some(data) = self.get(t).cloned() else {
                        continue;
                    };
                    if let crate::ast::term::TermKind::Var(name) = &data.kind {
                        vocab.insert(*name);
                    }
                    if let crate::ast::term::TermKind::Apply { func, .. } = &data.kind {
                        vocab.insert(*func);
                    }
                    let children = crate::ast::traversal::get_children(&data.kind);
                    for c in children.iter() {
                        *refs.entry(*c).or_default() += 1;
                    }
                    stack.push(Frame::Combine(t));
                    for c in children.iter().rev() {
                        stack.push(Frame::Expand(*c));
                    }
                }
                Frame::Combine(t) => {
                    let Some(data) = self.get(t) else { continue };
                    let children = crate::ast::traversal::get_children(&data.kind);
                    let s = 1 + children
                        .iter()
                        .map(|c| size.get(c).copied().unwrap_or(1))
                        .sum::<usize>();
                    size.insert(t, s);
                }
            }
        }
        let root_size = size.get(&root).copied().unwrap_or(1);

        // ---- 2. Candidates: multiply-referenced compound subtrees. ----
        let mut candidates: Vec<TermId> = refs
            .iter()
            .filter(|&(t, &r)| {
                r >= 2 && size.get(t).copied().unwrap_or(1) >= MIN_SHARED_SUBTREE_SIZE && *t != root
            })
            .map(|(&t, _)| t)
            .collect();
        // Children before parents: a candidate's candidate children are
        // strictly smaller, so ascending size is a valid topological
        // order.
        candidates.sort_by_key(|t| size.get(t).copied().unwrap_or(1));
        candidates.truncate(MAX_SHARED_BINDINGS);
        if candidates.is_empty() || root_size < 2 * MIN_SHARED_SUBTREE_SIZE {
            return (Vec::new(), root);
        }

        // ---- 3. Name minting against the vocabulary's complement. ----
        let mut names: FxHashMap<TermId, TermId> = FxHashMap::default();
        let mut bindings: Vec<(String, TermId)> = Vec::new();
        let mut counter = 1u32;
        for cand in candidates {
            let name = loop {
                let candidate = format!("a!{counter}");
                counter += 1;
                let spur = self.intern_str(&candidate);
                if !vocab.contains(&spur) {
                    break candidate;
                }
            };
            // The binding's RHS: the candidate with its already-named
            // (smaller) candidate children replaced by their names.
            let rhs = self.substitute(cand, &names);
            let sort = self
                .get(cand)
                .map(|t| t.sort)
                .unwrap_or(self.sorts.bool_sort);
            let var = self.mk_var(&name, sort);
            bindings.push((name, rhs));
            names.insert(cand, var);
        }
        let body = self.substitute(root, &names);
        (bindings, body)
    }
    /// Simplify a term by applying rewrite rules.
    ///
    /// This performs bottom-up simplification including:
    /// - Constant folding for arithmetic
    /// - Boolean simplifications
    /// - Identity/annihilator rules
    pub fn simplify(&mut self, id: TermId) -> TermId {
        let mut cache = FxHashMap::default();
        self.simplify_cached(id, &mut cache)
    }

    /// Simplify with memoization, using an explicit heap stack instead of
    /// native recursion (see the module doc comment). The two-phase
    /// iterative post-order shape mirrors `size_depth::term_size_cached`;
    /// only the small, explicitly-listed set of kinds in
    /// [`Self::simplifiable_children`] is ever expanded into children --
    /// everything else resolves to itself immediately, matching the prior
    /// recursive catch-all exactly (and, like the prior code, never
    /// memoizes an unvisited node under a fabricated entry -- it simply
    /// isn't pushed).
    fn simplify_cached(&mut self, id: TermId, cache: &mut FxHashMap<TermId, TermId>) -> TermId {
        if let Some(&result) = cache.get(&id) {
            return result;
        }

        let mut stack: Vec<(TermId, bool)> = vec![(id, false)];
        while let Some((current, expanded)) = stack.pop() {
            if cache.contains_key(&current) {
                continue;
            }

            if expanded {
                let result = self.combine_simplified(current, cache);
                cache.insert(current, result);
            } else {
                let children = self.simplifiable_children(current);
                stack.push((current, true));
                for &child in children.iter().rev() {
                    if !cache.contains_key(&child) {
                        stack.push((child, false));
                    }
                }
            }
        }

        cache.get(&id).copied().unwrap_or(id)
    }

    /// Context-dependent simplification (z3's `ctx-simplify` shape, the
    /// pass the nec-smt let-chain goals need — see
    /// `2026-09-19-smt-perf-gap-attribution.md`'s parameter-sweep
    /// addendum: `push_ite` + `ite_extra_rules` + `solve_eqs` are each
    /// necessary, and the LOCAL subset alone is a measured dead end; the
    /// closing power comes from carrying a literal context through the
    /// walk).
    ///
    /// The walk is top-down with a context of known-polarity atoms:
    /// * at an `And`, every conjunct contributes its atom polarity (the
    ///   conjunct IS true in this context) and the remaining conjuncts
    ///   simplify under it;
    /// * at an `Or`, a FALSE literal is dropped (modus ponens on the
    ///   path — one disjunct known false removes it);
    /// * at a `Not`, the polarity flips;
    /// * at an `Ite` whose condition the context decides, prune to the
    ///   selected branch; otherwise descend BOTH branches under
    ///   `c` / `¬c` (the case split that reaches through `or`/`not`
    ///   nesting — the piece the one-level And-context prune lacked);
    /// * at `Eq`/comparisons of a constant against an `Ite`, push into
    ///   the branches (fuel-bounded) so constant-vs-constant branches
    ///   decide.
    ///
    /// Every step is an equivalence at its node under the path context
    /// (never a strengthening); the top-level call starts with the empty
    /// context, so the RESULT is unconditionally equivalent to the input.
    /// Fuel-bounded throughout; a growth guard keeps the result when a
    /// rewrite would exceed `CTX_GROWTH_LIMIT` × the input's DAG size.
    pub fn ctx_simplify(&mut self, root: TermId) -> TermId {
        let size_in = self.subtree_dag_size(root);
        // The per-subtree Boolean-atom sets (the memo's relevance
        // domains): the walk of `t` can only consult context entries for
        // atoms OCCURRING in `t`'s subtree, so results memoize per
        // (term, relevant-atoms signature) — without this, shared
        // subchains re-walk multiplicatively (the nec-smt member burned
        // the whole 200k-step fuel on a 662-node term).
        let sub_atoms = self.subtree_bool_atoms(root);
        let mut fuel = CTX_FUEL_BUDGET;
        let mut memo: FxHashMap<(TermId, u64), TermId> = FxHashMap::default();
        let out = self.ctx_walk(
            root,
            &mut FxHashMap::default(),
            &mut fuel,
            &sub_atoms,
            &mut memo,
        );
        let size_out = self.subtree_dag_size(out);
        if size_out > size_in.saturating_mul(CTX_GROWTH_LIMIT) {
            return root;
        }
        out
    }

    /// Boolean-sorted atom sets per subtree, bottom-up over the DAG
    /// (children's sets unioned; a node's own id included when it is
    /// Boolean-sorted — any Boolean node can serve as a context atom
    /// key).  `None` for a node whose set exceeds
    /// [`MAX_MEMO_ATOM_SET`]: such subtrees simply do not memoize (the
    /// walk stays correct, only slower).
    fn subtree_bool_atoms(&self, root: TermId) -> FxHashMap<TermId, Option<FxHashSet<TermId>>> {
        /// Beyond this many distinct atoms a subtree's set is stored as
        /// `None` (no memoization for it) — the set itself would cost
        /// more than the re-walk it saves on typical inputs.
        const MAX_MEMO_ATOM_SET: usize = 1024;
        let mut out: FxHashMap<TermId, Option<FxHashSet<TermId>>> = FxHashMap::default();
        // Two-phase Expand/Combine (children's sets exist before the
        // parent unions them — the post-order trap the share-for-printing
        // pass already recorded once).
        enum Frame {
            Expand(TermId),
            Combine(TermId),
        }
        let mut stack = vec![Frame::Expand(root)];
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        while let Some(f) = stack.pop() {
            match f {
                Frame::Expand(t) => {
                    if !seen.insert(t) {
                        continue;
                    }
                    let Some(data) = self.get(t).cloned() else {
                        continue;
                    };
                    let children = crate::ast::traversal::get_children(&data.kind);
                    stack.push(Frame::Combine(t));
                    for c in children.iter().rev() {
                        stack.push(Frame::Expand(*c));
                    }
                }
                Frame::Combine(t) => {
                    let Some(data) = self.get(t) else { continue };
                    let children = crate::ast::traversal::get_children(&data.kind);
                    let mut set: Option<FxHashSet<TermId>> = if data.sort == self.sorts.bool_sort {
                        let mut s = FxHashSet::default();
                        s.insert(t);
                        Some(s)
                    } else {
                        Some(FxHashSet::default())
                    };
                    for c in children {
                        match (out.get(&c), &mut set) {
                            (Some(Some(cs)), Some(s)) => {
                                for x in cs {
                                    s.insert(*x);
                                }
                            }
                            (Some(None), _) | (None, _) => {
                                set = None;
                            }
                            _ => {}
                        }
                    }
                    if let Some(s) = &set
                        && s.len() > MAX_MEMO_ATOM_SET
                    {
                        set = None;
                    }
                    out.insert(t, set);
                }
            }
        }
        out
    }

    /// The memo signature for walking `t` under `ctx`: a hash of the
    /// context's entries restricted to `t`'s relevant atoms.  Two
    /// contexts agreeing on those entries walk `t` identically — the
    /// walk consults nothing else.
    fn ctx_signature(
        &self,
        t: TermId,
        ctx: &FxHashMap<TermId, bool>,
        sub_atoms: &FxHashMap<TermId, Option<FxHashSet<TermId>>>,
    ) -> Option<u64> {
        let relevant = sub_atoms.get(&t)?;
        let set = relevant.as_ref()?;
        // Iterate the CONTEXT (small: it grows only along the walk's
        // case-split/conjunct path) and test subtree membership — the
        // intersection is what the walk can consult.
        let mut h = std::collections::hash_map::DefaultHasher::new();
        use std::hash::Hash;
        let mut entries: SmallVec<[(TermId, bool); 8]> = SmallVec::new();
        for (&atom, &pol) in ctx.iter() {
            if set.contains(&atom) {
                entries.push((atom, pol));
            }
        }
        entries.sort_unstable_by_key(|(a, _)| a.0);
        for (atom, pol) in entries {
            atom.0.hash(&mut h);
            pol.hash(&mut h);
        }
        Some(std::hash::Hasher::finish(&h))
    }

    /// DAG node count of `t`'s subtree (the growth guard's metric).
    fn subtree_dag_size(&self, t: TermId) -> usize {
        let mut n = 0usize;
        let mut stack = vec![t];
        let mut seen = FxHashSet::default();
        while let Some(x) = stack.pop() {
            if seen.insert(x) {
                n += 1;
                if let Some(d) = self.get(x) {
                    stack.extend(crate::ast::traversal::get_children(&d.kind));
                }
            }
        }
        n
    }

    /// One context step: the polarity `p` assigns to atom `t`, if `t` is
    /// literal-shaped.
    fn atom_polarity(&self, t: TermId) -> Option<(TermId, bool)> {
        match self.get(t).map(|d| &d.kind) {
            Some(TermKind::Not(inner)) => Some((*inner, false)),
            // A Boolean atom in positive position asserts itself.
            Some(_) if self.get(t).is_some_and(|d| d.sort == self.sorts.bool_sort) => {
                Some((t, true))
            }
            _ => None,
        }
    }

    /// The context-decided value of `t`: a literal hit, a constant, or a
    /// comparison the context decides via a known atom's negation
    /// (`(not c)` with `c` known true).
    fn ctx_value(&self, t: TermId, ctx: &FxHashMap<TermId, bool>) -> Option<bool> {
        if let Some(TermKind::True) = self.get(t).map(|d| &d.kind) {
            return Some(true);
        }
        if let Some(TermKind::False) = self.get(t).map(|d| &d.kind) {
            return Some(false);
        }
        let (atom, positive) = self.atom_polarity(t)?;
        let known = *ctx.get(&atom)?;
        Some(if positive { known } else { !known })
    }

    fn ctx_walk(
        &mut self,
        t: TermId,
        ctx: &mut FxHashMap<TermId, bool>,
        fuel: &mut u32,
        sub_atoms: &FxHashMap<TermId, Option<FxHashSet<TermId>>>,
        memo: &mut FxHashMap<(TermId, u64), TermId>,
    ) -> TermId {
        let sig = self.ctx_signature(t, ctx, sub_atoms);
        if let Some(s) = sig
            && let Some(&r) = memo.get(&(t, s))
        {
            return r;
        }
        let out = self.ctx_walk_inner(t, ctx, fuel, sub_atoms, memo);
        if let Some(s) = sig {
            memo.insert((t, s), out);
        }
        out
    }

    fn ctx_walk_inner(
        &mut self,
        t: TermId,
        ctx: &mut FxHashMap<TermId, bool>,
        fuel: &mut u32,
        sub_atoms: &FxHashMap<TermId, Option<FxHashSet<TermId>>>,
        memo: &mut FxHashMap<(TermId, u64), TermId>,
    ) -> TermId {
        if *fuel == 0 {
            return t;
        }
        *fuel -= 1;
        // Constant or context-decided: replace by the Boolean directly.
        if let Some(v) = self.ctx_value(t, ctx) {
            return if v { self.true_id } else { self.false_id };
        }
        let Some(data) = self.get(t).cloned() else {
            return t;
        };
        match data.kind {
            TermKind::Not(inner) => {
                let s = self.ctx_walk(inner, ctx, fuel, sub_atoms, memo);
                self.mk_not(s)
            }
            TermKind::And(args) => self.ctx_and(args, ctx, fuel, sub_atoms, memo),
            TermKind::Or(args) => {
                // Drop disjuncts the context refutes; recurse the rest.
                let mut kept: SmallVec<[TermId; 4]> = SmallVec::new();
                for a in args {
                    if let Some(false) = self.ctx_value(a, ctx) {
                        continue;
                    }
                    let s = self.ctx_walk(a, ctx, fuel, sub_atoms, memo);
                    kept.push(s);
                }
                self.mk_or(kept)
            }
            TermKind::Ite(c, a, b) => {
                // Case split: each branch under its own guard.
                let cs = self.ctx_walk(c, ctx, fuel, sub_atoms, memo);
                if let Some(TermKind::True) = self.get(cs).map(|d| &d.kind) {
                    return self.ctx_walk(a, ctx, fuel, sub_atoms, memo);
                }
                if let Some(TermKind::False) = self.get(cs).map(|d| &d.kind) {
                    return self.ctx_walk(b, ctx, fuel, sub_atoms, memo);
                }
                let (as_, bs) = if let Some((atom, pol)) = self.atom_polarity(cs) {
                    let prev = ctx.insert(atom, pol);
                    let as_ = self.ctx_walk(a, ctx, fuel, sub_atoms, memo);
                    ctx.insert(atom, !pol);
                    let bs = self.ctx_walk(b, ctx, fuel, sub_atoms, memo);
                    match prev {
                        Some(p) => {
                            ctx.insert(atom, p);
                        }
                        None => {
                            ctx.remove(&atom);
                        }
                    }
                    (as_, bs)
                } else {
                    (
                        self.ctx_walk(a, ctx, fuel, sub_atoms, memo),
                        self.ctx_walk(b, ctx, fuel, sub_atoms, memo),
                    )
                };
                // The ite-on-Boolean connections (z3's `ite_extra_rules`
                // core): a Boolean ite with a constant branch connects to
                // and/or, where the context's literals absorb it.
                if self
                    .get(as_)
                    .is_some_and(|d| d.sort == self.sorts.bool_sort)
                    && self.get(bs).is_some_and(|d| d.sort == self.sorts.bool_sort)
                {
                    let t_true = matches!(self.get(as_).map(|d| &d.kind), Some(TermKind::True));
                    let t_false = matches!(self.get(as_).map(|d| &d.kind), Some(TermKind::False));
                    let e_true = matches!(self.get(bs).map(|d| &d.kind), Some(TermKind::True));
                    let e_false = matches!(self.get(bs).map(|d| &d.kind), Some(TermKind::False));
                    let not_cs = self.mk_not(cs);
                    if t_true && e_false {
                        return cs;
                    }
                    if t_false && e_true {
                        return not_cs;
                    }
                    if t_true {
                        return self.mk_or([cs, bs]);
                    }
                    if e_true {
                        return self.mk_or([not_cs, as_]);
                    }
                    if t_false {
                        return self.ctx_and(
                            SmallVec::from_iter([not_cs, bs]),
                            ctx,
                            fuel,
                            sub_atoms,
                            memo,
                        );
                    }
                    if e_false {
                        return self.ctx_and(
                            SmallVec::from_iter([cs, as_]),
                            ctx,
                            fuel,
                            sub_atoms,
                            memo,
                        );
                    }
                }
                self.mk_ite(cs, as_, bs)
            }
            TermKind::Eq(l, r) => {
                // The push (z3's `push_ite` equality half): a numeric
                // constant against an ite becomes an ite of comparisons.
                let lk = matches!(
                    self.get(l).map(|d| &d.kind),
                    Some(TermKind::IntConst(_) | TermKind::RealConst(_))
                );
                let rk = matches!(
                    self.get(r).map(|d| &d.kind),
                    Some(TermKind::IntConst(_) | TermKind::RealConst(_))
                );
                let li = matches!(self.get(l).map(|d| &d.kind), Some(TermKind::Ite(..)));
                let ri = matches!(self.get(r).map(|d| &d.kind), Some(TermKind::Ite(..)));
                if (lk && ri) || (rk && li) {
                    let (k, ite) = if lk { (l, r) } else { (r, l) };
                    if let Some(TermKind::Ite(c, a, b)) = self.get(ite).map(|d| d.kind.clone()) {
                        let ka_eq = self.mk_eq(k, a);
                        let ka = self.ctx_walk(ka_eq, ctx, fuel, sub_atoms, memo);
                        let kb_eq = self.mk_eq(k, b);
                        let kb = self.ctx_walk(kb_eq, ctx, fuel, sub_atoms, memo);
                        let cs = self.ctx_walk(c, ctx, fuel, sub_atoms, memo);
                        // Re-enter the walk so the ITE arm's connection
                        // folds see the pushed shape (a constant branch
                        // connects into and/or where the context absorbs
                        // it) — returning the raw `mk_ite` bypassed them.
                        let pushed = self.mk_ite(cs, ka, kb);
                        return self.ctx_walk(pushed, ctx, fuel, sub_atoms, memo);
                    }
                }
                let ls = self.ctx_walk(l, ctx, fuel, sub_atoms, memo);
                let rs = self.ctx_walk(r, ctx, fuel, sub_atoms, memo);
                self.mk_eq(ls, rs)
            }
            // Every other kind: keep the node (its children were already
            // simplified by the bottom-up pass that runs first).
            _ => t,
        }
    }

    fn ctx_and(
        &mut self,
        args: SmallVec<[TermId; 4]>,
        ctx: &mut FxHashMap<TermId, bool>,
        fuel: &mut u32,
        sub_atoms: &FxHashMap<TermId, Option<FxHashSet<TermId>>>,
        memo: &mut FxHashMap<(TermId, u64), TermId>,
    ) -> TermId {
        // Each conjunct asserts its atom's polarity; the REST simplify
        // under it.  The extensions unwind exactly: fresh entries are
        // removed, entries a parent had set are restored — a conjunct's
        // polarity is not valid outside the conjunction.
        let mut simplified: SmallVec<[TermId; 4]> = SmallVec::new();
        let mut unwind: Vec<Option<(TermId, bool)>> = Vec::new();
        for a in args {
            if let Some(false) = self.ctx_value(a, ctx) {
                for (atom, prev) in unwind.into_iter().rev().flatten() {
                    ctx.insert(atom, prev);
                }
                return self.false_id;
            }
            if let Some(true) = self.ctx_value(a, ctx) {
                continue;
            }
            let s = self.ctx_walk(a, ctx, fuel, sub_atoms, memo);
            match self.get(s).map(|d| &d.kind) {
                Some(TermKind::False) => {
                    for (atom, prev) in unwind.into_iter().rev().flatten() {
                        ctx.insert(atom, prev);
                    }
                    return self.false_id;
                }
                Some(TermKind::True) => continue,
                _ => {}
            }
            simplified.push(s);
            if let Some((atom, pol)) = self.atom_polarity(s) {
                let prev = ctx.insert(atom, pol);
                unwind.push(prev.map(|p| (atom, p)));
            }
        }
        for (atom, prev) in unwind.into_iter().rev().flatten() {
            ctx.insert(atom, prev);
        }
        self.mk_and(simplified)
    }

    /// The children `simplify_cached` should recurse into for `id`, or none
    /// for a leaf, an unrecognized term, or any kind the simplifier does
    /// not rewrite (matching the prior `Some(_) => id` catch-all, which
    /// never visited such a node's children at all).
    fn simplifiable_children(&self, id: TermId) -> SmallVec<[TermId; 4]> {
        match self.get(id).map(|t| &t.kind) {
            None
            | Some(
                TermKind::True
                | TermKind::False
                | TermKind::IntConst(_)
                | TermKind::RealConst(_)
                | TermKind::BitVecConst { .. }
                | TermKind::Var(_),
            ) => SmallVec::new(),
            Some(TermKind::Not(a) | TermKind::Neg(a)) => [*a].into_iter().collect(),
            Some(
                TermKind::And(args)
                | TermKind::Or(args)
                | TermKind::Add(args)
                | TermKind::Mul(args),
            ) => args.iter().copied().collect(),
            Some(
                TermKind::Implies(a, b)
                | TermKind::Eq(a, b)
                | TermKind::Sub(a, b)
                | TermKind::Lt(a, b)
                | TermKind::Le(a, b)
                | TermKind::Gt(a, b)
                | TermKind::Ge(a, b),
            ) => [*a, *b].into_iter().collect(),
            Some(TermKind::Ite(c, t, e)) => [*c, *t, *e].into_iter().collect(),
            Some(_) => SmallVec::new(),
        }
    }

    /// Rebuild `id` from its already-simplified children (see
    /// `simplify_cached`), applying the same rewrite/constant-folding rule
    /// the prior recursive match arm used for each kind.
    fn combine_simplified(&mut self, id: TermId, cache: &FxHashMap<TermId, TermId>) -> TermId {
        let sub =
            |cache: &FxHashMap<TermId, TermId>, t: TermId| cache.get(&t).copied().unwrap_or(t);
        match self.get(id).map(|t| t.kind.clone()) {
            None
            | Some(
                TermKind::True
                | TermKind::False
                | TermKind::IntConst(_)
                | TermKind::RealConst(_)
                | TermKind::BitVecConst { .. }
                | TermKind::Var(_),
            ) => id,

            Some(TermKind::Not(arg)) => {
                let new_arg = sub(cache, arg);
                self.mk_not(new_arg)
            }
            Some(TermKind::And(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args.iter().map(|&a| sub(cache, a)).collect();
                self.mk_and(new_args)
            }
            Some(TermKind::Or(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args.iter().map(|&a| sub(cache, a)).collect();
                self.mk_or(new_args)
            }
            Some(TermKind::Implies(lhs, rhs)) => {
                let new_lhs = sub(cache, lhs);
                let new_rhs = sub(cache, rhs);
                self.mk_implies(new_lhs, new_rhs)
            }
            Some(TermKind::Eq(lhs, rhs)) => {
                let new_lhs = sub(cache, lhs);
                let new_rhs = sub(cache, rhs);
                self.mk_eq(new_lhs, new_rhs)
            }
            Some(TermKind::Ite(cond, then_br, else_br)) => {
                let new_cond = sub(cache, cond);
                let new_then = sub(cache, then_br);
                let new_else = sub(cache, else_br);
                self.mk_ite(new_cond, new_then, new_else)
            }
            Some(TermKind::Add(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args.iter().map(|&a| sub(cache, a)).collect();
                self.simplify_add(new_args)
            }
            Some(TermKind::Sub(lhs, rhs)) => {
                let new_lhs = sub(cache, lhs);
                let new_rhs = sub(cache, rhs);
                self.simplify_sub(new_lhs, new_rhs)
            }
            Some(TermKind::Mul(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args.iter().map(|&a| sub(cache, a)).collect();
                self.simplify_mul(new_args)
            }
            Some(TermKind::Neg(arg)) => {
                let new_arg = sub(cache, arg);
                self.simplify_neg(new_arg)
            }
            Some(TermKind::Lt(lhs, rhs)) => {
                let new_lhs = sub(cache, lhs);
                let new_rhs = sub(cache, rhs);
                self.simplify_lt(new_lhs, new_rhs)
            }
            Some(TermKind::Le(lhs, rhs)) => {
                let new_lhs = sub(cache, lhs);
                let new_rhs = sub(cache, rhs);
                self.simplify_le(new_lhs, new_rhs)
            }
            Some(TermKind::Gt(lhs, rhs)) => {
                let new_lhs = sub(cache, lhs);
                let new_rhs = sub(cache, rhs);
                self.simplify_gt(new_lhs, new_rhs)
            }
            Some(TermKind::Ge(lhs, rhs)) => {
                let new_lhs = sub(cache, lhs);
                let new_rhs = sub(cache, rhs);
                self.simplify_ge(new_lhs, new_rhs)
            }
            // Everything else: left untouched, matching the prior
            // recursive catch-all (its children are never visited, so
            // there is nothing to gather from `cache` for them either).
            Some(_) => id,
        }
    }

    /// Simplify addition with constant folding.
    fn simplify_add(&mut self, args: SmallVec<[TermId; 4]>) -> TermId {
        let mut constant_sum = BigInt::from(0);
        let mut other_args: SmallVec<[TermId; 4]> = SmallVec::new();

        for arg in args {
            if let Some(TermKind::IntConst(n)) = self.get(arg).map(|t| &t.kind) {
                constant_sum += n;
            } else {
                other_args.push(arg);
            }
        }

        let zero = BigInt::from(0);
        if other_args.is_empty() {
            return self.intern(TermKind::IntConst(constant_sum), self.sorts.int_sort);
        }

        if constant_sum != zero {
            other_args.push(self.intern(TermKind::IntConst(constant_sum), self.sorts.int_sort));
        }

        if other_args.len() == 1 {
            return other_args[0];
        }

        self.mk_add(other_args)
    }

    /// Simplify subtraction with constant folding.
    fn simplify_sub(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let zero = BigInt::from(0);
        match (
            self.get(lhs).map(|t| t.kind.clone()),
            self.get(rhs).map(|t| t.kind.clone()),
        ) {
            (Some(TermKind::IntConst(a)), Some(TermKind::IntConst(b))) => {
                self.intern(TermKind::IntConst(a - b), self.sorts.int_sort)
            }
            (_, Some(TermKind::IntConst(n))) if n == zero => lhs,
            (Some(TermKind::IntConst(n)), _) if n == zero => self.simplify_neg(rhs),
            _ => self.mk_sub(lhs, rhs),
        }
    }

    /// Simplify multiplication with constant folding.
    fn simplify_mul(&mut self, args: SmallVec<[TermId; 4]>) -> TermId {
        let mut constant_product = BigInt::from(1);
        let mut other_args: SmallVec<[TermId; 4]> = SmallVec::new();
        let zero = BigInt::from(0);
        let one = BigInt::from(1);

        for arg in args {
            if let Some(TermKind::IntConst(n)) = self.get(arg).map(|t| &t.kind) {
                if *n == zero {
                    return self.mk_int(0);
                }
                constant_product *= n;
            } else {
                other_args.push(arg);
            }
        }

        if other_args.is_empty() {
            return self.intern(TermKind::IntConst(constant_product), self.sorts.int_sort);
        }

        if constant_product == zero {
            return self.mk_int(0);
        }

        if constant_product != one {
            other_args.insert(
                0,
                self.intern(TermKind::IntConst(constant_product), self.sorts.int_sort),
            );
        }

        if other_args.len() == 1 {
            return other_args[0];
        }

        self.mk_mul(other_args)
    }

    /// Simplify negation.
    fn simplify_neg(&mut self, arg: TermId) -> TermId {
        match self.get(arg).map(|t| t.kind.clone()) {
            Some(TermKind::IntConst(n)) => self.intern(TermKind::IntConst(-n), self.sorts.int_sort),
            Some(TermKind::Neg(inner)) => inner,
            _ => {
                let sort = self.get(arg).map_or(self.sorts.int_sort, |t| t.sort);
                self.intern(TermKind::Neg(arg), sort)
            }
        }
    }

    /// Simplify less-than with constant comparison and reflexivity.
    fn simplify_lt(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        // Reflexivity: a < a is always False
        if lhs == rhs {
            return self.false_id;
        }
        match (
            self.get(lhs).map(|t| t.kind.clone()),
            self.get(rhs).map(|t| t.kind.clone()),
        ) {
            (Some(TermKind::IntConst(a)), Some(TermKind::IntConst(b))) => self.mk_bool(a < b),
            _ => self.mk_lt(lhs, rhs),
        }
    }

    /// Simplify less-or-equal with constant comparison and reflexivity.
    fn simplify_le(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        // Reflexivity: a <= a is always True
        if lhs == rhs {
            return self.true_id;
        }
        match (
            self.get(lhs).map(|t| t.kind.clone()),
            self.get(rhs).map(|t| t.kind.clone()),
        ) {
            (Some(TermKind::IntConst(a)), Some(TermKind::IntConst(b))) => self.mk_bool(a <= b),
            _ => self.mk_le(lhs, rhs),
        }
    }

    /// Simplify greater-than with constant comparison and reflexivity.
    fn simplify_gt(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        // Reflexivity: a > a is always False
        if lhs == rhs {
            return self.false_id;
        }
        match (
            self.get(lhs).map(|t| t.kind.clone()),
            self.get(rhs).map(|t| t.kind.clone()),
        ) {
            (Some(TermKind::IntConst(a)), Some(TermKind::IntConst(b))) => self.mk_bool(a > b),
            _ => self.mk_gt(lhs, rhs),
        }
    }

    /// Simplify greater-or-equal with constant comparison and reflexivity.
    fn simplify_ge(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        // Reflexivity: a >= a is always True
        if lhs == rhs {
            return self.true_id;
        }
        match (
            self.get(lhs).map(|t| t.kind.clone()),
            self.get(rhs).map(|t| t.kind.clone()),
        ) {
            (Some(TermKind::IntConst(a)), Some(TermKind::IntConst(b))) => self.mk_bool(a >= b),
            _ => self.mk_ge(lhs, rhs),
        }
    }
}
