//! Batch congruence closure over finite-field-sorted terms – the EUF half
//! of the `QF_UFFF` combination (`docs/FF_THEORY_DESIGN.md` §7).
//!
//! The pure-`QF_FF` dispatch treats an uninterpreted application with an
//! FF result sort (`f : 𝔽pⁿ → 𝔽p`) as an **opaque ring variable**; the
//! combination layer supplies everything EUF knows about those variables
//! as ordinary literals (asserted equalities/disequalities plus the
//! congruences `x = y ⟹ f(x) = f(y)`). This module computes those
//! consequences: a congruence closure over the FF-sorted subterms of the
//! goal's atoms.
//!
//! **Why a second closure.** `crate::euf` is an incremental, trail-rewind
//! engine fused to the CDCL(T) search (proof forests, watched atoms,
//! scope trails). The FF combination needs a *batch* check over a fixed
//! term set with no undo. Rather than couple the eager FF dispatch to the
//! CDCL(T) e-graph state, this is a deliberately small, from-scratch
//! closure. Term counts here are the applications and subterms of the
//! goal's FF atoms, not circuit scale.
//!
//! **The fixpoint.** A merge re-signs the applications that take a member
//! of the losing class as an argument – each is looked up in the signature
//! table under its new (function, argument-representative) key and merged
//! with the application already there – and a merge of two applications is
//! itself a merge, so the work runs through an explicit queue until it
//! runs out ([`CongruenceClosure::propagate`]). The signature table is
//! kept across merges. An entry whose application was re-signed is left
//! behind under its old key, and that key can never be looked up again: a
//! signature changes only when one of its argument classes changes root,
//! and a root that lost a union is never a root again (so no `find` ever
//! produces it). A lookup therefore meets an entry exactly while the entry
//! still describes its application – the "no stale entry is ever read"
//! property, by an argument rather than by the rebuild it used to be
//! bought with: one full rebuild per level made `x = y ⟹ fⁿ(x) = fⁿ(y)`
//! a quadratic walk.
//!
//! Determinism: nodes are numbered in registration order (a fixed DFS
//! over the caller's index-sorted atom list), applications are signed in
//! index order, and classes are reported by ascending node id. The
//! partition a fixpoint reaches is the congruence closure whichever
//! congruent pair merged first, so no merge order and no hash-iteration
//! order feeds any output.

use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::interner::Spur;
use nixie_core::sort::SortKind;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;

/// A node in the closure: an FF-sorted term (leaf, compound arithmetic
/// term, or uninterpreted application).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NodeId(u32);

/// Batch congruence closure over FF-sorted terms.
///
/// Terms are added with [`CongruenceClosure::register_dag`]; equalities
/// with [`CongruenceClosure::merge`]; the congruence fixpoint runs in
/// [`CongruenceClosure::propagate`]. Disequalities are the caller's to
/// check against [`CongruenceClosure::are_equal`] – the closure only
/// ever merges.
#[derive(Debug, Default)]
pub struct CongruenceClosure {
    /// Node id → term.
    nodes: Vec<TermId>,
    /// Term → node id.
    node_of: FxHashMap<TermId, NodeId>,
    /// Union-find parent (index into `nodes`).
    parent: Vec<u32>,
    /// Union-find rank.
    rank: Vec<u8>,
    /// For application nodes: the function symbol and the *term ids* of
    /// the arguments (`None` for leaves and compound arithmetic terms,
    /// which have no congruence axiom of their own).
    app_info: Vec<Option<(Spur, SmallVec<[TermId; 4]>)>>,
    /// The members of each class, at the class's root (a node that is not
    /// a root holds nothing here). A class that loses a union hands its
    /// list to `pending` and the queue later appends it to the root's.
    class_members: Vec<SmallVec<[u32; 2]>>,
    /// For each node, the application nodes that take it as an argument
    /// (once each, whatever the arity repeats), for the applications
    /// `app_info[..listed]` covers.
    use_list: Vec<SmallVec<[u32; 2]>>,
    /// How many entries of `app_info` the use lists cover.
    listed: usize,
    /// How many entries of `app_info` have been offered to `signature`, in
    /// index order.
    signed: usize,
    /// (function, argument representatives) → the first application signed
    /// under that key. Kept across merges; see the module doc for why an
    /// entry left under a dead key is never read.
    signature: FxHashMap<(Spur, SmallVec<[u32; 4]>), u32>,
    /// The member lists of the classes that lost a union and whose parent
    /// applications have yet to be re-signed.
    pending: Vec<Vec<u32>>,
    /// How many signatures [`sign`](Self::sign) looked up – the work of the
    /// fixpoint, which the tests bound.
    #[cfg(test)]
    signs: usize,
}

impl CongruenceClosure {
    /// An empty closure.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    fn alloc(&mut self, term: TermId) -> NodeId {
        let id = NodeId(self.nodes.len() as u32);
        self.nodes.push(term);
        self.parent.push(id.0);
        self.rank.push(0);
        self.app_info.push(None);
        self.class_members.push(SmallVec::from_slice(&[id.0]));
        self.use_list.push(SmallVec::new());
        self.node_of.insert(term, id);
        id
    }

    /// The node of a term, if registered.
    #[must_use]
    pub fn node(&self, term: TermId) -> Option<NodeId> {
        self.node_of.get(&term).copied()
    }

    /// Whether a term's sort is a finite field (any modulus).
    fn term_is_ff(manager: &TermManager, t: TermId) -> bool {
        manager
            .get(t)
            .and_then(|term| manager.sorts.get(term.sort).map(|s| &s.kind))
            .is_some_and(|kind| matches!(kind, SortKind::FiniteField(_)))
    }

    /// Register every FF-sorted subterm of a literal's DAG as a node
    /// (applications additionally record their signature). Non-FF
    /// structure is walked through (Bool connectives) but never
    /// registered. One frame stack; user DAGs can be arbitrarily deep.
    pub fn register_dag(&mut self, manager: &TermManager, root: TermId) {
        let mut visited: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
        let mut stack: Vec<TermId> = vec![root];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            let Some(term) = manager.get(t) else {
                continue;
            };
            if Self::term_is_ff(manager, t) {
                let id = self
                    .node_of
                    .get(&t)
                    .copied()
                    .unwrap_or_else(|| self.alloc(t));
                if let TermKind::Apply { func, args } = &term.kind {
                    self.app_info[id.0 as usize] =
                        Some((*func, SmallVec::from_slice(args.as_slice())));
                }
                // FF subterms of an FF term are still walked: they may be
                // application arguments or equality sides in their own
                // right, and registering them costs one slot each.
                stack.extend(nixie_core::ast::get_children(&term.kind));
            } else {
                // Boolean structure and other connectives: walk through.
                stack.extend(nixie_core::ast::get_children(&term.kind));
            }
        }
    }

    /// Union-find find (no compression: rank-bounded depth ≤ log₂ n is
    /// ample at batch scale, and a read-only find keeps the query API
    /// `&self`).
    fn find(&self, mut n: u32) -> u32 {
        while self.parent[n as usize] != n {
            n = self.parent[n as usize];
        }
        n
    }

    /// Union by rank. Returns the new root.
    fn union(&mut self, a: u32, b: u32) -> u32 {
        let mut ra = self.find(a);
        let mut rb = self.find(b);
        if ra == rb {
            return ra;
        }
        if self.rank[ra as usize] < self.rank[rb as usize] {
            std::mem::swap(&mut ra, &mut rb);
        }
        self.parent[rb as usize] = ra;
        if self.rank[ra as usize] == self.rank[rb as usize] {
            self.rank[ra as usize] += 1;
        }
        // `rb`'s class just joined `ra`'s. Its members are the list whose
        // parent applications `propagate` re-signs; the queue then appends
        // them to the root that class has by then (it may have merged
        // again). `ra`'s own members keep their root, so no application
        // that takes one of them as an argument changes signature.
        let losers = std::mem::take(&mut self.class_members[rb as usize]);
        self.pending.push(losers.into_iter().collect());
        ra
    }

    /// Assert `a = b` (both must be registered). Merges their classes
    /// immediately; run [`propagate`](Self::propagate) once after a batch
    /// of merges to close under congruence.
    pub fn merge(&mut self, a: TermId, b: TermId) {
        if let (Some(x), Some(y)) = (self.node_of.get(&a), self.node_of.get(&b)) {
            self.union(x.0, y.0);
        }
    }

    /// Close under the congruence axiom to a fixpoint: no two applications
    /// of one function with pairwise equal argument classes stay in
    /// different classes.
    ///
    /// Three steps. The use lists are extended to the applications
    /// registered since the last call; the applications not yet signed are
    /// signed in index order (a signature already in the table merges the
    /// two applications, a new one is recorded); and the queue of classes
    /// that lost a union is drained – every application that takes a member
    /// of such a class as an argument is signed again under the
    /// representatives its arguments have now. Each step's merges queue
    /// more, until none do.
    pub fn propagate(&mut self) {
        for idx in self.listed..self.app_info.len() {
            let Some((_, args)) = &self.app_info[idx] else {
                continue;
            };
            // An argument never registered (its term was not part of any
            // walked DAG, or is not field-sorted) cannot be canonicalized;
            // registering happens over the same DAGs the caller walks, so
            // that is a caller bug – the parent is skipped rather than
            // fabricated a representative, in every call as in every round
            // before.
            let mut arg_nodes: SmallVec<[u32; 4]> = SmallVec::new();
            let mut ok = true;
            for arg in args {
                match self.node_of.get(arg) {
                    Some(n) => {
                        if !arg_nodes.contains(&n.0) {
                            arg_nodes.push(n.0);
                        }
                    }
                    None => {
                        ok = false;
                        break;
                    }
                }
            }
            if ok {
                for &n in &arg_nodes {
                    self.use_list[n as usize].push(idx as u32);
                }
            }
        }
        self.listed = self.app_info.len();

        for idx in self.signed..self.app_info.len() {
            if self.app_info[idx].is_some() {
                self.sign(idx as u32);
            }
        }
        self.signed = self.app_info.len();

        while let Some(losers) = self.pending.pop() {
            for &m in &losers {
                for i in 0..self.use_list[m as usize].len() {
                    let parent_app = self.use_list[m as usize][i];
                    self.sign(parent_app);
                }
            }
            // `losers[0]` is a member of the class it became part of.
            let root = self.find(losers[0]);
            self.class_members[root as usize].extend_from_slice(&losers);
        }
    }

    /// Offer application `p` to the signature table under the signature its
    /// arguments have now: the application already signed under it is
    /// merged with `p`, or `p` is recorded as that one. An application with
    /// an argument that was never registered is skipped (see
    /// [`propagate`](Self::propagate)).
    fn sign(&mut self, p: u32) {
        let Some((func, args)) = &self.app_info[p as usize] else {
            return;
        };
        #[cfg(test)]
        {
            self.signs += 1;
        }
        let mut reps: SmallVec<[u32; 4]> = SmallVec::new();
        for arg in args {
            match self.node_of.get(arg) {
                Some(n) => reps.push(self.find(n.0)),
                None => return,
            }
        }
        let key = (*func, reps);
        match self.signature.get(&key) {
            Some(&other) => {
                let rp = self.find(p);
                let ro = self.find(other);
                if rp != ro {
                    self.union(rp, ro);
                }
            }
            None => {
                self.signature.insert(key, p);
            }
        }
    }

    /// Whether two registered terms are in the same class. `None` when a
    /// term was never registered.
    #[must_use]
    pub fn are_equal(&self, a: TermId, b: TermId) -> Option<bool> {
        match (self.node_of.get(&a), self.node_of.get(&b)) {
            (Some(x), Some(y)) => Some(self.find(x.0) == self.find(y.0)),
            _ => None,
        }
    }

    /// The classes, deterministically: each class ascending by node id
    /// (registration order), the class list ascending by first member.
    /// Singleton classes are omitted – the caller consumes the implied
    /// equalities, and a lone term implies nothing.
    #[must_use]
    pub fn nonsingleton_classes(&self) -> Vec<Vec<TermId>> {
        let mut by_root: FxHashMap<u32, Vec<TermId>> = FxHashMap::default();
        for (idx, &term) in self.nodes.iter().enumerate() {
            by_root.entry(self.find(idx as u32)).or_default().push(term);
        }
        let mut classes: Vec<Vec<TermId>> = by_root
            .into_values()
            .filter(|c| c.len() > 1)
            .map(|mut c| {
                c.sort_unstable();
                c
            })
            .collect();
        classes.sort_by(|a, b| a[0].cmp(&b[0]));
        classes
    }

    /// Every registered application node's term, ascending (used by the
    /// combination layer's function-hood scan over candidate models).
    #[must_use]
    pub fn application_terms(&self) -> Vec<TermId> {
        let mut apps: Vec<TermId> = self
            .app_info
            .iter()
            .enumerate()
            .filter_map(|(idx, info)| info.as_ref().map(|_| self.nodes[idx]))
            .collect();
        apps.sort_unstable();
        apps
    }

    /// The (function, argument terms) of a registered application.
    #[must_use]
    pub fn application_signature(&self, term: TermId) -> Option<(Spur, SmallVec<[TermId; 4]>)> {
        let id = self.node_of.get(&term)?.0 as usize;
        self.app_info[id].clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use nixie_core::ast::TermManager;
    use num_bigint::BigUint;

    fn ff_manager() -> TermManager {
        let mut m = TermManager::new();
        m.sorts
            .finite_field(BigUint::from(7u32))
            .expect("prime modulus");
        m
    }

    fn ff7(m: &mut TermManager) -> nixie_core::sort::SortId {
        m.sorts
            .find_finite_field(&BigUint::from(7u32))
            .expect("field interned")
    }

    #[test]
    fn congruence_after_arg_merge() {
        let mut m = ff_manager();
        let s = ff7(&mut m);
        let x = m.mk_var("x", s);
        let y = m.mk_var("y", s);
        let fx = m.mk_apply("f", [x], s);
        let fy = m.mk_apply("f", [y], s);
        let eq = m.mk_eq(x, y);
        let mut cc = CongruenceClosure::new();
        cc.register_dag(&m, eq);
        cc.register_dag(&m, fx);
        cc.register_dag(&m, fy);
        cc.merge(x, y);
        cc.propagate();
        assert_eq!(cc.are_equal(fx, fy), Some(true));
    }

    #[test]
    fn no_congruence_without_merge() {
        let mut m = ff_manager();
        let s = ff7(&mut m);
        let x = m.mk_var("x", s);
        let y = m.mk_var("y", s);
        let fx = m.mk_apply("f", [x], s);
        let fy = m.mk_apply("f", [y], s);
        let _ = m.mk_eq(x, y);
        let mut cc = CongruenceClosure::new();
        cc.register_dag(&m, x);
        cc.register_dag(&m, y);
        cc.propagate();
        assert_eq!(cc.are_equal(fx, fy), None);
        // Register the applications themselves: still separate classes.
        cc.register_dag(&m, fx);
        cc.register_dag(&m, fy);
        cc.propagate();
        assert_eq!(cc.are_equal(fx, fy), Some(false));
    }

    #[test]
    fn transitive_congruence_chain() {
        // f(x) = f(y) once x = y, g(f(x)) = g(f(y)) transitively.
        let mut m = ff_manager();
        let s = ff7(&mut m);
        let x = m.mk_var("x", s);
        let y = m.mk_var("y", s);
        let fx = m.mk_apply("f", [x], s);
        let fy = m.mk_apply("f", [y], s);
        let gfx = m.mk_apply("g", [fx], s);
        let gfy = m.mk_apply("g", [fy], s);
        let mut cc = CongruenceClosure::new();
        cc.register_dag(&m, gfx);
        cc.register_dag(&m, gfy);
        cc.merge(x, y);
        cc.propagate();
        assert_eq!(cc.are_equal(fx, fy), Some(true));
        assert_eq!(cc.are_equal(gfx, gfy), Some(true));
    }

    #[test]
    fn binary_function_congruence() {
        let mut m = ff_manager();
        let s = ff7(&mut m);
        let x1 = m.mk_var("x1", s);
        let x2 = m.mk_var("x2", s);
        let y1 = m.mk_var("y1", s);
        let y2 = m.mk_var("y2", s);
        let h1 = m.mk_apply("h", [x1, x2], s);
        let h2 = m.mk_apply("h", [y1, y2], s);
        let mut cc = CongruenceClosure::new();
        cc.register_dag(&m, h1);
        cc.register_dag(&m, h2);
        cc.merge(x1, y1);
        cc.propagate();
        assert_eq!(
            cc.are_equal(h1, h2),
            Some(false),
            "one arg alone is not congruence"
        );
        cc.merge(x2, y2);
        cc.propagate();
        assert_eq!(cc.are_equal(h1, h2), Some(true));
    }

    #[test]
    fn classes_are_deterministic_and_complete() {
        let mut m = ff_manager();
        let s = ff7(&mut m);
        let a = m.mk_var("a", s);
        let b = m.mk_var("b", s);
        let c = m.mk_var("c", s);
        let d = m.mk_var("d", s);
        let mut cc = CongruenceClosure::new();
        for t in [a, b, c, d] {
            cc.register_dag(&m, t);
        }
        cc.merge(a, b);
        cc.merge(b, c);
        cc.propagate();
        let classes = cc.nonsingleton_classes();
        assert_eq!(classes.len(), 1, "one nonsingleton class: {classes:?}");
        assert_eq!(classes[0], vec![a, b, c]);
    }

    /// A plain union-find over terms, for the oracle below.
    struct Terms(FxHashMap<TermId, TermId>);

    impl Terms {
        fn new(terms: &[TermId]) -> Self {
            Self(terms.iter().map(|&t| (t, t)).collect())
        }

        fn find(&mut self, t: TermId) -> TermId {
            let mut root = t;
            while self.0[&root] != root {
                root = self.0[&root];
            }
            let mut cur = t;
            while self.0[&cur] != cur {
                let next = self.0[&cur];
                self.0.insert(cur, root);
                cur = next;
            }
            root
        }

        fn union(&mut self, a: TermId, b: TermId) -> bool {
            let (ra, rb) = (self.find(a), self.find(b));
            if ra == rb {
                return false;
            }
            self.0.insert(rb, ra);
            true
        }
    }

    /// The closure is exactly the congruence closure of `merges`: its
    /// classes equal the definition's – the asserted pairs, then every two
    /// applications of one function with pairwise-equal argument classes,
    /// until nothing changes – and no two such applications are left apart.
    fn assert_is_the_closure(cc: &CongruenceClosure, merges: &[(TermId, TermId)]) {
        let mut oracle = Terms::new(&cc.nodes);
        for &(a, b) in merges {
            oracle.union(a, b);
        }
        let apps: Vec<Option<(Spur, Vec<TermId>)>> = cc
            .app_info
            .iter()
            .map(|info| info.as_ref().map(|(func, args)| (*func, args.to_vec())))
            .collect();
        loop {
            let mut changed = false;
            for (i, app_i) in apps.iter().enumerate() {
                for (j, app_j) in apps.iter().enumerate().skip(i + 1) {
                    let (Some((func_i, args_i)), Some((func_j, args_j))) = (app_i, app_j) else {
                        continue;
                    };
                    let (t_i, t_j) = (cc.nodes[i], cc.nodes[j]);
                    if func_i != func_j
                        || args_i.len() != args_j.len()
                        || !args_i
                            .iter()
                            .chain(args_j)
                            .all(|a| cc.node_of.contains_key(a))
                    {
                        continue;
                    }
                    let congruent = args_i
                        .iter()
                        .zip(args_j)
                        .all(|(&a, &b)| oracle.find(a) == oracle.find(b));
                    if congruent && oracle.union(t_i, t_j) {
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        for (i, &a) in cc.nodes.iter().enumerate() {
            for &b in &cc.nodes[i + 1..] {
                assert_eq!(
                    cc.are_equal(a, b),
                    Some(oracle.find(a) == oracle.find(b)),
                    "the closure and the definition disagree on {a:?} and {b:?}"
                );
            }
        }
        for (i, _) in cc.nodes.iter().enumerate() {
            let root = cc.find(i as u32);
            assert!(
                cc.class_members[root as usize].contains(&(i as u32)),
                "node {i} missing from its root's member list"
            );
        }
        assert!(cc.pending.is_empty(), "a class left un-appended");
    }

    /// The fixpoint the retired rule computed, on a second closure: every
    /// round rebuilt the signature table from scratch and merged every pair
    /// it found, until a round found none. The union is the retired one –
    /// rank alone, no member list.
    fn propagate_in_rounds(cc: &mut CongruenceClosure) {
        loop {
            let mut sig: FxHashMap<(Spur, SmallVec<[u32; 4]>), u32> = FxHashMap::default();
            let mut merges: Vec<(u32, u32)> = Vec::new();
            for (idx, info) in cc.app_info.iter().enumerate() {
                let Some((func, args)) = info else {
                    continue;
                };
                let mut reps: SmallVec<[u32; 4]> = SmallVec::new();
                let mut ok = true;
                for &arg in args {
                    match cc.node_of.get(&arg) {
                        Some(n) => reps.push(cc.find(n.0)),
                        None => {
                            ok = false;
                            break;
                        }
                    }
                }
                if !ok {
                    continue;
                }
                let key = (*func, reps);
                match sig.get(&key) {
                    Some(&other) => {
                        if cc.find(other) != cc.find(idx as u32) {
                            merges.push((idx as u32, other));
                        }
                    }
                    None => {
                        sig.insert(key, idx as u32);
                    }
                }
            }
            if merges.is_empty() {
                return;
            }
            for (a, b) in merges {
                let mut ra = cc.find(a);
                let mut rb = cc.find(b);
                if ra == rb {
                    continue;
                }
                if cc.rank[ra as usize] < cc.rank[rb as usize] {
                    std::mem::swap(&mut ra, &mut rb);
                }
                cc.parent[rb as usize] = ra;
                if cc.rank[ra as usize] == cc.rank[rb as usize] {
                    cc.rank[ra as usize] += 1;
                }
            }
        }
    }

    struct Lcg(u64);

    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0 >> 33
        }

        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }
    }

    /// A random goal over 𝔽₇: six variables, three constants, three sums,
    /// then `layers` layers of four applications each, mostly over the
    /// previous layer and the current one – shared subterms, chains and
    /// diamonds of arbitrary depth.
    fn random_terms(m: &mut TermManager, rng: &mut Lcg, layers: usize) -> Vec<TermId> {
        let s = ff7(m);
        let field = match m.sorts.get(s).map(|sort| sort.kind.clone()) {
            Some(SortKind::FiniteField(id)) => id,
            _ => panic!("field sort"),
        };
        let mut all: Vec<TermId> = Vec::new();
        for i in 0..6 {
            all.push(m.mk_var(&format!("v{i}"), s));
        }
        for i in 0..3i32 {
            all.push(m.mk_ff_const(field, i.into()).expect("constant"));
        }
        for _ in 0..3 {
            let a = all[rng.below(all.len())];
            let b = all[rng.below(all.len())];
            all.push(m.mk_ff_add([a, b]).expect("field terms"));
        }
        for layer in 0..layers {
            let mut built: Vec<TermId> = Vec::new();
            for k in 0..4 {
                let arity = 1 + rng.below(2);
                let args: Vec<TermId> = (0..arity)
                    .map(|_| {
                        if layer > 0 && !built.is_empty() && rng.below(4) != 0 {
                            built[rng.below(built.len())]
                        } else {
                            all[rng.below(all.len())]
                        }
                    })
                    .collect();
                built.push(m.mk_apply(&format!("f{layer}_{k}"), args, s));
            }
            all.extend(built);
        }
        all
    }

    /// On random goals, with merges and further registrations interleaved
    /// over several `propagate` calls, the queued fixpoint reaches the
    /// partition the retired rounds reached and the definition prescribes.
    #[test]
    fn the_queued_fixpoint_is_the_rounds_and_the_definition() {
        let mut rng = Lcg(0xc099_e5e5_0001);
        for round in 0..400 {
            let mut m = ff_manager();
            let layers = 3 + rng.below(3);
            let all = random_terms(&mut m, &mut rng, layers);
            let extra = random_terms(&mut m, &mut rng, 1);
            let mut cc = CongruenceClosure::new();
            let mut retired = CongruenceClosure::new();
            let mut merges: Vec<(TermId, TermId)> = Vec::new();
            let mut registered = 0;
            for step in 0..4 {
                // Some terms of the goal join between fixpoints.
                let up_to = (registered + 5 + rng.below(6)).min(all.len());
                for &t in &all[registered..up_to] {
                    cc.register_dag(&m, t);
                    retired.register_dag(&m, t);
                }
                registered = up_to;
                for _ in 0..1 + rng.below(3) {
                    let a = all[rng.below(registered.max(1))];
                    let b = all[rng.below(registered.max(1))];
                    cc.merge(a, b);
                    retired.merge(a, b);
                    merges.push((a, b));
                }
                cc.propagate();
                propagate_in_rounds(&mut retired);
                for (i, &a) in cc.nodes.iter().enumerate() {
                    for &b in &cc.nodes[i + 1..] {
                        assert_eq!(
                            cc.are_equal(a, b),
                            retired.are_equal(a, b),
                            "round {round}, step {step}: the queue and the rounds disagree on {a:?}, {b:?}"
                        );
                    }
                }
                assert_is_the_closure(&cc, &merges);
                // A second propagation with nothing new changes nothing.
                cc.propagate();
                assert_is_the_closure(&cc, &merges);
            }
            // Terms registered after every merge are signed at the next call.
            for &t in &extra {
                cc.register_dag(&m, t);
                retired.register_dag(&m, t);
            }
            cc.propagate();
            propagate_in_rounds(&mut retired);
            for (i, &a) in cc.nodes.iter().enumerate() {
                for &b in &cc.nodes[i + 1..] {
                    assert_eq!(cc.are_equal(a, b), retired.are_equal(a, b));
                }
            }
            assert_is_the_closure(&cc, &merges);
        }
    }

    /// `x = y ⟹ fⁿ(x) = fⁿ(y)`: one re-signing per level. The retired
    /// rounds took one whole pass over every application per level – n
    /// passes over 2n applications for a chain of depth n.
    #[test]
    fn a_chain_closes_in_one_resigning_per_level() {
        let mut m = ff_manager();
        let s = ff7(&mut m);
        let x = m.mk_var("x", s);
        let y = m.mk_var("y", s);
        let n = 500;
        let (mut cx, mut cy) = (x, y);
        for _ in 0..n {
            cx = m.mk_apply("f", [cx], s);
            cy = m.mk_apply("f", [cy], s);
        }
        let mut cc = CongruenceClosure::new();
        cc.register_dag(&m, cx);
        cc.register_dag(&m, cy);
        cc.propagate();
        assert_eq!(cc.are_equal(cx, cy), Some(false));
        assert_eq!(cc.signs, 2 * n, "every application is signed once");
        cc.merge(x, y);
        cc.propagate();
        assert_eq!(cc.are_equal(cx, cy), Some(true));
        assert_eq!(cc.signs, 3 * n, "one re-signing per level of the chain");
    }

    /// Classes that lose before the first `propagate` still end up whole on
    /// their root's list: five merges in a row, one call.
    #[test]
    fn merges_before_a_propagate_queue_their_chunks() {
        let mut m = ff_manager();
        let s = ff7(&mut m);
        let vars: Vec<TermId> = (0..6).map(|i| m.mk_var(&format!("w{i}"), s)).collect();
        let mut cc = CongruenceClosure::new();
        for &v in &vars {
            cc.register_dag(&m, v);
        }
        for pair in vars.windows(2) {
            cc.merge(pair[0], pair[1]);
        }
        cc.propagate();
        assert_eq!(cc.nonsingleton_classes(), vec![vars.clone()]);
        let root = cc.find(0);
        assert_eq!(cc.class_members[root as usize].len(), vars.len());
    }
}
