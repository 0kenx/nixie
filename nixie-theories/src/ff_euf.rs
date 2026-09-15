//! Batch congruence closure over finite-field-sorted terms — the EUF half
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
//! closure. The congruence fixpoint rebuilds its signature table from
//! scratch each round (no incremental signature maintenance), trading a
//! log factor for an audit trail the incremental engine cannot offer —
//! the same "no stale entries, ever" property that
//! `euf/solver/congruence.rs`'s `update_sig_entry` exists to restore after
//! the fact. Term counts here are the applications and subterms of the
//! goal's FF atoms, not circuit scale.
//!
//! Determinism: nodes are numbered in registration order (a fixed DFS
//! over the caller's index-sorted atom list), classes are reported by
//! ascending node id, and the fixpoint scans parents in index order — no
//! hash-iteration order feeds any output.

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
/// check against [`CongruenceClosure::are_equal`] — the closure only
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

    /// Close under the congruence axiom to a fixpoint: while some two
    /// application nodes have equal (function, argument-class) signatures
    /// but different classes, merge them. Each round rebuilds the
    /// signature table from the current representatives — a stale entry
    /// is structurally impossible because no entry outlives its round.
    pub fn propagate(&mut self) {
        loop {
            let mut sig: FxHashMap<(Spur, SmallVec<[u32; 4]>), u32> = FxHashMap::default();
            let mut merges: Vec<(u32, u32)> = Vec::new();
            for (idx, info) in self.app_info.iter().enumerate() {
                let Some((func, args)) = info else {
                    continue;
                };
                // Canonicalize the signature with the current
                // representatives. An argument never registered (its term
                // was not part of any walked DAG) cannot be canonicalized;
                // registering happens over the same DAGs the caller walks,
                // so that is a caller bug — skip the parent rather than
                // fabricate a representative.
                let mut reps: SmallVec<[u32; 4]> = SmallVec::new();
                let mut ok = true;
                for &arg in args {
                    match self.node_of.get(&arg) {
                        Some(n) => reps.push(self.find(n.0)),
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
                        if self.find(other) != self.find(idx as u32) {
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
                self.union(a, b);
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
    /// Singleton classes are omitted — the caller consumes the implied
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

    fn ff_manager() -> TermManager {
        let mut m = TermManager::new();
        m.sorts
            .finite_field(num_bigint::BigUint::from(7u32))
            .expect("prime modulus");
        m
    }

    fn ff7(m: &mut TermManager) -> nixie_core::sort::SortId {
        m.sorts
            .find_finite_field(&num_bigint::BigUint::from(7u32))
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
}
