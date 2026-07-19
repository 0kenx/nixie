//! Array Theory Solver
//!
//! Implements the theory of extensional arrays using a combination
//! of read-over-write axioms and a delayed lemma approach.

#[allow(unused_imports)]
use crate::prelude::*;
use crate::theory::{EqualityNotification, Theory, TheoryCombination, TheoryId, TheoryResult};
use oxiz_core::ast::TermId;
use oxiz_core::error::Result;
#[cfg(feature = "profiling")]
use oxiz_core::profiling::{ProfilingCategory, ScopedTimer};

/// Represents a select operation: select(array, index)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct SelectOp {
    /// The array being read from
    array: u32,
    /// The index being accessed
    index: u32,
}

/// Represents a store operation: store(array, index, value)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct StoreOp {
    /// The original array
    array: u32,
    /// The index being written to
    index: u32,
    /// The value being written
    value: u32,
}

/// An array term (either a base array or a store result)
#[derive(Debug, Clone)]
#[allow(dead_code)]
enum ArrayTerm {
    /// A base array variable
    Base(u32),
    /// A store operation result
    Store {
        /// The underlying array
        base: u32,
        /// The store operation that created this
        store: StoreOp,
    },
}

/// A pending lemma to be instantiated
#[derive(Debug, Clone)]
enum PendingLemma {
    /// Read-over-write same: select(store(a, i, v), i) = v
    ReadOverWriteSame {
        /// The store operation
        store: StoreOp,
        /// The result array
        store_result: u32,
    },
    /// Read-over-write different: i ≠ j → select(store(a, i, v), j) = select(a, j)
    ReadOverWriteDiff {
        /// The store operation
        store: StoreOp,
        /// The result array
        store_result: u32,
        /// The select index
        select_index: u32,
    },
}

/// Array Theory Solver
#[derive(Debug)]
pub struct ArraySolver {
    /// Node counter
    next_node: u32,
    /// Term to node mapping
    term_to_node: FxHashMap<TermId, u32>,
    /// Node to term mapping
    node_to_term: Vec<Option<TermId>>,
    /// Array terms
    arrays: Vec<Option<ArrayTerm>>,
    /// Select operations: (select_node, SelectOp)
    selects: Vec<(u32, SelectOp)>,
    /// Store operations: (result_node, StoreOp)
    stores: Vec<(u32, StoreOp)>,
    /// Equivalence classes (simple union-find)
    parent: Vec<u32>,
    /// Trail for undo: (child, old_parent)
    trail: Vec<(u32, u32)>,
    /// Disequalities
    diseqs: Vec<(u32, u32, TermId)>,
    /// Pending lemmas to check
    pending_lemmas: Vec<PendingLemma>,
    /// Context stack for push/pop
    context_stack: Vec<ContextState>,
    /// Current conflicts (if any)
    current_conflict: Option<Vec<TermId>>,
    /// Shared equalities derived by array axioms for Nelson-Oppen combination.
    /// These arise from read-over-write and extensionality axioms.
    shared_equalities: Vec<EqualityNotification>,
    /// Append-only log of every `merge(a, b, reason)` call, used by
    /// `explain_equal` to reconstruct the actual chain of reasons that
    /// makes two nodes equal (the live `parent` union-find is path
    /// -compressed for fast `find()`, which discards the intermediate
    /// hops a proof/explanation would need). See `explain_equal`'s doc
    /// comment for the full rationale.
    merge_log: Vec<(u32, u32, TermId)>,
}

/// State for push/pop
#[derive(Debug, Clone)]
struct ContextState {
    num_nodes: usize,
    num_selects: usize,
    num_stores: usize,
    num_diseqs: usize,
    num_pending_lemmas: usize,
    num_trail: usize,
    num_merge_log: usize,
}

impl Default for ArraySolver {
    fn default() -> Self {
        Self::new()
    }
}

impl ArraySolver {
    /// Create a new array solver
    #[must_use]
    pub fn new() -> Self {
        Self {
            next_node: 0,
            term_to_node: FxHashMap::default(),
            node_to_term: Vec::new(),
            arrays: Vec::new(),
            selects: Vec::new(),
            stores: Vec::new(),
            parent: Vec::new(),
            trail: Vec::new(),
            diseqs: Vec::new(),
            pending_lemmas: Vec::new(),
            context_stack: Vec::new(),
            current_conflict: None,
            shared_equalities: Vec::new(),
            merge_log: Vec::new(),
        }
    }

    /// Create a new node
    fn new_node(&mut self) -> u32 {
        let id = self.next_node;
        self.next_node += 1;
        self.parent.push(id); // Initially its own parent
        self.node_to_term.push(None);
        self.arrays.push(None);
        id
    }

    /// Intern a term, returning its node
    pub fn intern(&mut self, term: TermId) -> u32 {
        if let Some(&node) = self.term_to_node.get(&term) {
            return node;
        }

        let node = self.new_node();
        self.term_to_node.insert(term, node);
        self.node_to_term[node as usize] = Some(term);
        node
    }

    /// Intern an array variable
    pub fn intern_array(&mut self, term: TermId) -> u32 {
        let node = self.intern(term);
        if self.arrays[node as usize].is_none() {
            self.arrays[node as usize] = Some(ArrayTerm::Base(node));
        }
        node
    }

    /// Intern a select operation: select(array, index)
    pub fn intern_select(&mut self, term: TermId, array: u32, index: u32) -> u32 {
        let node = self.intern(term);
        let select = SelectOp { array, index };
        self.selects.push((node, select));

        // Check for immediate read-over-write lemmas
        self.check_read_over_write(node, &select);

        node
    }

    /// Intern a store operation: store(array, index, value)
    pub fn intern_store(&mut self, term: TermId, array: u32, index: u32, value: u32) -> u32 {
        let node = self.intern(term);
        let store = StoreOp {
            array,
            index,
            value,
        };
        self.stores.push((node, store));
        self.arrays[node as usize] = Some(ArrayTerm::Store { base: array, store });

        // Add read-over-write-same lemma
        self.pending_lemmas.push(PendingLemma::ReadOverWriteSame {
            store,
            store_result: node,
        });

        node
    }

    /// Check for read-over-write lemmas when a new select is added
    fn check_read_over_write(&mut self, _select_node: u32, select: &SelectOp) {
        // Find all stores on the same array
        for (store_result, store) in &self.stores {
            if self.find(store.array) == self.find(select.array) || *store_result == select.array {
                // Check if indices are the same or different
                if self.find(store.index) == self.find(select.index) {
                    // Same index: select(store(a, i, v), i) = v
                    // Merge select_node with store.value
                    self.pending_lemmas.push(PendingLemma::ReadOverWriteSame {
                        store: *store,
                        store_result: *store_result,
                    });
                } else {
                    // Different indices: may need read-over-write-different lemma
                    self.pending_lemmas.push(PendingLemma::ReadOverWriteDiff {
                        store: *store,
                        store_result: *store_result,
                        select_index: select.index,
                    });
                }
            }
        }
    }

    /// Find the representative of a node (without path compression)
    fn find(&self, mut node: u32) -> u32 {
        while self.parent[node as usize] != node {
            node = self.parent[node as usize];
        }
        node
    }

    /// Find with path compression (when we have mutable access)
    /// Records trail for incremental undo
    fn find_compress(&mut self, mut node: u32) -> u32 {
        let mut root = node;
        while self.parent[root as usize] != root {
            root = self.parent[root as usize];
        }
        // Path compression with trail recording
        while self.parent[node as usize] != root {
            let parent = self.parent[node as usize];
            // Record old parent for undo
            self.trail.push((node, parent));
            self.parent[node as usize] = root;
            node = parent;
        }
        root
    }

    /// Check if two nodes are equivalent
    pub fn are_equal(&self, a: u32, b: u32) -> bool {
        self.find(a) == self.find(b)
    }

    /// Check if two nodes are PROVEN disequal (an explicit disequality was
    /// asserted between their equivalence classes), as opposed to merely
    /// "not currently known equal". These are different: two nodes with no
    /// asserted disequality can still become equal later (e.g. once
    /// Nelson-Oppen propagates an arithmetic equality between the index
    /// expressions they represent), so `!are_equal(a, b)` is NOT a sound
    /// stand-in for "a and b are different indices" -- only an explicit
    /// disequality is.
    fn is_proven_disequal(&self, a: u32, b: u32) -> bool {
        let (ra, rb) = (self.find(a), self.find(b));
        self.diseqs.iter().any(|&(lhs, rhs, _)| {
            (self.find(lhs) == ra && self.find(rhs) == rb)
                || (self.find(lhs) == rb && self.find(rhs) == ra)
        })
    }

    /// Merge two equivalence classes
    pub fn merge(&mut self, a: u32, b: u32, reason: TermId) -> Result<()> {
        let root_a = self.find_compress(a);
        let root_b = self.find_compress(b);

        // Recorded regardless of whether `a`/`b` were already in the same
        // class: `explain_equal` replays this log to reconstruct the full
        // reason chain between any two nodes, so every asserted merge
        // needs to be in it (a merge between already-equal nodes is still
        // a valid alternate edge/reason for that equality).
        self.merge_log.push((a, b, reason));

        if root_a != root_b {
            // Record old parent for undo
            self.trail.push((root_b, root_b));
            // Union by rank (simplified: always make root_a the parent)
            self.parent[root_b as usize] = root_a;

            // Check for conflicts with disequalities
            for &(lhs, rhs, diseq_reason) in self.diseqs.clone().iter() {
                if self.find(lhs) == self.find(rhs) {
                    // The conflict is `lhs = rhs` (via the merge chain
                    // that connects them) AND `lhs != rhs` (`diseq_reason`).
                    // Previously only the single merge reason that
                    // happened to trigger this check (`reason`) and
                    // `diseq_reason` were recorded, omitting every OTHER
                    // merge in the chain that actually makes `lhs` and
                    // `rhs` equal -- an over-strong (unsound) learned
                    // conflict clause, since it implicitly claimed the
                    // conflict follows from just those two facts alone.
                    let mut conflict = self.explain_equal(lhs, rhs);
                    conflict.push(diseq_reason);
                    self.current_conflict = Some(conflict);
                    return Ok(());
                }
            }
        }

        Ok(())
    }

    /// Assert a disequality
    pub fn assert_diseq(&mut self, a: u32, b: u32, reason: TermId) {
        self.diseqs.push((a, b, reason));

        // Check for immediate conflict: `a` and `b` might already be
        // forced equal by a PRIOR chain of merges. Include that whole
        // chain in the conflict, not just this disequality's own reason
        // (which alone does not explain why `a` and `b` were equal).
        if self.find(a) == self.find(b) {
            let mut conflict = self.explain_equal(a, b);
            conflict.push(reason);
            self.current_conflict = Some(conflict);
        }
    }

    /// Reconstruct the chain of merge reasons that makes `a` and `b` equal.
    ///
    /// The live `parent` union-find is path-compressed for fast `find()`
    /// (see `find_compress`), which rewires a node directly to its root
    /// and discards the intermediate hops -- exactly the information a
    /// conflict EXPLANATION needs (which specific asserted equalities are
    /// actually responsible for `a = b`). Instead of compressing, this
    /// replays `merge_log` (every `merge` call ever made, regardless of
    /// whether it changed the union-find) as an undirected graph of
    /// `(node, node, reason)` edges and does a BFS from `a` to `b`,
    /// collecting the reasons of the edges on the path found. If `a` and
    /// `b` are not (yet) in the same class, or no path is found in the
    /// log for some reason, this returns whatever partial chain BFS
    /// reached rather than fabricating a reason.
    fn explain_equal(&self, a: u32, b: u32) -> Vec<TermId> {
        if a == b {
            return Vec::new();
        }

        let mut adjacency: FxHashMap<u32, Vec<(u32, TermId)>> = FxHashMap::default();
        for &(x, y, reason) in &self.merge_log {
            adjacency.entry(x).or_default().push((y, reason));
            adjacency.entry(y).or_default().push((x, reason));
        }

        let mut visited: FxHashSet<u32> = FxHashSet::default();
        visited.insert(a);
        let mut queue: std::collections::VecDeque<u32> = std::collections::VecDeque::new();
        queue.push_back(a);
        // came_from[node] = (predecessor, reason for the edge used to reach it)
        let mut came_from: FxHashMap<u32, (u32, TermId)> = FxHashMap::default();

        while let Some(node) = queue.pop_front() {
            if node == b {
                break;
            }
            if let Some(neighbors) = adjacency.get(&node) {
                for &(next, reason) in neighbors {
                    if visited.insert(next) {
                        came_from.insert(next, (node, reason));
                        queue.push_back(next);
                    }
                }
            }
        }

        let mut chain = Vec::new();
        let mut cur = b;
        while let Some(&(prev, reason)) = came_from.get(&cur) {
            chain.push(reason);
            cur = prev;
            if cur == a {
                break;
            }
        }
        chain
    }

    /// Process pending lemmas
    fn process_lemmas(&mut self) -> Result<TheoryResult> {
        let lemmas = core::mem::take(&mut self.pending_lemmas);
        let mut propagations: Vec<(TermId, Vec<TermId>)> = Vec::new();
        let mut pending_merges: Vec<(u32, u32)> = Vec::new();

        for lemma in lemmas {
            match lemma {
                PendingLemma::ReadOverWriteSame {
                    store,
                    store_result,
                } => {
                    // Find select(store(a, i, v), i) and equate with v
                    for (select_node, select) in &self.selects {
                        if self.find(select.array) == self.find(store_result)
                            && self.find(select.index) == self.find(store.index)
                        {
                            // select(store(a, i, v), i) = v
                            if !self.are_equal(*select_node, store.value) {
                                // Generate equality propagation
                                if let (Some(sel_term), Some(val_term)) = (
                                    self.node_to_term[*select_node as usize],
                                    self.node_to_term[store.value as usize],
                                ) {
                                    propagations.push((sel_term, vec![val_term]));
                                }
                                pending_merges.push((*select_node, store.value));
                            }
                        }
                    }
                }
                PendingLemma::ReadOverWriteDiff {
                    store,
                    store_result,
                    select_index,
                } => {
                    // If i ≠ j, then select(store(a, i, v), j) = select(a, j)
                    //
                    // This must fire only when the indices are PROVEN
                    // disequal, not merely "not currently known equal"
                    // (`!self.are_equal(...)`): the latter is also true
                    // while the indices' equality is simply undecided, and
                    // they could still be merged equal later (e.g. via a
                    // Nelson-Oppen arithmetic propagation). Firing on that
                    // weaker condition could force `select(store(a,i,v),j)
                    // = select(a,j)` for indices that turn out equal,
                    // where the correct value is actually `v` (the
                    // read-over-write-SAME case) -- a soundness bug, not
                    // just an incompleteness one.
                    if self.is_proven_disequal(store.index, select_index) {
                        // Find the select we need to equate
                        for (select_node, select) in &self.selects {
                            if self.find(select.array) == self.find(store_result)
                                && self.find(select.index) == self.find(select_index)
                            {
                                // Find select(a, j) where a is the base array
                                for (other_select_node, other_select) in &self.selects {
                                    if self.find(other_select.array) == self.find(store.array)
                                        && self.find(other_select.index) == self.find(select_index)
                                        && !self.are_equal(*select_node, *other_select_node)
                                    {
                                        pending_merges.push((*select_node, *other_select_node));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Apply all pending merges
        for (a, b) in pending_merges {
            self.merge(a, b, TermId::new(0))?;
        }

        if let Some(conflict) = self.current_conflict.take() {
            return Ok(TheoryResult::Unsat(conflict));
        }

        if !propagations.is_empty() {
            return Ok(TheoryResult::Propagate(propagations));
        }

        Ok(TheoryResult::Sat)
    }

    /// Check for conflicts
    pub fn check_conflicts(&self) -> Option<Vec<TermId>> {
        for &(lhs, rhs, reason) in &self.diseqs {
            if self.find(lhs) == self.find(rhs) {
                // Include the full merge chain that makes `lhs`/`rhs`
                // equal, not just the disequality's own reason (see
                // `merge`/`assert_diseq`'s doc comments for why a partial
                // reason set is an unsound, over-strong conflict clause).
                let mut conflict = self.explain_equal(lhs, rhs);
                conflict.push(reason);
                return Some(conflict);
            }
        }
        None
    }

    /// Get all select operations with their array, index, and result nodes.
    /// Returns (result_term, array_term, index_term) for each select.
    pub fn get_select_operations(&self) -> Vec<(TermId, TermId, TermId)> {
        let mut result = Vec::new();
        for (sel_node, sel_op) in &self.selects {
            let sel_term = self.node_to_term.get(*sel_node as usize).and_then(|t| *t);
            let arr_term = self
                .node_to_term
                .get(sel_op.array as usize)
                .and_then(|t| *t);
            let idx_term = self
                .node_to_term
                .get(sel_op.index as usize)
                .and_then(|t| *t);
            if let (Some(s), Some(a), Some(i)) = (sel_term, arr_term, idx_term) {
                result.push((s, a, i));
            }
        }
        result
    }

    /// Get all store operations with their array, index, value, and result nodes.
    /// Returns (result_term, array_term, index_term, value_term) for each store.
    pub fn get_store_operations(&self) -> Vec<(TermId, TermId, TermId, TermId)> {
        let mut result = Vec::new();
        for (store_node, store_op) in &self.stores {
            let store_term = self.node_to_term.get(*store_node as usize).and_then(|t| *t);
            let arr_term = self
                .node_to_term
                .get(store_op.array as usize)
                .and_then(|t| *t);
            let idx_term = self
                .node_to_term
                .get(store_op.index as usize)
                .and_then(|t| *t);
            let val_term = self
                .node_to_term
                .get(store_op.value as usize)
                .and_then(|t| *t);
            if let (Some(s), Some(a), Some(i), Some(v)) = (store_term, arr_term, idx_term, val_term)
            {
                result.push((s, a, i, v));
            }
        }
        result
    }

    /// Get all interned terms (node -> term mapping).
    /// Useful for model construction to identify which terms belong to the array theory.
    pub fn get_interned_terms(&self) -> Vec<TermId> {
        self.term_to_node.keys().copied().collect()
    }

    /// Check if two nodes are in the same equivalence class by their term IDs.
    pub fn are_terms_equal(&self, a: TermId, b: TermId) -> bool {
        match (self.term_to_node.get(&a), self.term_to_node.get(&b)) {
            (Some(&na), Some(&nb)) => self.find(na) == self.find(nb),
            _ => false,
        }
    }
}

impl Theory for ArraySolver {
    fn id(&self) -> TheoryId {
        TheoryId::Arrays
    }

    fn name(&self) -> &str {
        "Arrays"
    }

    fn can_handle(&self, _term: TermId) -> bool {
        // Array theory handles select and store operations
        true
    }

    fn assert_true(&mut self, term: TermId) -> Result<TheoryResult> {
        // Assuming term is an equality, intern and merge
        let _ = self.intern(term);
        Ok(TheoryResult::Sat)
    }

    fn assert_false(&mut self, term: TermId) -> Result<TheoryResult> {
        // Assuming term is an equality, assert disequality
        let node = self.intern(term);
        self.assert_diseq(node, node, term);
        Ok(TheoryResult::Sat)
    }

    fn check(&mut self) -> Result<TheoryResult> {
        #[cfg(feature = "profiling")]
        let _timer = ScopedTimer::new(ProfilingCategory::ArrayExtensionality);
        // Process any pending lemmas first
        let lemma_result = self.process_lemmas()?;
        if !matches!(lemma_result, TheoryResult::Sat) {
            return Ok(lemma_result);
        }

        // Check for conflicts
        if let Some(conflict) = self.check_conflicts() {
            return Ok(TheoryResult::Unsat(conflict));
        }

        Ok(TheoryResult::Sat)
    }

    fn push(&mut self) {
        self.context_stack.push(ContextState {
            num_nodes: self.next_node as usize,
            num_selects: self.selects.len(),
            num_stores: self.stores.len(),
            num_diseqs: self.diseqs.len(),
            num_pending_lemmas: self.pending_lemmas.len(),
            num_trail: self.trail.len(),
            num_merge_log: self.merge_log.len(),
        });
    }

    fn pop(&mut self) {
        if let Some(state) = self.context_stack.pop() {
            // Restore nodes
            self.next_node = state.num_nodes as u32;
            self.node_to_term.truncate(state.num_nodes);
            self.arrays.truncate(state.num_nodes);
            self.parent.truncate(state.num_nodes);

            // Undo union-find operations via trail
            while self.trail.len() > state.num_trail {
                if let Some((node, old_parent)) = self.trail.pop() {
                    self.parent[node as usize] = old_parent;
                }
            }

            // Remove terms added after push
            self.term_to_node
                .retain(|_, &mut v| (v as usize) < state.num_nodes);

            // Restore constraints
            self.selects.truncate(state.num_selects);
            self.stores.truncate(state.num_stores);
            self.diseqs.truncate(state.num_diseqs);
            self.pending_lemmas.truncate(state.num_pending_lemmas);
            self.merge_log.truncate(state.num_merge_log);

            // Clear conflict
            self.current_conflict = None;
        }
    }

    fn reset(&mut self) {
        self.next_node = 0;
        self.term_to_node.clear();
        self.node_to_term.clear();
        self.arrays.clear();
        self.selects.clear();
        self.stores.clear();
        self.parent.clear();
        self.trail.clear();
        self.diseqs.clear();
        self.pending_lemmas.clear();
        self.context_stack.clear();
        self.current_conflict = None;
        self.shared_equalities.clear();
    }

    fn get_model(&self) -> Vec<(TermId, TermId)> {
        // Build a model from the array solver's union-find state.
        // For each interned term, find its equivalence class representative
        // and map it to the representative's term. This captures:
        //   - select(store(a, i, v), i) = v  (read-over-write same)
        //   - select(store(a, i, v), j) = select(a, j) when i != j
        //   - Explicitly merged terms via equality assertions
        //
        // Group terms by their equivalence class root and map each to the
        // representative term of that class (the first term found with a
        // TermId at that root).

        // First, find the representative term for each equivalence class root
        let mut root_to_repr: FxHashMap<u32, TermId> = FxHashMap::default();
        for (&term, &node) in &self.term_to_node {
            let root = self.find(node);
            root_to_repr.entry(root).or_insert(term);
        }

        // Now map each term to its class representative
        let mut assignments = Vec::new();
        for (&term, &node) in &self.term_to_node {
            let root = self.find(node);
            if let Some(&repr_term) = root_to_repr.get(&root) {
                assignments.push((term, repr_term));
            }
        }

        // Additionally, for each select operation that has a known value
        // (its result is in the same equivalence class as some value node),
        // include the select result -> value mapping.
        for (sel_node, sel_op) in &self.selects {
            let sel_root = self.find(*sel_node);
            // Check if this select's result is equivalent to a store's value
            for (store_result, store) in &self.stores {
                if self.find(sel_op.array) == self.find(*store_result)
                    && self.find(sel_op.index) == self.find(store.index)
                {
                    // select(store(a, i, v), i) = v
                    let val_root = self.find(store.value);
                    if sel_root == val_root
                        && let (Some(Some(sel_term)), Some(Some(val_term))) = (
                            self.node_to_term.get(*sel_node as usize),
                            self.node_to_term.get(store.value as usize),
                        )
                        && !assignments.iter().any(|(t, _)| *t == *sel_term)
                    {
                        assignments.push((*sel_term, *val_term));
                    }
                }
            }
        }

        assignments
    }
}

impl TheoryCombination for ArraySolver {
    fn notify_equality(&mut self, eq: EqualityNotification) -> bool {
        // Check if either term has been interned in the array solver
        let lhs_node = self.term_to_node.get(&eq.lhs).copied();
        let rhs_node = self.term_to_node.get(&eq.rhs).copied();

        match (lhs_node, rhs_node) {
            (Some(lhs), Some(rhs)) => {
                // Both terms are in the array solver -- merge their equivalence classes
                let reason = eq.reason.unwrap_or(eq.lhs);
                if self.merge(lhs, rhs, reason).is_err() {
                    return false;
                }

                // Check if the merge caused a conflict with existing disequalities
                if self.current_conflict.is_some() {
                    return false;
                }

                // When indices become equal, propagate read-over-write consequences:
                // If i = j and we have select(a, i) and select(a, j), then
                // select(a, i) = select(a, j).
                self.propagate_index_equalities(lhs, rhs);

                true
            }
            (Some(_), None) | (None, Some(_)) => {
                // One term is in the array solver, the other is foreign.
                // Accept the notification -- it might become relevant later.
                true
            }
            (None, None) => {
                // Neither term is relevant to the array theory
                false
            }
        }
    }

    fn get_shared_equalities(&self) -> Vec<EqualityNotification> {
        self.shared_equalities.clone()
    }

    fn is_relevant(&self, term: TermId) -> bool {
        self.term_to_node.contains_key(&term)
    }
}

impl ArraySolver {
    /// When two index nodes become equal, check if there are select operations
    /// on the same array with those indices and propagate equalities.
    ///
    /// This implements the key array axiom for Nelson-Oppen:
    /// If i = j then select(a, i) = select(a, j).
    fn propagate_index_equalities(&mut self, node_a: u32, node_b: u32) {
        // Collect select operations to compare (to avoid borrow conflicts)
        let selects_snapshot: Vec<(u32, SelectOp)> = self.selects.clone();
        let n = selects_snapshot.len();

        self.shared_equalities.clear();

        for i in 0..n {
            let (sel_node_i, ref sel_i) = selects_snapshot[i];
            for (sel_node_j, sel_j) in &selects_snapshot[(i + 1)..] {
                let sel_node_j = *sel_node_j;

                // Check if both selects are on the same array (same equivalence class)
                if self.find(sel_i.array) != self.find(sel_j.array) {
                    continue;
                }

                // Check if the indices are now in the same equivalence class
                let idx_i_root = self.find(sel_i.index);
                let idx_j_root = self.find(sel_j.index);

                if idx_i_root == idx_j_root {
                    // The indices are equal, so the select results must be equal
                    let sel_i_root = self.find(sel_node_i);
                    let sel_j_root = self.find(sel_node_j);

                    if sel_i_root != sel_j_root {
                        // Derive select(a, i) = select(a, j) and share it
                        if let (Some(Some(term_i)), Some(Some(term_j))) = (
                            self.node_to_term.get(sel_node_i as usize),
                            self.node_to_term.get(sel_node_j as usize),
                        ) {
                            self.shared_equalities.push(EqualityNotification {
                                lhs: *term_i,
                                rhs: *term_j,
                                reason: None,
                            });
                        }
                    }
                }
            }
        }

        // Also check store axioms: when i = j and we have store(a, i, v),
        // then select(store(a, i, v), j) = v.
        let merged_root_a = self.find(node_a);
        let merged_root_b = self.find(node_b);
        let stores_snapshot: Vec<(u32, StoreOp)> = self.stores.clone();

        for (store_result, store) in &stores_snapshot {
            let store_idx_root = self.find(store.index);

            // Check if the store's index became equal to either merged node
            if store_idx_root == merged_root_a || store_idx_root == merged_root_b {
                // Find selects on the store result with the same index
                for (sel_node, sel) in &selects_snapshot {
                    if self.find(sel.array) == self.find(*store_result)
                        && self.find(sel.index) == store_idx_root
                    {
                        let val_root = self.find(store.value);
                        let sel_root = self.find(*sel_node);

                        if val_root != sel_root
                            && let (Some(Some(val_term)), Some(Some(sel_term))) = (
                                self.node_to_term.get(store.value as usize),
                                self.node_to_term.get(*sel_node as usize),
                            )
                        {
                            self.shared_equalities.push(EqualityNotification {
                                lhs: *val_term,
                                rhs: *sel_term,
                                reason: None,
                            });
                        }
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_array_basic() {
        let mut solver = ArraySolver::new();

        // Create an array and some indices
        let a = solver.intern_array(TermId::new(1));
        let i = solver.intern(TermId::new(2));
        let v = solver.intern(TermId::new(3));

        // store(a, i, v)
        let a_store = solver.intern_store(TermId::new(10), a, i, v);

        // select(store(a, i, v), i) should equal v
        let select = solver.intern_select(TermId::new(11), a_store, i);

        let result = solver.check().expect("test operation should succeed");
        // Result may be Sat or Propagate (propagating the equality)
        assert!(!matches!(result, TheoryResult::Unsat(_)));

        // After processing lemmas, select should be equal to v
        assert!(solver.are_equal(select, v));
    }

    #[test]
    fn test_array_read_different_index() {
        let mut solver = ArraySolver::new();

        // Create an array and indices
        let a = solver.intern_array(TermId::new(1));
        let i = solver.intern(TermId::new(2));
        let j = solver.intern(TermId::new(3));
        let v = solver.intern(TermId::new(4));

        // Assert i != j
        solver.assert_diseq(i, j, TermId::new(100));

        // store(a, i, v)
        let a_store = solver.intern_store(TermId::new(10), a, i, v);

        // select(a, j) - original array at j
        let select_a_j = solver.intern_select(TermId::new(11), a, j);

        // select(store(a, i, v), j) - should equal select(a, j)
        let select_store_j = solver.intern_select(TermId::new(12), a_store, j);

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Sat));

        // After read-over-write-diff lemma, selects should be equal
        assert!(solver.are_equal(select_a_j, select_store_j));
    }

    #[test]
    fn test_array_conflict() {
        let mut solver = ArraySolver::new();

        let a = solver.intern(TermId::new(1));
        let b = solver.intern(TermId::new(2));

        // Assert a != b
        solver.assert_diseq(a, b, TermId::new(100));

        // Then merge a = b
        solver
            .merge(a, b, TermId::new(101))
            .expect("test operation should succeed");

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Unsat(_)));
    }

    #[test]
    fn test_array_push_pop() {
        let mut solver = ArraySolver::new();

        let a = solver.intern_array(TermId::new(1));
        let i = solver.intern(TermId::new(2));
        let v = solver.intern(TermId::new(3));

        solver.push();

        let _a_store = solver.intern_store(TermId::new(10), a, i, v);
        assert_eq!(solver.stores.len(), 1);

        solver.pop();

        assert_eq!(solver.stores.len(), 0);
    }

    #[test]
    fn test_incremental_merge_undo() {
        let mut solver = ArraySolver::new();

        let a = solver.intern(TermId::new(1));
        let b = solver.intern(TermId::new(2));
        let c = solver.intern(TermId::new(3));

        // Before merge, a and b are different
        assert!(!solver.are_equal(a, b));

        solver.push();

        // Merge a and b
        solver
            .merge(a, b, TermId::new(100))
            .expect("test operation should succeed");
        assert!(solver.are_equal(a, b));

        solver.push();

        // Merge b and c
        solver
            .merge(b, c, TermId::new(101))
            .expect("test operation should succeed");
        assert!(solver.are_equal(a, c));

        // Pop should undo b=c but keep a=b
        solver.pop();
        assert!(solver.are_equal(a, b));
        assert!(!solver.are_equal(a, c));

        // Pop should undo a=b
        solver.pop();
        assert!(!solver.are_equal(a, b));
    }

    #[test]
    fn test_incremental_with_pending_lemmas() {
        let mut solver = ArraySolver::new();

        let a = solver.intern_array(TermId::new(1));
        let i = solver.intern(TermId::new(2));
        let v = solver.intern(TermId::new(3));

        solver.push();

        // Create store which adds a pending lemma
        let _a_store = solver.intern_store(TermId::new(10), a, i, v);
        let initial_lemmas = solver.pending_lemmas.len();
        assert!(initial_lemmas > 0);

        solver.push();

        // Add another store
        let j = solver.intern(TermId::new(4));
        let w = solver.intern(TermId::new(5));
        let _a_store2 = solver.intern_store(TermId::new(11), a, j, w);
        assert!(solver.pending_lemmas.len() > initial_lemmas);

        // Pop should restore lemmas count
        solver.pop();
        assert_eq!(solver.pending_lemmas.len(), initial_lemmas);

        solver.pop();
        assert_eq!(solver.pending_lemmas.len(), 0);
    }

    // Audit regression (theories-array): the read-over-write-DIFFERENT
    // axiom (`select(store(a,i,v),j) = select(a,j)` when `i != j`) used to
    // fire whenever the indices were merely "not currently known equal"
    // (`!self.are_equal(...)`), rather than PROVEN disequal. Indices with
    // no asserted relationship at all must NOT trigger this axiom, since
    // they could still become equal later.
    #[test]
    fn audit_read_over_write_diff_requires_proven_disequal() {
        let mut solver = ArraySolver::new();

        let a = solver.intern_array(TermId::new(1));
        let i = solver.intern(TermId::new(2));
        let j = solver.intern(TermId::new(3));
        let v = solver.intern(TermId::new(4));

        // No relationship asserted between `i` and `j` at all.
        let a_store = solver.intern_store(TermId::new(10), a, i, v);
        let select_a_j = solver.intern_select(TermId::new(11), a, j);
        let select_store_j = solver.intern_select(TermId::new(12), a_store, j);

        let result = solver.check().expect("check should succeed");
        assert!(matches!(result, TheoryResult::Sat));

        // Must NOT have been merged: `i` and `j` are not proven disequal,
        // so asserting `select(store(a,i,v),j) = select(a,j)` would be
        // unsound if `i` and `j` later turn out equal (where the correct
        // value is `v`, not `select(a,j)`).
        assert!(
            !solver.are_equal(select_a_j, select_store_j),
            "read-over-write-diff must not fire without a proven disequality"
        );

        // Once `i != j` is actually proven, the axiom (queued eagerly at
        // `intern_select` time) must fire on the next `check()`.
        solver.assert_diseq(i, j, TermId::new(100));
        // Re-trigger axiom discovery: a fresh select forces
        // `check_read_over_write` to re-scan with the new disequality
        // in place (the original selects were queued before the
        // disequality existed).
        let _ = solver.intern_select(TermId::new(13), a_store, j);
        let result2 = solver.check().expect("check should succeed");
        assert!(matches!(result2, TheoryResult::Sat));
        assert!(
            solver.are_equal(select_a_j, select_store_j),
            "read-over-write-diff must fire once the indices are proven disequal"
        );
    }

    // Audit regression (theories-array): conflict explanations only cited
    // the single merge reason that happened to trigger the check plus the
    // disequality's own reason, omitting every OTHER merge in the chain
    // that actually makes the two sides equal -- an over-strong (unsound)
    // learned clause. The full chain must now be included.
    #[test]
    fn audit_conflict_includes_full_equality_chain() {
        let mut solver = ArraySolver::new();

        let a = solver.intern(TermId::new(1));
        let b = solver.intern(TermId::new(2));
        let c = solver.intern(TermId::new(3));
        let d = solver.intern(TermId::new(4));

        let r_ab = TermId::new(101);
        let r_bc = TermId::new(102);
        let r_cd = TermId::new(103);
        let r_diseq = TermId::new(200);

        // a != d
        solver.assert_diseq(a, d, r_diseq);

        // Chain: a = b = c = d (each an independent merge with its own
        // reason), which transitively forces a = d, contradicting a != d.
        solver.merge(a, b, r_ab).expect("merge should succeed");
        solver.merge(b, c, r_bc).expect("merge should succeed");
        solver.merge(c, d, r_cd).expect("merge should succeed");

        let result = solver.check().expect("check should succeed");
        match result {
            TheoryResult::Unsat(conflict) => {
                for r in [r_ab, r_bc, r_cd, r_diseq] {
                    assert!(
                        conflict.contains(&r),
                        "conflict {conflict:?} must include every reason in the \
                         equality chain plus the disequality, missing {r:?}"
                    );
                }
            }
            other => panic!("expected Unsat, got {other:?}"),
        }
    }
}
