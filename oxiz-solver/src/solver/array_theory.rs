//! Incremental array-theory state — Stage 5 of `docs/ARRAY_THEORY_PLAN.md`.
//!
//! Indexed bookkeeping for the CDCL(T) array theory, mirroring Z3's
//! `theory_array_full::var_data_full`: for each array term it records the
//! `store`s that write it and the `select`s that read it.  Populated as
//! `select`/`store` terms are encoded and retracted on user `pop`, so the
//! later event-driven stages (`merge_eh` congruence, `relevant_eh`
//! read-over-write, incremental lemma addition) can react to reads/writes by
//! O(1) lookup instead of rescanning the whole formula each lazy-refinement
//! round.
//!
//! Scope handling.  Entries are added at encode (assert) time, i.e. at the
//! user context level, so they are undone by a user `pop` through journals
//! snapshot in `ContextState` (see `Solver::push` / `Solver::pop`).  A HashMap
//! cannot be truncated, so every insertion is appended to a journal and `pop`
//! replays the journal in reverse, popping the matching Vec tail and dropping
//! the key when its Vec becomes empty.  `reset` clears everything.

#![allow(missing_docs)]

use crate::prelude::*;
use oxiz_core::ast::TermId;

/// Incremental array-theory index: `base array -> store terms` and
/// `array -> select terms`.
#[derive(Default, Debug)]
pub(crate) struct ArrayTheory {
    /// `base -> store terms` writing it (`store(base, idx, val)`).
    maps: FxHashMap<TermId, Vec<TermId>>,
    /// `array -> select terms` reading it (`select(array, idx)`).
    parents: FxHashMap<TermId, Vec<TermId>>,
    /// Read-over-write targets for selects that read a store directly:
    /// `select_term -> (store_idx, read_idx, store_val, select(base,
    /// read_idx))`, where the fourth element is **pre-created at encode time**
    /// (the theory holds `&TermManager`, so it cannot `mk_select` mid-search).
    /// Lets the RoW propagation fire both the SAME case (`i = j ⇒ select = v`)
    /// and the DIFFERENT case (`i ≠ j ⇒ select = select(base, j)`) without
    /// term creation during search.
    row_targets: FxHashMap<TermId, (TermId, TermId, TermId, TermId)>,
    /// Extensionality witnesses pre-created at encode time, one per array
    /// equality atom `(= a b)`: `(a, b, k, select(a, k), select(b, k))`.
    /// `final_check` checks each for the extensionality conflict `a ≠ b`
    /// (proven disequal) while `select(a, k) = select(b, k)` (proven equal via
    /// read-over-write / congruence) — which forces `a = b`, a contradiction.
    ext_witnesses: Vec<(TermId, TermId, TermId, TermId, TermId)>,
    /// `ext_witnesses` length snapshot for LIFO undo on `pop`.
    ext_witnesses_journal_len_snapshots: Vec<usize>,
    /// One `base` per `maps` insertion, in insertion order, for LIFO undo.
    maps_journal: Vec<TermId>,
    /// One `array` per `parents` insertion, in insertion order, for LIFO undo.
    parents_journal: Vec<TermId>,
    /// One `select_term` per `row_targets` insertion, for LIFO undo.
    row_targets_journal: Vec<TermId>,
}

impl ArrayTheory {
    /// Create an empty index.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Record that `store_term = store(base, _, _)` writes `base`.
    pub(crate) fn add_store(&mut self, base: TermId, store_term: TermId) {
        self.maps.entry(base).or_default().push(store_term);
        self.maps_journal.push(base);
    }

    /// Record that `select_term = select(array, _)` reads `array`.
    pub(crate) fn add_select(&mut self, array: TermId, select_term: TermId) {
        self.parents.entry(array).or_default().push(select_term);
        self.parents_journal.push(array);
    }

    /// Record a read-over-write target for `select_term = select(store(base,
    /// i, v), j)`: the propagation can then fire SAME (`i = j ⇒ select = v`)
    /// or DIFFERENT (`i ≠ j ⇒ select = select(base, j)`) using `base_read`
    /// (= the pre-created `select(base, j)`), with no term creation during
    /// search.
    pub(crate) fn add_row_target(
        &mut self,
        select_term: TermId,
        store_idx: TermId,
        read_idx: TermId,
        store_val: TermId,
        base_read: TermId,
    ) {
        self.row_targets
            .insert(select_term, (store_idx, read_idx, store_val, base_read));
        self.row_targets_journal.push(select_term);
    }

    /// The read-over-write target for `select_term`, if it reads a store:
    /// `(store_idx, read_idx, store_val, select(base, read_idx))`.
    pub(crate) fn row_target(
        &self,
        select_term: TermId,
    ) -> Option<(TermId, TermId, TermId, TermId)> {
        self.row_targets.get(&select_term).copied()
    }

    /// Record an extensionality witness for the array equality atom `(= a b)`:
    /// `k` is a fresh index variable; `sa = select(a, k)`, `sb = select(b, k)`.
    /// Pre-created at encode time (the theory holds `&TermManager`).
    pub(crate) fn add_ext_witness(
        &mut self,
        a: TermId,
        b: TermId,
        k: TermId,
        sa: TermId,
        sb: TermId,
    ) {
        self.ext_witnesses.push((a, b, k, sa, sb));
    }

    /// Iterate the extensionality witnesses `(a, b, k, select(a,k),
    /// select(b,k))`.
    pub(crate) fn ext_witnesses(&self) -> &[(TermId, TermId, TermId, TermId, TermId)] {
        &self.ext_witnesses
    }

    /// The `store` terms writing `array` (`store(array, _, _)`).
    #[allow(dead_code)] // consumed by Stage 5 steps 3–6 (merge_eh / relevant_eh)
    pub(crate) fn stores_of(&self, array: TermId) -> &[TermId] {
        self.maps.get(&array).map(Vec::as_slice).unwrap_or(&[])
    }

    /// The `select` terms reading `array` (`select(array, _)`).
    #[allow(dead_code)] // consumed by Stage 5 steps 3–6
    pub(crate) fn selects_of(&self, array: TermId) -> &[TermId] {
        self.parents
            .get(&array)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// Iterator over every `(array, select_term)` pair in the index.
    pub(crate) fn select_entries(&self) -> impl Iterator<Item = (TermId, TermId)> + '_ {
        self.parents
            .iter()
            .flat_map(|(&array, sels)| sels.iter().map(move |&s| (array, s)))
    }

    /// Snapshot of the journal lengths, for [`Self::pop].
    pub(crate) fn snapshot(&self) -> ArrayTheoryScope {
        ArrayTheoryScope {
            maps_journal_len: self.maps_journal.len(),
            parents_journal_len: self.parents_journal.len(),
            row_targets_journal_len: self.row_targets_journal.len(),
            ext_witnesses_len: self.ext_witnesses.len(),
        }
    }

    /// Undo every insertion made since the matching [`Self::snapshot] / `push`.
    pub(crate) fn pop(&mut self, scope: ArrayTheoryScope) {
        while self.parents_journal.len() > scope.parents_journal_len {
            if let Some(array) = self.parents_journal.pop()
                && let Some(v) = self.parents.get_mut(&array)
            {
                v.pop();
                if v.is_empty() {
                    self.parents.remove(&array);
                }
            }
        }
        while self.row_targets_journal.len() > scope.row_targets_journal_len {
            if let Some(sel) = self.row_targets_journal.pop() {
                self.row_targets.remove(&sel);
            }
        }
        self.ext_witnesses.truncate(scope.ext_witnesses_len);
        while self.maps_journal.len() > scope.maps_journal_len {
            if let Some(base) = self.maps_journal.pop()
                && let Some(v) = self.maps.get_mut(&base)
            {
                v.pop();
                if v.is_empty() {
                    self.maps.remove(&base);
                }
            }
        }
    }

    /// Drop all bookkeeping (called by `Solver::reset`).
    pub(crate) fn reset(&mut self) {
        self.maps.clear();
        self.parents.clear();
        self.row_targets.clear();
        self.ext_witnesses.clear();
        self.maps_journal.clear();
        self.parents_journal.clear();
        self.row_targets_journal.clear();
    }

    /// Number of indexed `store` entries (debug / statistics).
    #[allow(dead_code)]
    pub(crate) fn num_stores(&self) -> usize {
        self.maps.values().map(Vec::len).sum()
    }

    /// Number of indexed `select` entries (debug / statistics).
    #[allow(dead_code)]
    pub(crate) fn num_selects(&self) -> usize {
        self.parents.values().map(Vec::len).sum()
    }
}

/// Journal-length snapshot used to undo a scope's insertions on `pop`.
#[derive(Clone, Copy, Default, Debug)]
pub(crate) struct ArrayTheoryScope {
    maps_journal_len: usize,
    parents_journal_len: usize,
    row_targets_journal_len: usize,
    ext_witnesses_len: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_lookup_and_pop() {
        let mut t = ArrayTheory::new();
        let (a, b) = (TermId::new(1), TermId::new(2));
        let (s1, s2) = (TermId::new(10), TermId::new(11));
        let (r1, r2) = (TermId::new(20), TermId::new(21));

        let snap = t.snapshot();
        t.add_store(a, s1);
        t.add_store(a, s2);
        t.add_store(b, s1);
        t.add_select(a, r1);
        assert_eq!(t.stores_of(a), &[s1, s2]);
        assert_eq!(t.stores_of(b), &[s1]);
        assert_eq!(t.selects_of(a), &[r1]);
        assert!(t.selects_of(b).is_empty());

        // Pop undoes everything back to the snapshot, including dropping keys
        // whose Vec became empty.
        t.pop(snap);
        assert!(t.stores_of(a).is_empty());
        assert!(t.stores_of(b).is_empty());
        assert!(t.selects_of(a).is_empty());
        assert_eq!(t.num_stores(), 0);
        assert_eq!(t.num_selects(), 0);
    }

    #[test]
    fn nested_scopes_pop_lifo() {
        let mut t = ArrayTheory::new();
        let a = TermId::new(1);
        let outer = t.snapshot();
        t.add_store(a, TermId::new(10));
        let inner = t.snapshot();
        t.add_store(a, TermId::new(11));
        assert_eq!(t.num_stores(), 2);
        t.pop(inner);
        assert_eq!(t.stores_of(a), &[TermId::new(10)]);
        t.pop(outer);
        assert!(t.stores_of(a).is_empty());
    }
}
