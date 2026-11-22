//! Term Manager - Arena allocation for terms

use super::term::{Term, TermId, TermKind};
use super::traversal::get_children;
use crate::interner::{Rodeo, Spur};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::sort::{SortId, SortKind, SortManager};
use hashbrown::HashTable;
use portable_atomic::{AtomicU32, Ordering};
use smallvec::SmallVec;

/// A subtree's Boolean-atom set (see
/// [`crate::ast::manager::query::simplify`]'s `subtree_bool_atoms`):
/// sorted ascending by `TermId.0`.  Membership is a binary search and
/// unions are two-pointer merges — no hashing anywhere in the
/// construction.  Shared through `Arc` in the manager-level
/// `subtree_atom_cache` (cross-assertion reuse; see its field doc).
pub(crate) type AtomSet = SmallVec<[TermId; 4]>;

mod builder;
mod dt_eq;
mod dt_fold;
mod dt_ite_lift;
mod import;
pub use dt_ite_lift::MAX_ITE_LIFT_NODES;
pub mod bv_fold;
pub mod ff_fold;
mod query;
use query::substitute::SubstMemo;
mod rounding_mode;
pub mod str_fold;

/// Hash of an interning key, i.e. of the pair `(kind, sort)`.
///
/// This is deliberately the *same* value the previous
/// `FxHashMap<(TermKind, SortId), TermId>` computed for the same pair:
/// `Hash for (A, B)` is defined as `a.hash(state)` followed by
/// `b.hash(state)`, so hashing the two components in that order into a
/// default-seeded [`rustc_hash::FxHasher`] reproduces the old key hash bit for
/// bit. Storing ids instead of owned keys was meant to move memory and nothing
/// else, so the hash distribution -- and with it every bucket-occupancy and
/// probe-length property the intern table had before -- is held fixed.
/// (Ported from upstream v0.3.3.)
fn hash_term_key(kind: &TermKind, sort: SortId) -> u64 {
    use core::hash::{Hash, Hasher};

    let mut hasher = rustc_hash::FxHasher::default();
    kind.hash(&mut hasher);
    sort.hash(&mut hasher);
    hasher.finish()
}

/// Statistics for garbage collection
#[derive(Debug, Clone, Default)]
pub struct GCStatistics {
    /// Number of GC runs
    pub gc_count: usize,
    /// Total terms collected across all GC runs
    pub total_collected: usize,
    /// Total cache entries removed across all GC runs
    pub total_cache_removed: usize,
    /// Last GC collection count
    pub last_collected: usize,
    /// Last GC cache removal count
    pub last_cache_removed: usize,
}

/// Manager for term allocation and interning
#[derive(Debug)]
pub struct TermManager {
    /// Arena for term storage
    pub(super) terms: Vec<Term>,
    /// Next term ID
    pub(super) next_id: AtomicU32,
    /// String interner for symbols
    pub(super) interner: Rodeo,
    /// Sort manager
    pub sorts: SortManager,
    /// Whether anything has introduced a rounding mode: a mode term, or a
    /// parser-accepted `RoundingMode` declaration (see `rounding_mode.rs`).
    pub(super) rounding_mode_used: bool,
    /// Intern table for structural sharing: hashes of `(kind, sort)` to the
    /// `TermId` of the one term carrying that pair.
    ///
    /// A term's identity is the pair `(kind, sort)`, not the kind alone: two
    /// structurally identical kinds at different sorts -- most notably `Var`
    /// with the same name -- must intern to distinct terms, or same-named
    /// variables of different sorts alias and silently type-confuse (wrong
    /// terms, wrong models).
    ///
    /// Rather than own a *second* copy of each `TermKind` as a map key, this
    /// stores only the id and resolves both lookups and collisions against
    /// `terms[id]`, so each kind is retained exactly once -- in the `terms`
    /// vector, which is where `get()` reads it from anyway. That is why this
    /// is a [`HashTable`] and not a `HashMap`: a `HashMap` has no way to
    /// express "the key lives somewhere else". (Ported from upstream v0.3.3.)
    pub(super) table: HashTable<TermId>,
    /// Hash fast-reject side array, parallel to `terms`: `hashes[i]` is the
    /// `hash_term_key` value of term `i`'s `(kind, sort)`.  Append-only and
    /// written exactly once per term (next to the single `terms.push`), so it
    /// is consistent by construction.  The hashcons probe compares this 8-byte
    /// entry before loading the full `Term` from the arena — the dominant
    /// per-candidate cost of parsing large inputs (scan #3 item #2b).
    pub(super) hashes: Vec<u64>,
    /// True constant
    pub true_id: TermId,
    /// False constant
    pub false_id: TermId,
    /// GC statistics
    pub(super) gc_stats: GCStatistics,
    /// Memo for [`crate::ast::manager::query::simplify`]'s guard-equality
    /// solve (`eq_ite_rules`): the solved form of an equality PAIR, keyed
    /// by the id-ordered pair.  The solve is a pure function of the two
    /// terms' (immutable) kinds, and term ids are never reused (the
    /// append-only arena; `gc` only prunes the intern table), so entries
    /// are valid for the manager's whole lifetime.  Without it, the ctx
    /// walk re-solves the same `(ite, value)` pair under every split
    /// path and the bottom-up/ctx pair re-solves each other's output —
    /// the interning flood that hung the large nec-smt members' walks.
    pub(super) eq_solve_cache: FxHashMap<(TermId, TermId), Option<TermId>>,
    /// Memo for [`crate::ast::manager::builder`]'s `bvmul` AC
    /// canonicalization: the canonical chain id of a (canonical-pair
    /// ordered) input pair.  A pure function of immutable terms (valid
    /// for the manager's lifetime, ids never reused), so shared meganode
    /// chains pay the flatten+sort+fold once — the substitution fixpoints
    /// rebuild the same chains millions of times.
    pub(super) ac_mul_cache: std::cell::RefCell<FxHashMap<(TermId, TermId), TermId>>,
    /// Memo for [`crate::tactic::quantifier::predicates::contains_quantifier`]:
    /// the ids of terms *proven* quantifier-free by a completed traversal.
    /// Term content is immutable and ids are never reused (append-only
    /// arena; `gc` only prunes the intern table), so an entry is valid for
    /// the manager's whole lifetime. Only negative results are memoized
    /// (a found quantifier aborts the walk early, so the visited prefix
    /// is not all quantifier-free); every *sub*term of a quantifier-free
    /// root is quantifier-free, so one walk populates the whole DAG. The
    /// pipeline asks this per assertion at several stages — without the
    /// memo each call re-walks the assertion DAG with a fresh visited set.
    /// `RefCell` because the queries arrive through `&TermManager` (the
    /// manager is not `Sync` — its interner is single-threaded — so plain
    /// interior mutability is sound here).
    pub(super) quantifier_free_cache: std::cell::RefCell<FxHashSet<TermId>>,
    /// Same shape as `quantifier_free_cache`, for set/bag-sortedness (see
    /// `contains_set_or_bag_sort`): per-assert feature-detection walks on
    /// shared meganode prefixes were re-walking the whole prefix per
    /// assertion.
    pub(super) setbag_free_cache: std::cell::RefCell<FxHashSet<TermId>>,
    /// Same shape, for `Ite` nodes (see `contains_ite`).
    pub(super) ite_free_cache: std::cell::RefCell<FxHashSet<TermId>>,
    /// Same shape, for array-sorted subterms (see `contains_array_sort`).
    pub(super) array_free_cache: std::cell::RefCell<FxHashSet<TermId>>,
    /// Same shape, for nonlinear arith products (see
    /// `contains_nonlinear_mul`).
    pub(super) nonlinear_free_cache: std::cell::RefCell<FxHashSet<TermId>>,
    /// Cross-assertion memo for [`crate::ast::manager::query::simplify`]'s
    /// `subtree_bool_atoms`: each term's Boolean-atom set (sorted dense
    /// ids; `None` = oversized, see `MAX_MEMO_ATOM_SET`).  A set is a pure
    /// function of the term's (immutable) node and children, and ids are
    /// never reused (append-only arena; `gc` only prunes the intern
    /// table), so an entry is valid for the manager's whole lifetime.
    /// `Arc`-shared because a solve's assertions overlap heavily on
    /// meganode prefixes: without the memo every assertion rebuilt the
    /// shared prefixes' sets from scratch (the hdp class spent 35 % of a
    /// run in exactly that, pre-sorting-landing).  `RefCell` as above.
    pub(super) subtree_atom_cache:
        std::cell::RefCell<FxHashMap<TermId, Option<std::sync::Arc<AtomSet>>>>,
    /// Epoch-stamped visited marks shared by every DAG walker that asks
    /// for one ([`TermManager::fresh_visit_epoch`]): one `Vec<u32>`
    /// indexed by the dense term id, a fresh epoch per walk.  This
    /// replaces the per-call `FxHashSet` allocation + hashing of every
    /// hot walker with one array probe (the minigzip-class profile had
    /// ~30 % of the run in visited-set insert/rehash churn across ~8
    /// distinct per-assert walkers).  Interior mutability as above (the
    /// manager is single-threaded by construction).
    visit_epoch: std::cell::Cell<u32>,
    visit_marks: std::cell::RefCell<Vec<u32>>,
}

impl Default for TermManager {
    fn default() -> Self {
        Self::new()
    }
}

impl TermManager {
    /// A fresh visited-epoch for a DAG walk (see the `visit_marks` field
    /// doc).  Epochs are unique per call; the `u32` counter wrapping
    /// clears the array (a walk that outlives 2³² calls re-marks).
    #[must_use]
    pub fn fresh_visit_epoch(&self) -> u32 {
        let next = self.visit_epoch.get().wrapping_add(1);
        if next == 0 {
            // Wrapped: every mark in the array belongs to some old epoch,
            // so clear them all and restart at 1.
            self.visit_marks.borrow_mut().fill(0);
            self.visit_epoch.set(1);
            1
        } else {
            self.visit_epoch.set(next);
            next
        }
    }

    /// Mark `t` with `epoch` and report whether it was *unmarked* (the
    /// check-and-set every walker's dedup reduces to; one borrow, one
    /// array probe, no hashing).
    pub fn visit_try_mark(&self, epoch: u32, t: TermId) -> bool {
        let idx = t.0 as usize;
        let mut marks = self.visit_marks.borrow_mut();
        if idx >= marks.len() {
            marks.resize(idx + 1, 0);
        }
        if marks[idx] == epoch {
            false
        } else {
            marks[idx] = epoch;
            true
        }
    }

    /// Create a new term manager
    #[must_use]
    pub fn new() -> Self {
        Self::with_capacity(1024)
    }

    /// Create a new term manager presized for `expected_terms` interned
    /// terms. Purely an allocation hint: the tables grow identically from
    /// any starting capacity, so answers and TermIds are the same as from
    /// [`TermManager::new`] — but goals that will intern tens of thousands
    /// of terms (the graph and CP drivers) avoid the intermediate
    /// table-growth copies, which profiled as a quarter of a pure-Boolean
    /// goal's assertion pipeline.
    ///
    /// The symbol interner is presized to the same estimate: named
    /// variables typically dominate an API-driven goal's term population.
    #[must_use]
    pub fn with_capacity(expected_terms: usize) -> Self {
        let sorts = SortManager::new();
        let bool_sort = sorts.bool_sort;

        let mut manager = Self {
            terms: Vec::with_capacity(expected_terms.max(1024)),
            next_id: AtomicU32::new(0),
            interner: Rodeo::with_capacity_and_hasher(
                lasso::Capacity::for_strings(expected_terms.max(1024)),
                crate::interner::FxBuildHasherDbg::default(),
            ),
            sorts,
            rounding_mode_used: false,
            table: HashTable::with_capacity(expected_terms.max(1024)),
            hashes: Vec::with_capacity(expected_terms.max(1024)),
            true_id: TermId(0),
            false_id: TermId(1),
            gc_stats: GCStatistics::default(),
            quantifier_free_cache: std::cell::RefCell::new(FxHashSet::default()),
            setbag_free_cache: std::cell::RefCell::new(FxHashSet::default()),
            ite_free_cache: std::cell::RefCell::new(FxHashSet::default()),
            array_free_cache: std::cell::RefCell::new(FxHashSet::default()),
            nonlinear_free_cache: std::cell::RefCell::new(FxHashSet::default()),
            subtree_atom_cache: std::cell::RefCell::new(FxHashMap::default()),
            visit_epoch: std::cell::Cell::new(0),
            visit_marks: std::cell::RefCell::new(Vec::new()),
            eq_solve_cache: FxHashMap::default(),
            ac_mul_cache: std::cell::RefCell::new(FxHashMap::default()),
        };

        // Pre-allocate true and false
        manager.true_id = manager.intern(TermKind::True, bool_sort);
        manager.false_id = manager.intern(TermKind::False, bool_sort);

        manager
    }

    /// Intern a term kind with an explicit sort, returning its unique ID.
    ///
    /// This is the public-facing version of the internal `intern` method,
    /// intended for use by crates that need to construct term kinds directly
    /// (e.g. when rebuilding quantifiers with substituted bodies).
    pub fn intern_term(&mut self, mut kind: TermKind, sort: SortId) -> TermId {
        // Raw construction must preserve the numeral invariant that mk_bitvec
        // establishes. Otherwise equality can fold two spellings of the same
        // residue to false before any theory or model checker sees them.
        if let TermKind::BitVecConst { value, width } = &mut kind
            && (value.sign() == num_bigint::Sign::Minus || value.bits() > u64::from(*width))
        {
            *value = bv_fold::bv_wrap_unsigned(value, *width);
        }
        self.intern(kind, sort)
    }

    /// Does `term`'s DAG contain any quantifier? Memoized: terms whose
    /// completed traversal found none are recorded (with every visited
    /// subterm) in the `quantifier_free_cache` field, so repeated queries —
    /// and sibling assertions sharing subterms — become set lookups.
    /// Exact by construction: term content is immutable, ids are never
    /// reused, and only full negative traversals populate the cache.
    #[must_use]
    pub fn contains_quantifier(&self, term: TermId) -> bool {
        if self.quantifier_free_cache.borrow().contains(&term) {
            return false;
        }
        // Iterative DAG walk (no native recursion over user terms).  A
        // popped node already in the cache is proven free — its whole
        // subtree is skipped, so sibling assertions sharing a meganode
        // prefix stop re-walking it.
        let cache_now = self.quantifier_free_cache.borrow();
        let mut visited = FxHashSet::default();
        let mut stack = vec![term];
        while let Some(id) = stack.pop() {
            if cache_now.contains(&id) {
                continue;
            }
            if !visited.insert(id) {
                continue;
            }
            let Some(data) = self.get(id) else {
                continue;
            };
            if matches!(data.kind, TermKind::Forall { .. } | TermKind::Exists { .. }) {
                // Partial traversal: the visited prefix may still contain
                // quantifiers above this one elsewhere; memoize nothing.
                return true;
            }
            for child in get_children(&data.kind).iter().rev() {
                stack.push(*child);
            }
        }
        // Completed without finding: every visited subterm is quantifier-
        // free (a quantifier anywhere reachable would have aborted).
        drop(cache_now);
        self.quantifier_free_cache
            .borrow_mut()
            .extend(visited.iter().copied());
        false
    }

    /// Does `term`'s DAG contain a set- or bag-sorted subterm?  Same
    /// memoization shape as [`Self::contains_quantifier`]: completed
    /// negative traversals populate `setbag_free_cache` (per-node subtree
    /// skips included), turning the per-assertion set/bag survey gate
    /// into a lookup after the first assertion over a shared prefix.
    #[must_use]
    pub fn contains_set_or_bag_sort(&self, term: TermId) -> bool {
        if self.setbag_free_cache.borrow().contains(&term) {
            return false;
        }
        let cache_now = self.setbag_free_cache.borrow();
        let mut visited = FxHashSet::default();
        let mut stack = vec![term];
        while let Some(id) = stack.pop() {
            if cache_now.contains(&id) {
                continue;
            }
            if !visited.insert(id) {
                continue;
            }
            let Some(data) = self.get(id) else {
                continue;
            };
            if self
                .sorts
                .get(data.sort)
                .is_some_and(|s| matches!(s.kind, SortKind::Set(_) | SortKind::Bag(_)))
            {
                return true;
            }
            for child in get_children(&data.kind) {
                stack.push(child);
            }
        }
        drop(cache_now);
        self.setbag_free_cache
            .borrow_mut()
            .extend(visited.iter().copied());
        false
    }

    /// Does `term`'s DAG contain an `Ite` node?  Memoized like
    /// [`Self::contains_quantifier`] (see `ite_free_cache`).
    #[must_use]
    pub fn contains_ite(&self, term: TermId) -> bool {
        if self.ite_free_cache.borrow().contains(&term) {
            return false;
        }
        let cache_now = self.ite_free_cache.borrow();
        let mut visited = FxHashSet::default();
        let mut stack = vec![term];
        while let Some(id) = stack.pop() {
            if cache_now.contains(&id) {
                continue;
            }
            if !visited.insert(id) {
                continue;
            }
            let Some(data) = self.get(id) else {
                continue;
            };
            if matches!(data.kind, TermKind::Ite(..)) {
                return true;
            }
            for child in get_children(&data.kind) {
                stack.push(child);
            }
        }
        drop(cache_now);
        self.ite_free_cache
            .borrow_mut()
            .extend(visited.iter().copied());
        false
    }

    /// Does `term`'s DAG contain an array-sorted subterm?  Memoized like
    /// [`Self::contains_quantifier`] (see `array_free_cache`); turns the
    /// per-assert ground-instance registration's array scan into a lookup
    /// on shared meganode prefixes.
    #[must_use]
    pub fn contains_array_sort(&self, term: TermId) -> bool {
        if self.array_free_cache.borrow().contains(&term) {
            return false;
        }
        let cache_now = self.array_free_cache.borrow();
        let mut visited = FxHashSet::default();
        let mut stack = vec![term];
        while let Some(id) = stack.pop() {
            if cache_now.contains(&id) {
                continue;
            }
            if !visited.insert(id) {
                continue;
            }
            let Some(data) = self.get(id) else {
                continue;
            };
            if self
                .sorts
                .get(data.sort)
                .is_some_and(|s| matches!(s.kind, SortKind::Array { .. }))
            {
                return true;
            }
            for child in get_children(&data.kind) {
                stack.push(child);
            }
        }
        drop(cache_now);
        self.array_free_cache
            .borrow_mut()
            .extend(visited.iter().copied());
        false
    }

    /// Does `term`'s DAG contain a nonlinear arith product — a `Mul`
    /// with at least two non-constant operands?  Memoized like
    /// [`Self::contains_quantifier`] (see `nonlinear_free_cache`).  The
    /// check-side NIA detection rescans every assertion otherwise.
    #[must_use]
    pub fn contains_nonlinear_mul(&self, term: TermId) -> bool {
        if self.nonlinear_free_cache.borrow().contains(&term) {
            return false;
        }
        let cache_now = self.nonlinear_free_cache.borrow();
        let mut visited = FxHashSet::default();
        let mut stack = vec![term];
        while let Some(id) = stack.pop() {
            if cache_now.contains(&id) {
                continue;
            }
            if !visited.insert(id) {
                continue;
            }
            let Some(data) = self.get(id) else {
                continue;
            };
            if let TermKind::Mul(args) = &data.kind {
                let nonconst = args
                    .iter()
                    .filter(|a| {
                        !matches!(
                            self.get(**a).map(|d| &d.kind),
                            Some(TermKind::IntConst(_)) | Some(TermKind::RealConst(_))
                        )
                    })
                    .count();
                if nonconst >= 2 {
                    return true;
                }
            }
            for child in get_children(&data.kind) {
                stack.push(child);
            }
        }
        drop(cache_now);
        self.nonlinear_free_cache
            .borrow_mut()
            .extend(visited.iter().copied());
        false
    }

    /// Intern a term, returning its unique ID
    pub(crate) fn intern(&mut self, kind: TermKind, sort: SortId) -> TermId {
        // Identity is the pair (kind, sort): identical kinds at distinct sorts
        // must not alias (see the `table` field documentation).
        let hash = hash_term_key(&kind, sort);

        {
            let Self {
                terms,
                table,
                hashes,
                ..
            } = self;
            if let Some(&id) = table.find(hash, |&id| {
                // Hash fast-reject before the Term load: the 8-byte side
                // array (see `hashes`) screens out foreign-bucket candidates
                // at ~12x the density of the Term arena, so a candidate Term
                // is loaded only on a hash match (exact compare still
                // follows — a hash match alone never proves identity).
                hashes.get(id.0 as usize).is_some_and(|h| *h == hash)
                    && terms
                        .get(id.0 as usize)
                        .is_some_and(|t| t.sort == sort && t.kind == kind)
            }) {
                return id;
            }
        }

        // Miss: allocate the id, then push the term *before* recording it, so
        // that the id the table stores is already resolvable through `terms`.
        let id = TermId(self.next_id.fetch_add(1, Ordering::Relaxed));
        self.terms.push(Term { id, kind, sort });
        self.hashes.push(hash);

        let Self { table, hashes, .. } = self;
        table.insert_unique(hash, id, |&id| {
            hashes.get(id.0 as usize).copied().unwrap_or(0)
        });
        id
    }

    /// Get a term by its ID
    #[must_use]
    pub fn get(&self, id: TermId) -> Option<&Term> {
        self.terms.get(id.0 as usize)
    }

    /// Lookup the interned id of `(kind, sort)` WITHOUT interning: `None`
    /// when no such term exists.  The read-only half of the interning
    /// write path (`Self::intern`, private)
    /// for callers that must not mint terms (e.g. probing whether an
    /// equality atom between two terms already exists — creating it would
    /// be exactly the quadratic blowup the probe exists to avoid).
    #[must_use]
    pub fn find_interned(&self, kind: &TermKind, sort: SortId) -> Option<TermId> {
        let hash = hash_term_key(kind, sort);
        let Self {
            terms,
            table,
            hashes,
            ..
        } = self;
        table
            .find(hash, |&id| {
                hashes.get(id.0 as usize).is_some_and(|h| *h == hash)
                    && terms
                        .get(id.0 as usize)
                        .is_some_and(|t| t.sort == sort && &t.kind == kind)
            })
            .copied()
    }

    /// Intern a string, returning its key
    pub fn intern_str(&mut self, s: &str) -> Spur {
        self.interner.get_or_intern(s)
    }

    /// Declare a datatype whose constructor/selector keys belong to this term
    /// manager. Declaration names are normalized into the sort manager's
    /// interner; term nodes continue to use this manager's interner.
    pub fn declare_datatype(
        &mut self,
        name: &str,
        mut constructors: Vec<crate::sort::DataTypeConstructor>,
    ) {
        for constructor in &mut constructors {
            let name = self.resolve_str(constructor.name).to_string();
            constructor.name = self.sorts.intern_str(&name);
            for (selector, _) in &mut constructor.selectors {
                let name = self.resolve_str(*selector).to_string();
                *selector = self.sorts.intern_str(&name);
            }
        }
        self.sorts.declare_datatype(name, constructors);
    }

    /// Resolve an interned string
    #[must_use]
    pub fn resolve_str(&self, key: Spur) -> &str {
        self.interner.resolve(&key)
    }

    /// Get the number of terms allocated
    #[must_use]
    pub fn len(&self) -> usize {
        self.terms.len()
    }

    /// Check if the manager is empty (only contains true/false)
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.terms.len() <= 2
    }

    // ======== Garbage Collection ========

    /// Perform garbage collection on unreachable terms
    ///
    /// This method performs a mark-and-sweep garbage collection:
    /// 1. Marks all terms reachable from the given root set
    /// 2. Removes unmarked entries from the cache
    ///
    /// Note: This doesn't actually free memory from the arena (terms vector),
    /// but it does clean up the cache to prevent unbounded growth.
    ///
    /// # Arguments
    /// * `roots` - Set of root term IDs to keep (and their descendants)
    ///
    /// # Returns
    /// Number of cache entries removed
    pub fn gc(&mut self, roots: &FxHashSet<TermId>) -> usize {
        // Mark phase: find all reachable terms
        let mut reachable = FxHashSet::default();
        let mut worklist: Vec<TermId> = roots.iter().copied().collect();

        // Always keep true and false
        worklist.push(self.true_id);
        worklist.push(self.false_id);

        while let Some(id) = worklist.pop() {
            if !reachable.insert(id) {
                continue; // Already visited
            }

            // Mark children as reachable
            if let Some(term) = self.get(id) {
                for child in get_children(&term.kind) {
                    if !reachable.contains(&child) {
                        worklist.push(child);
                    }
                }
            }
        }

        // Sweep phase: remove unreachable entries from the intern table.
        // A swept term stays readable through `get`, and interning its kind
        // again allocates a *fresh* id rather than returning the old one.
        let original_cache_size = self.table.len();
        self.table.retain(|id| reachable.contains(id));
        let removed = original_cache_size - self.table.len();

        // Update statistics
        self.gc_stats.gc_count += 1;
        self.gc_stats.total_cache_removed += removed;
        self.gc_stats.last_cache_removed = removed;
        self.gc_stats.last_collected = removed;
        self.gc_stats.total_collected += removed;

        removed
    }

    /// Perform aggressive garbage collection
    ///
    /// Similar to `gc()` but more thorough. It also shrinks the cache capacity
    /// to fit the retained entries, potentially freeing more memory.
    ///
    /// # Arguments
    /// * `roots` - Set of root term IDs to keep (and their descendants)
    ///
    /// # Returns
    /// Number of cache entries removed
    pub fn gc_aggressive(&mut self, roots: &FxHashSet<TermId>) -> usize {
        let removed = self.gc(roots);
        // Reallocating the table rehashes every retained id, so this needs the
        // same `terms`-resolving hasher that `intern` inserts with.
        let Self { terms, table, .. } = self;
        table.shrink_to_fit(|&id| {
            terms
                .get(id.0 as usize)
                .map_or(0, |t| hash_term_key(&t.kind, t.sort))
        });
        removed
    }

    /// Get garbage collection statistics
    #[must_use]
    pub fn gc_statistics(&self) -> &GCStatistics {
        &self.gc_stats
    }

    /// Get the current cache size (number of hash-consed terms)
    #[must_use]
    pub fn cache_size(&self) -> usize {
        self.table.len()
    }

    /// Get the total number of terms allocated
    #[must_use]
    pub fn term_count(&self) -> usize {
        self.terms.len()
    }

    /// Clear all GC statistics
    pub fn reset_gc_stats(&mut self) {
        self.gc_stats = GCStatistics::default();
    }
}

/// A reusable substitution session for MANY terms under ONE fixed mapping
/// (round-fixpoint loops like the eliminator's reconstruct pass): the
/// mapping is cloned once, the memo and the domain prefilter are built
/// once, and every term substitutes through [`TermManager::
/// substitute_session`] sharing them.  The per-call `substitute` form
/// re-clones the mapping and allocates a fresh memo per term — on loops
/// over definitions sharing meganode prefixes that re-walked every
/// shared prefix per definition (the bzip2recover class spent a third
/// of its run there).  Cache sharing across one mapping is the
/// documented-blessed pattern (`substitute_cached`'s doc); the session
/// boundary is exactly "the mapping does not change".
#[derive(Debug, Clone, Default)]
pub struct SubstSession {
    subst: FxHashMap<TermId, TermId>,
    cache: SubstMemo,
    domain: Option<std::rc::Rc<[u64]>>,
}

impl SubstSession {
    /// A session for `mapping`; the domain bitmap builds lazily on first
    /// use (empty mappings never build one).
    #[must_use]
    pub fn new(mapping: &FxHashMap<TermId, TermId>) -> Self {
        Self {
            subst: mapping.clone(),
            cache: SubstMemo::default(),
            domain: None,
        }
    }
}

impl TermManager {
    /// Substitute `id` under the session's fixed mapping, sharing the
    /// session's memo across every call (see [`SubstSession`]).
    pub fn substitute_session(&mut self, id: TermId, session: &mut SubstSession) -> TermId {
        if session.domain.is_none() {
            let max_id = session
                .subst
                .keys()
                .map(|k| k.0 as usize)
                .max()
                .unwrap_or(0);
            let mut bits = vec![0u64; max_id / 64 + 1];
            for &k in session.subst.keys() {
                bits[k.0 as usize / 64] |= 1u64 << (k.0 % 64);
            }
            session.domain = Some(bits.into());
        }
        let keep = FxHashSet::default();
        let domain = session.domain.clone().unwrap_or_default();
        self.substitute_cached_keep_domain::<SubstMemo>(
            id,
            &session.subst,
            &keep,
            &mut session.cache,
            Some(&domain),
        )
    }
}

/// Builder for constructing substitutions incrementally with optimizations
///
/// This provides better performance than repeatedly calling substitute when
/// building up complex substitutions, especially when:
/// - Composing multiple substitutions
/// - Applying the same substitution to many terms
/// - Building substitutions incrementally
#[derive(Debug, Clone)]
pub struct SubstitutionBuilder {
    /// The substitution mapping
    mapping: FxHashMap<TermId, TermId>,
    /// Shared cache for substitution results — the DENSE-SLAB form
    /// ([`SubstMemo`]): this cache lives for a whole elimination campaign
    /// whose walks cover a large fraction of the manager's term-id space,
    /// so per-node probes are array reads instead of hashes (the
    /// `term_to_bv` dense-slab precedent; the hashed form's probes were
    /// 14 % of the bzip2recover-class run after the bv-wrap landing).
    cache: SubstMemo,
    /// Over-approximating membership bitmap of `mapping`'s DOMAIN (one bit
    /// per term id; set = "may be substituted here"): consulted before the
    /// per-node hash probe in the substitution walk, so the overwhelmingly
    /// common not-in-domain node skips hashing entirely.  Built lazily on
    /// the first [`Self::apply`] after any mapping mutation (every mutator
    /// clears it alongside the cache); an `Rc` so the walk's contexts share
    /// one copy.  Sound as a prefilter because every per-scope map is a
    /// SUBSET of `mapping` (keep-filtering and binder shadowing only
    /// remove entries): a set bit falls through to the exact probe, a
    /// clear bit provably misses.
    domain_bits: Option<std::rc::Rc<[u64]>>,
}

impl SubstitutionBuilder {
    /// Create a new empty substitution builder
    #[must_use]
    pub fn new() -> Self {
        Self {
            mapping: FxHashMap::default(),
            cache: SubstMemo::default(),
            domain_bits: None,
        }
    }

    /// Create a builder with initial capacity
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            mapping: FxHashMap::with_capacity_and_hasher(capacity, Default::default()),
            cache: SubstMemo::default(),
            domain_bits: None,
        }
    }

    /// Add a substitution mapping
    pub fn add(&mut self, from: TermId, to: TermId) -> &mut Self {
        // Invalidate cache when adding new mapping
        self.cache.clear();
        self.domain_bits = None;
        self.mapping.insert(from, to);
        self
    }

    /// Add multiple substitution mappings
    pub fn add_many(&mut self, mappings: impl IntoIterator<Item = (TermId, TermId)>) -> &mut Self {
        self.cache.clear();
        self.domain_bits = None;
        self.mapping.extend(mappings);
        self
    }

    /// Compose this substitution with another
    ///
    /// The resulting substitution applies `other` first, then `self`.
    /// This is optimized to share structure where possible.
    pub fn compose(&mut self, other: &SubstitutionBuilder, manager: &mut TermManager) -> &mut Self {
        // For each mapping in self, substitute using other
        let mut new_mapping = FxHashMap::default();
        let mut temp_cache = SubstMemo::default();

        for (&from, &to) in &self.mapping {
            let new_to = if other.mapping.contains_key(&to) {
                manager.substitute_cached(to, &other.mapping, &mut temp_cache)
            } else {
                to
            };
            new_mapping.insert(from, new_to);
        }

        // Add mappings from other that aren't in self
        for (&from, &to) in &other.mapping {
            new_mapping.entry(from).or_insert(to);
        }

        self.mapping = new_mapping;
        self.cache.clear();
        self.domain_bits = None;
        self
    }

    /// Apply the substitution to a term
    ///
    /// This uses a persistent cache across multiple applications,
    /// making it more efficient when substituting many terms.
    pub fn apply(&mut self, id: TermId, manager: &mut TermManager) -> TermId {
        if self.domain_bits.is_none() {
            self.domain_bits = Some(Self::build_domain_bits(&self.mapping));
        }
        let bits = self.domain_bits.clone().unwrap_or_default();
        manager.substitute_cached_domain(id, &self.mapping, &mut self.cache, &bits)
    }

    /// One bit per term id up to the mapping's highest domain id; set for
    /// ids present in the mapping's domain.
    fn build_domain_bits(mapping: &FxHashMap<TermId, TermId>) -> std::rc::Rc<[u64]> {
        let max_id = mapping.keys().map(|k| k.0 as usize).max().unwrap_or(0);
        let mut bits = vec![0u64; max_id / 64 + 1];
        for &k in mapping.keys() {
            bits[k.0 as usize / 64] |= 1u64 << (k.0 % 64);
        }
        bits.into()
    }

    /// Apply the substitution to multiple terms efficiently
    ///
    /// Uses the shared cache to avoid redundant work.
    pub fn apply_many(&mut self, ids: &[TermId], manager: &mut TermManager) -> Vec<TermId> {
        ids.iter().map(|&id| self.apply(id, manager)).collect()
    }

    /// Get the underlying mapping
    #[must_use]
    pub fn mapping(&self) -> &FxHashMap<TermId, TermId> {
        &self.mapping
    }

    /// Check if the substitution is empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.mapping.is_empty()
    }

    /// Get the number of mappings
    #[must_use]
    pub fn len(&self) -> usize {
        self.mapping.len()
    }

    /// Clear the substitution
    pub fn clear(&mut self) {
        self.mapping.clear();
        self.cache.clear();
        self.domain_bits = None;
    }

    /// Reset the cache (useful for freeing memory)
    pub fn reset_cache(&mut self) {
        self.cache.clear();
        self.domain_bits = None;
    }

    /// Get cache statistics (for debugging/optimization)
    #[must_use]
    pub fn cache_stats(&self) -> (usize, usize) {
        (self.cache.len(), self.cache.capacity())
    }
}

impl Default for SubstitutionBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn raw_bv_numerals_share_the_builders_canonical_residue() {
        use crate::ast::{TermKind, TermManager};
        use num_bigint::BigInt;
        for width in [1, 8, 64, 129] {
            let mut manager = TermManager::new();
            let sort = manager.sorts.bitvec(width);
            let modulus = BigInt::from(1) << width as usize;
            for value in [BigInt::from(-1), &modulus + 3u32, -(&modulus + 3u32)] {
                let raw = manager.intern_term(
                    TermKind::BitVecConst {
                        value: value.clone(),
                        width,
                    },
                    sort,
                );
                let built = manager.mk_bitvec(value, width);
                assert_eq!(raw, built);
                assert_eq!(manager.mk_eq(raw, built), manager.true_id);
            }
        }
    }

    use super::*;

    #[test]
    fn test_constants() {
        let manager = TermManager::new();
        assert_ne!(manager.mk_true(), manager.mk_false());
        assert_eq!(manager.mk_bool(true), manager.mk_true());
        assert_eq!(manager.mk_bool(false), manager.mk_false());
    }

    #[test]
    fn test_not_simplification() {
        let mut manager = TermManager::new();
        let t = manager.mk_true();
        let f = manager.mk_false();

        assert_eq!(manager.mk_not(t), f);
        assert_eq!(manager.mk_not(f), t);

        let x = manager.mk_var("x", manager.sorts.bool_sort);
        let not_x = manager.mk_not(x);
        let not_not_x = manager.mk_not(not_x);
        assert_eq!(not_not_x, x);
    }

    #[test]
    fn test_and_simplification() {
        let mut manager = TermManager::new();
        let t = manager.mk_true();
        let f = manager.mk_false();
        let x = manager.mk_var("x", manager.sorts.bool_sort);

        assert_eq!(manager.mk_and([t, x]), x);
        assert_eq!(manager.mk_and([f, x]), f);
        assert_eq!(manager.mk_and([t, t]), t);
        assert_eq!(manager.mk_and(core::iter::empty()), t);
    }

    #[test]
    fn test_or_simplification() {
        let mut manager = TermManager::new();
        let t = manager.mk_true();
        let f = manager.mk_false();
        let x = manager.mk_var("x", manager.sorts.bool_sort);

        assert_eq!(manager.mk_or([f, x]), x);
        assert_eq!(manager.mk_or([t, x]), t);
        assert_eq!(manager.mk_or([f, f]), f);
        assert_eq!(manager.mk_or(core::iter::empty()), f);
    }

    #[test]
    fn test_eq_canonicalization() {
        let mut manager = TermManager::new();
        let x = manager.mk_var("x", manager.sorts.int_sort);
        let y = manager.mk_var("y", manager.sorts.int_sort);

        let eq1 = manager.mk_eq(x, y);
        let eq2 = manager.mk_eq(y, x);
        assert_eq!(eq1, eq2);
    }

    #[test]
    fn test_bv_commutative_ops_canonicalize_operand_order() {
        let mut manager = TermManager::new();
        let bv8 = manager.sorts.bitvec(8);
        let x = manager.mk_var("x", bv8);
        let y = manager.mk_var("y", bv8);

        assert_eq!(manager.mk_bv_and(x, y), manager.mk_bv_and(y, x));
        assert_eq!(manager.mk_bv_or(x, y), manager.mk_bv_or(y, x));
        assert_eq!(manager.mk_bv_add(x, y), manager.mk_bv_add(y, x));
        assert_eq!(manager.mk_bv_mul(x, y), manager.mk_bv_mul(y, x));
        assert_eq!(manager.mk_bv_xor(x, y), manager.mk_bv_xor(y, x));
    }

    #[test]
    fn test_bv_commutative_ops_canonicalize_const_var_order() {
        let mut manager = TermManager::new();
        let bv8 = manager.sorts.bitvec(8);
        let x = manager.mk_var("x", bv8);
        let three = manager.mk_bitvec(3i64, 8);

        assert_eq!(manager.mk_bv_mul(three, x), manager.mk_bv_mul(x, three));
        assert_eq!(manager.mk_bv_add(three, x), manager.mk_bv_add(x, three));
    }

    #[test]
    fn test_bv_sub_does_not_canonicalize_operand_order() {
        let mut manager = TermManager::new();
        let bv8 = manager.sorts.bitvec(8);
        let x = manager.mk_var("x", bv8);
        let y = manager.mk_var("y", bv8);

        assert_ne!(manager.mk_bv_sub(x, y), manager.mk_bv_sub(y, x));
    }

    #[test]
    fn test_ite_simplification() {
        let mut manager = TermManager::new();
        let t = manager.mk_true();
        let f = manager.mk_false();
        let x = manager.mk_var("x", manager.sorts.bool_sort);
        let y = manager.mk_var("y", manager.sorts.bool_sort);

        assert_eq!(manager.mk_ite(t, x, y), x);
        assert_eq!(manager.mk_ite(f, x, y), y);
        assert_eq!(manager.mk_ite(x, t, f), x);
    }

    #[test]
    fn test_interning() {
        let mut manager = TermManager::new();
        let x1 = manager.mk_var("x", manager.sorts.int_sort);
        let x2 = manager.mk_var("x", manager.sorts.int_sort);
        assert_eq!(x1, x2);

        let y = manager.mk_var("y", manager.sorts.int_sort);
        assert_ne!(x1, y);
    }

    #[test]
    fn test_term_size() {
        let mut manager = TermManager::new();
        let x = manager.mk_var("x", manager.sorts.int_sort);
        let y = manager.mk_var("y", manager.sorts.int_sort);
        let z = manager.mk_var("z", manager.sorts.int_sort);

        assert_eq!(manager.term_size(x), 1);

        let add_xy = manager.mk_add([x, y]);
        assert_eq!(manager.term_size(add_xy), 3);

        let add_xyz = manager.mk_add([x, y, z]);
        assert_eq!(manager.term_size(add_xyz), 4);

        let nested = manager.mk_add([add_xy, z]);
        // add_xy has size 3, z has size 1, outer add has size 1
        // But x and y appear only once each due to hash-consing
        assert_eq!(manager.term_size(nested), 5);
    }

    #[test]
    fn test_term_depth() {
        let mut manager = TermManager::new();
        let x = manager.mk_var("x", manager.sorts.int_sort);
        let y = manager.mk_var("y", manager.sorts.int_sort);

        assert_eq!(manager.term_depth(x), 0);

        let add_xy = manager.mk_add([x, y]);
        assert_eq!(manager.term_depth(add_xy), 1);

        let nested = manager.mk_add([add_xy, x]);
        assert_eq!(manager.term_depth(nested), 2);
    }

    #[test]
    fn test_substitute() {
        let mut manager = TermManager::new();
        let x = manager.mk_var("x", manager.sorts.int_sort);
        let y = manager.mk_var("y", manager.sorts.int_sort);
        let c = manager.mk_int(42);

        let expr = manager.mk_add([x, y]);

        let mut subst = FxHashMap::default();
        subst.insert(x, c);

        let result = manager.substitute(expr, &subst);

        let expected = manager.mk_add([c, y]);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_free_vars() {
        let mut manager = TermManager::new();
        let x = manager.mk_var("x", manager.sorts.int_sort);
        let y = manager.mk_var("y", manager.sorts.int_sort);
        let c = manager.mk_int(42);

        let expr = manager.mk_add([x, y, c]);
        let vars = manager.free_vars(expr);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&x));
        assert!(vars.contains(&y));

        let const_expr = manager.mk_int(100);
        let vars = manager.free_vars(const_expr);
        assert!(vars.is_empty());
    }

    // ======== Quantifier Pattern Tests ========

    #[test]
    fn test_forall_without_patterns() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let bool_sort = manager.sorts.bool_sort;

        let x = manager.mk_var("x", int_sort);
        let zero = manager.mk_int(0);
        let gt_zero = manager.mk_gt(x, zero);

        let forall = manager.mk_forall([("x", int_sort)], gt_zero);
        let term = manager.get(forall).expect("forall term should exist");

        assert_eq!(term.sort, bool_sort);
        match &term.kind {
            TermKind::Forall {
                vars,
                body,
                patterns,
            } => {
                assert_eq!(vars.len(), 1);
                assert_eq!(*body, gt_zero);
                assert!(patterns.is_empty(), "should have no patterns");
            }
            _ => panic!("expected Forall term"),
        }
    }

    #[test]
    fn test_forall_with_patterns() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let bool_sort = manager.sorts.bool_sort;

        let x = manager.mk_var("x", int_sort);
        let f_x = manager.mk_apply("f", [x], int_sort);
        let zero = manager.mk_int(0);
        let gt_zero = manager.mk_gt(f_x, zero);

        let forall = manager.mk_forall_with_patterns([("x", int_sort)], gt_zero, [[f_x]]);
        let term = manager.get(forall).expect("forall term should exist");

        assert_eq!(term.sort, bool_sort);
        match &term.kind {
            TermKind::Forall {
                vars,
                body,
                patterns,
            } => {
                assert_eq!(vars.len(), 1);
                assert_eq!(*body, gt_zero);
                assert_eq!(patterns.len(), 1, "should have 1 pattern");
                assert_eq!(patterns[0].len(), 1, "pattern should have 1 term");
                assert_eq!(patterns[0][0], f_x, "pattern term should be f(x)");
            }
            _ => panic!("expected Forall term"),
        }
    }

    #[test]
    fn test_forall_with_multiple_patterns() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;

        let x = manager.mk_var("x", int_sort);
        let f_x = manager.mk_apply("f", [x], int_sort);
        let g_x = manager.mk_apply("g", [x], int_sort);
        let zero = manager.mk_int(0);
        let body = manager.mk_gt(f_x, zero);

        // Two patterns: (f x) and (g x)
        let forall = manager.mk_forall_with_patterns([("x", int_sort)], body, [[f_x], [g_x]]);

        match &manager.get(forall).expect("forall term should exist").kind {
            TermKind::Forall { patterns, .. } => {
                assert_eq!(patterns.len(), 2, "should have 2 patterns");
            }
            _ => panic!("expected Forall term"),
        }
    }

    #[test]
    fn test_forall_with_multi_term_pattern() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;

        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        let f_x = manager.mk_apply("f", [x], int_sort);
        let g_y = manager.mk_apply("g", [y], int_sort);
        let body = manager.mk_gt(f_x, g_y);

        // One pattern with two terms: (f x) (g y)
        let forall =
            manager.mk_forall_with_patterns([("x", int_sort), ("y", int_sort)], body, [[f_x, g_y]]);

        match &manager.get(forall).expect("forall term should exist").kind {
            TermKind::Forall { patterns, .. } => {
                assert_eq!(patterns.len(), 1, "should have 1 pattern");
                assert_eq!(patterns[0].len(), 2, "pattern should have 2 terms");
            }
            _ => panic!("expected Forall term"),
        }
    }

    #[test]
    fn test_exists_with_patterns() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;

        let x = manager.mk_var("x", int_sort);
        let f_x = manager.mk_apply("f", [x], int_sort);
        let zero = manager.mk_int(0);
        let body = manager.mk_gt(f_x, zero);

        let exists = manager.mk_exists_with_patterns([("x", int_sort)], body, [[f_x]]);

        match &manager.get(exists).expect("exists term should exist").kind {
            TermKind::Exists { patterns, .. } => {
                assert_eq!(patterns.len(), 1);
            }
            _ => panic!("expected Exists term"),
        }
    }
}
