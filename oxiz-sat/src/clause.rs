//! Clause representation and database

use crate::literal::Lit;
#[allow(unused_imports)]
use crate::memory::{ClauseArena, ClauseRef, ClauseView};

use smallvec::SmallVec;

/// Unique identifier for a clause
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ClauseId(pub u32);

impl ClauseId {
    /// The null clause ID (indicates no clause)
    pub const NULL: Self = Self(u32::MAX);

    /// Create a new clause ID
    #[must_use]
    pub const fn new(id: u32) -> Self {
        Self(id)
    }

    /// Check if this is a null ID
    #[must_use]
    pub const fn is_null(self) -> bool {
        self.0 == u32::MAX
    }

    /// Get the raw index
    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

/// Clause tier for tiered database management
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ClauseTier {
    /// Tier 3: Local clauses (recently learned, deleted aggressively)
    Local = 3,
    /// Tier 2: Mid-tier clauses (useful but not essential, deleted conservatively)
    Mid = 2,
    /// Tier 1: Core/GLUE clauses (very high quality, rarely deleted)
    Core = 1,
}

/// A clause is a disjunction of literals
///
/// Cache-line aligned for better memory performance
#[derive(Debug, Clone)]
#[repr(align(64))]
pub struct Clause {
    /// The literals in this clause – SmallVec placed FIRST for optimal struct
    /// layout: 7 inline lits (28B) + len/cap (16B) = 44B, leaving 20B for
    /// metadata in the same 64-byte cache line. Eliminates heap spills for
    /// 5-7 literal clauses (the previous four-element inline capacity spilled
    /// at 5).
    pub lits: SmallVec<[Lit; 8]>,
    /// LBD (Literal Block Distance) for quality metric
    pub lbd: u32,
    /// Number of times this clause was used in conflict analysis
    pub usage_count: u32,
    /// Activity for clause deletion heuristic
    pub activity: f64,
    /// Whether this is a learned clause
    pub learned: bool,
    /// Whether this clause has been deleted
    pub deleted: bool,
    /// Tier for tiered database management (only used for learned clauses)
    pub tier: ClauseTier,
}

impl Clause {
    /// Create a new clause
    #[must_use]
    pub fn new(lits: impl IntoIterator<Item = Lit>, learned: bool) -> Self {
        Self {
            activity: 0.0,
            learned,
            lbd: 0,
            deleted: false,
            lits: lits.into_iter().collect(),
            tier: ClauseTier::Local, // All learned clauses start in Local tier
            usage_count: 0,
        }
    }

    /// Create an original (non-learned) clause
    #[must_use]
    pub fn original(lits: impl IntoIterator<Item = Lit>) -> Self {
        Self::new(lits, false)
    }

    /// Create a learned clause
    #[must_use]
    pub fn learned(lits: impl IntoIterator<Item = Lit>) -> Self {
        Self::new(lits, true)
    }

    /// Get the number of literals
    #[must_use]
    pub fn len(&self) -> usize {
        self.lits.len()
    }

    /// Check if empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.lits.is_empty()
    }

    /// Check if this is a unit clause
    #[must_use]
    pub fn is_unit(&self) -> bool {
        self.lits.len() == 1
    }

    /// Check if this is a binary clause
    #[must_use]
    pub fn is_binary(&self) -> bool {
        self.lits.len() == 2
    }

    /// Get the first literal (for unit clauses)
    #[must_use]
    pub fn unit_lit(&self) -> Option<Lit> {
        if self.is_unit() {
            Some(self.lits[0])
        } else {
            None
        }
    }

    /// Swap literals at indices i and j
    pub fn swap(&mut self, i: usize, j: usize) {
        self.lits.swap(i, j);
    }

    /// Increment usage count and potentially promote tier
    pub fn record_usage(&mut self) {
        self.usage_count += 1;

        // Promote to Mid tier after 3 uses
        if self.usage_count >= 3 && self.tier == ClauseTier::Local {
            self.tier = ClauseTier::Mid;
        }
        // Promote to Core tier after 10 uses or if LBD ≤ 2
        else if (self.usage_count >= 10 || self.lbd <= 2) && self.tier == ClauseTier::Mid {
            self.tier = ClauseTier::Core;
        }
    }

    /// Promote clause to Core tier (for GLUE clauses)
    pub fn promote_to_core(&mut self) {
        self.tier = ClauseTier::Core;
    }

    /// Eagerly assign a tier from the clause's current LBD.
    ///
    /// Mirrors CaDiCaL: low-glue clauses are protected *immediately* at
    /// learning time rather than waiting for `record_usage` to promote them.
    /// Without this, a freshly-learned glue-2 clause lands in `Local` and is
    /// eligible for the aggressive 75%-per-cycle Local sweep before it ever gets
    /// reused – which is catastrophic on multiplier circuits (e.g. `longmult`),
    /// where the short glue-1/glue-2 clauses *are* the propagating cascade that
    /// collapses the formula. Promotion is one-way upward (never demotes a
    /// clause that `record_usage`/`promote_to_core` already lifted higher).
    pub fn assign_tier_from_lbd(&mut self) {
        let target = if self.lbd <= 2 {
            ClauseTier::Core
        } else if self.lbd <= 6 {
            ClauseTier::Mid
        } else {
            ClauseTier::Local
        };
        if target as u8 <= self.tier as u8 {
            self.tier = target;
        }
    }

    /// Normalize clause: remove duplicates, sort literals, check for tautology
    /// Returns true if clause is a tautology (contains both l and ~l)
    pub fn normalize(&mut self) -> bool {
        if self.lits.is_empty() {
            return false;
        }

        // Sort literals for better cache locality and faster operations
        self.lits.sort_unstable_by_key(|lit| lit.code());

        // Remove duplicates and check for tautology in a single pass
        let mut write_idx = 0;
        let mut prev_lit = self.lits[0];

        for read_idx in 1..self.lits.len() {
            let curr_lit = self.lits[read_idx];

            // Check for tautology (complementary literals)
            if curr_lit == prev_lit.negate() {
                return true;
            }

            // Skip duplicates
            if curr_lit != prev_lit {
                write_idx += 1;
                self.lits[write_idx] = curr_lit;
                prev_lit = curr_lit;
            }
        }

        // Truncate to remove duplicates
        self.lits.truncate(write_idx + 1);
        false
    }

    /// Check if this clause subsumes another clause
    /// A clause C subsumes D if C ⊆ D (all literals of C are in D)
    #[must_use]
    pub fn subsumes(&self, other: &Clause) -> bool {
        if self.lits.len() > other.lits.len() {
            return false;
        }

        // Both clauses should be sorted for efficient checking
        let mut i = 0;
        let mut j = 0;

        while i < self.lits.len() && j < other.lits.len() {
            if self.lits[i] == other.lits[j] {
                i += 1;
                j += 1;
            } else if self.lits[i].code() < other.lits[j].code() {
                // Literal from self not in other
                return false;
            } else {
                j += 1;
            }
        }

        i == self.lits.len()
    }

    /// Check if this clause is a self-subsuming resolvent of another clause
    /// Returns the literal to remove from other if self-subsumption is possible
    #[must_use]
    pub fn self_subsuming_resolvent(&self, other: &Clause) -> Option<Lit> {
        // `>`, not `>=` (ported from upstream v0.3.3): the old `>=` rejected
        // *equal-length* pairs — the single most common shape
        // (`(a∨b∨c)` against `(a∨b∨¬c)` → `(a∨b)`) — so the rule fired on
        // almost nothing, which is also why its zero production callers went
        // unnoticed.  (`subsume_round` implements strengthening independently;
        // this method stays as the Clause-level primitive.)
        if self.lits.len() > other.lits.len() {
            return None;
        }

        let mut diff_lit = None;
        let mut matches = 0;

        for &other_lit in &other.lits {
            if self.lits.contains(&other_lit) {
                matches += 1;
            } else if self.lits.contains(&other_lit.negate()) {
                if diff_lit.is_some() {
                    return None; // More than one difference
                }
                diff_lit = Some(other_lit);
            }
        }

        // Self-subsuming resolution requires exactly one complementary literal
        // and all other literals of self must be in other
        if matches == self.lits.len() - 1 && diff_lit.is_some() {
            diff_lit
        } else {
            None
        }
    }
}

/// Statistics for clause database
#[derive(Debug, Clone, Default)]
pub struct ClauseDatabaseStats {
    /// Number of clauses in each tier
    pub tier_counts: [usize; 3], // [Core, Mid, Local]
    /// Total LBD sum for computing average
    pub total_lbd: u64,
    /// Number of clauses with LBD counted
    pub lbd_count: usize,
    /// Distribution of clause sizes
    pub size_distribution: [usize; 10], // [binary, ternary, 4-lit, ..., 10+]
    /// Number of clause promotions
    pub promotions: usize,
    /// Number of clause demotions
    pub demotions: usize,
}

impl ClauseDatabaseStats {
    /// Get average LBD across all learned clauses
    #[must_use]
    pub fn avg_lbd(&self) -> f64 {
        if self.lbd_count == 0 {
            0.0
        } else {
            self.total_lbd as f64 / self.lbd_count as f64
        }
    }

    /// Display statistics
    pub fn display(&self) {
        println!("Clause Database Statistics:");
        println!("  Tier distribution:");
        println!("    Core:  {}", self.tier_counts[0]);
        println!("    Mid:   {}", self.tier_counts[1]);
        println!("    Local: {}", self.tier_counts[2]);
        println!("  Average LBD: {:.2}", self.avg_lbd());
        println!("  Size distribution:");
        for (i, &count) in self.size_distribution.iter().enumerate() {
            if count > 0 {
                let size = if i < 9 {
                    format!("{}", i + 2)
                } else {
                    "10+".to_string()
                };
                println!("    {} literals: {}", size, count);
            }
        }
        println!(
            "  Promotions: {}, Demotions: {}",
            self.promotions, self.demotions
        );
    }
}

/// Database of clauses backed by the contiguous clause arena (`memory.rs`).
pub struct ClauseDatabase {
    /// Contiguous clause storage (see `memory.rs`): every clause is a
    /// 16-byte header immediately followed by its literals, packed into one
    /// `Vec<u64>`. Slots are append-only: a `ClauseRef` names exactly one
    /// clause forever.
    arena: ClauseArena,
    /// Dense id → arena ref table. `ClauseId::index()` indexes this; ids are
    /// handed out in allocation order and never reused or relocated, so ids
    /// stored in trail reasons, watchers and the LRAT tables stay valid for
    /// the database's lifetime (same guarantee the old `Vec<Clause>` gave).
    refs: Vec<ClauseRef>,
    /// Number of live original clauses.
    num_original: usize,
    /// Number of live learned clauses.
    num_learned: usize,
    /// Statistics.
    stats: ClauseDatabaseStats,
}

impl core::fmt::Debug for ClauseDatabase {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ClauseDatabase")
            .field("live", &self.len())
            .field("slots", &self.refs.len())
            .field("num_original", &self.num_original)
            .field("num_learned", &self.num_learned)
            .finish()
    }
}

impl Default for ClauseDatabase {
    fn default() -> Self {
        Self::new()
    }
}

impl ClauseDatabase {
    /// Create an empty database.
    #[must_use]
    pub fn new() -> Self {
        Self {
            arena: ClauseArena::new(64 * 1024),
            refs: Vec::new(),
            num_original: 0,
            num_learned: 0,
            stats: ClauseDatabaseStats::default(),
        }
    }

    fn view(&self, id: ClauseId) -> Option<ClauseView<'_>> {
        let r = *self.refs.get(id.index())?;
        self.arena.get(r)
    }

    /// Arena slot of a clause id. `None` for out-of-range ids (cannot happen
    /// for an id returned by one of the `add_*` constructors – slots are
    /// append-only and ids are never reused).
    pub(crate) fn ref_of(&self, id: ClauseId) -> Option<ClauseRef> {
        self.refs.get(id.index()).copied()
    }

    /// Mutable literal slice of a live clause addressed **directly** by its
    /// arena slot – the propagation hot path, which already carries the slot
    /// inside its watchers and must not pay the extra `refs[id]` indirection
    /// (a second dependent cache miss per visited watcher) on every visit.
    ///
    /// Validation is identical to [`Self::live_lits_mut`] (slot bounds,
    /// deleted flag); a null/stale ref simply reads as "no clause", exactly
    /// as an invalid id does.
    /// Propagation-scan entry (formerly two variants: the fully
    /// validating `live_lits_by_ref` and the hot elided
    /// `live_lits_by_ref_hot`; the hot variant measured 12–16 % fewer
    /// instructions on identical trajectories, so it is the only one —
    /// region validation lives in `debug_assert!`s, see
    /// [`ClauseArena::live_lits_hot`]'s safety argument).
    #[inline]
    pub(crate) fn live_lits_by_ref(&mut self, r: ClauseRef) -> Option<&mut [Lit]> {
        self.arena.live_lits_hot(r)
    }

    /// Get a read-only view of the clause by ID (deleted clauses are still
    /// returned, flagged – callers filter on `deleted`, exactly as with the
    /// previous `Option<&Clause>`).
    #[must_use]
    pub fn get(&self, id: ClauseId) -> Option<ClauseView<'_>> {
        self.view(id)
    }

    /// Mutable literal slice of a **live** clause (single header
    /// read validates the slot and the deleted flag). This is the
    /// propagation hot path's entry point into the arena.
    pub fn live_lits_mut(&mut self, id: ClauseId) -> Option<&mut [Lit]> {
        self.ref_of(id).and_then(|r| self.arena.live_lits_mut(r))
    }

    /// Rewrite a clause with a (shorter or equal-length) literal array,
    /// in place, keeping its id stable. Returns `false` (clause untouched)
    /// for invalid/deleted ids or growth attempts – an arena slot cannot
    /// grow, and relocating would invalidate ids held by watchers and
    /// reasons. Every in-solver rewrite site only shrinks.
    pub fn shrink(&mut self, id: ClauseId, new_lits: &[Lit]) -> bool {
        self.ref_of(id)
            .is_some_and(|r| self.arena.shrink(r, new_lits))
    }

    /// Swap literals `i` and `j` of the clause (no-op for invalid ids or
    /// out-of-range indices).
    pub fn swap_lits(&mut self, id: ClauseId, i: usize, j: usize) {
        if let Some(r) = self.ref_of(id) {
            self.arena.swap_lits(r, i, j);
        }
    }

    /// Set the LBD of a live clause.
    pub fn set_lbd(&mut self, id: ClauseId, lbd: u32) {
        if let Some(r) = self.ref_of(id) {
            self.arena.set_lbd(r, lbd);
        }
    }

    /// Set the tier of a live clause.
    pub fn set_tier(&mut self, id: ClauseId, tier: ClauseTier) {
        if let Some(r) = self.ref_of(id) {
            self.arena.set_tier(r, tier);
        }
    }

    /// Clear the learned flag, promoting the clause to original (cadical
    /// `subsume_clause`'s promotion rule). Deliberately does not touch the
    /// live-original/learned counters – the pre-arena code flipped
    /// `Clause::learned` raw, and `reduce_clause_database` iterates
    /// `learned_clause_ids`, not the counters.
    pub fn clear_learned(&mut self, id: ClauseId) {
        if let Some(r) = self.ref_of(id) {
            self.arena.clear_learned(r);
        }
    }

    /// Mark deleted **without** any counter/stat updates (the raw
    /// `c.deleted = true` sites; the arena flag is all they changed).
    pub fn mark_deleted_raw(&mut self, id: ClauseId) {
        if let Some(r) = self.ref_of(id) {
            self.arena.delete(r);
        }
    }

    /// Increment the usage counter and apply the tier promotions, exactly as
    /// `Clause::record_usage` did: Local → Mid at 3 uses, Mid → Core at 10
    /// uses or `lbd <= 2`. (The arena's usage byte saturates at 255; both
    /// thresholds are far below, so every decision is identical.)
    pub fn record_usage(&mut self, id: ClauseId) {
        let Some(r) = self.ref_of(id) else { return };
        let usage = self.arena.bump_usage(r);
        let Some(v) = self.arena.get(r) else { return };
        if usage >= 3 && v.tier == ClauseTier::Local {
            self.arena.set_tier(r, ClauseTier::Mid);
        } else if (usage >= 10 || v.lbd <= 2) && v.tier == ClauseTier::Mid {
            self.arena.set_tier(r, ClauseTier::Core);
        }
    }

    /// Current usage counter (0 for unknown/deleted clauses).
    pub fn usage_of(&self, id: ClauseId) -> u32 {
        self.ref_of(id)
            .and_then(|r| self.arena.get(r).map(|v| v.usage_count))
            .unwrap_or(0)
    }

    /// Halve the usage counter (the reduce round's decay under the
    /// used-shield; keeps ordering, reaches 0 in O(log rounds)).
    pub fn decay_usage(&mut self, id: ClauseId) {
        if let Some(r) = self.ref_of(id) {
            let u = self.arena.get(r).map_or(0, |v| v.usage_count);
            self.arena.set_usage(r, u / 2);
        }
    }

    /// Increment the usage counter **without** tier promotion (raw counter
    /// access; `record_usage` is the promoting variant the conflict path
    /// uses).
    pub fn bump_usage(&mut self, id: ClauseId) -> u32 {
        self.ref_of(id).map_or(0, |r| self.arena.bump_usage(r))
    }

    /// Reset the usage counter to zero (tier-change bookkeeping in
    /// `clause_maintenance`; the old `Clause::optimize_tier` zeroed the field
    /// inline).
    pub fn reset_usage(&mut self, id: ClauseId) {
        if let Some(r) = self.ref_of(id) {
            self.arena.reset_usage(r);
        }
    }

    /// Promote to Core tier unconditionally (`Clause::promote_to_core`).
    pub fn promote_to_core(&mut self, id: ClauseId) {
        self.set_tier(id, ClauseTier::Core);
    }

    /// Assign the tier implied by the clause's current LBD, one-way upward
    /// (never demotes a clause that `record_usage`/`promote_to_core` already
    /// lifted higher) – `Clause::assign_tier_from_lbd` verbatim: Core for
    /// LBD ≤ 2, Mid for LBD ≤ 6, else Local.
    pub fn assign_tier_from_lbd(&mut self, id: ClauseId) {
        let Some(v) = self.view(id) else { return };
        let target = if v.lbd <= 2 {
            ClauseTier::Core
        } else if v.lbd <= 6 {
            ClauseTier::Mid
        } else {
            ClauseTier::Local
        };
        if (target as u8) <= (v.tier as u8) {
            self.set_tier(id, target);
        }
    }

    /// Normalize a clause: sort literals by code, drop duplicates, report
    /// tautology. Semantics identical to `Clause::normalize` (same sort key,
    /// same single-pass dedup+tautology). Returns `true` if the clause is a
    /// tautology; the clause is left untouched in that case (callers delete
    /// it).
    pub fn normalize(&mut self, id: ClauseId) -> bool {
        let Some(r) = self.ref_of(id) else {
            return false;
        };
        let Some(v) = self.arena.get(r) else {
            return false;
        };
        let mut lits: SmallVec<[Lit; 8]> = v.lits.iter().copied().collect();
        if lits.is_empty() {
            return false;
        }
        lits.sort_unstable_by_key(|lit| lit.code());
        let mut write_idx = 0;
        let mut prev_lit = lits[0];
        let mut taut = false;
        for read_idx in 1..lits.len() {
            let curr = lits[read_idx];
            if curr == prev_lit.negate() {
                taut = true;
                break;
            }
            if curr != prev_lit {
                write_idx += 1;
                lits[write_idx] = curr;
                prev_lit = curr;
            }
        }
        if taut {
            return true;
        }
        lits.truncate(write_idx + 1);
        self.arena.shrink(r, &lits);
        false
    }

    /// Update statistics for a freshly added clause (computed from the same
    /// facts the old `update_stats_add` read off the `Clause`).
    fn update_stats_add_fields(&mut self, learned: bool, len: usize) {
        if learned {
            // Fresh clauses are always Local tier with lbd 0.
            self.stats.tier_counts[2] += 1;
        }
        if len >= 2 {
            let size_idx = if len >= 12 { 9 } else { len - 2 };
            self.stats.size_distribution[size_idx] += 1;
        }
    }

    /// Update statistics when removing a clause.
    fn update_stats_remove_fields(
        &mut self,
        learned: bool,
        tier: ClauseTier,
        lbd: u32,
        size: usize,
    ) {
        if learned {
            let tier_idx = match tier {
                ClauseTier::Core => 0,
                ClauseTier::Mid => 1,
                ClauseTier::Local => 2,
            };
            if self.stats.tier_counts[tier_idx] > 0 {
                self.stats.tier_counts[tier_idx] -= 1;
            }
            if lbd > 0 && self.stats.lbd_count > 0 {
                self.stats.total_lbd = self.stats.total_lbd.saturating_sub(lbd as u64);
                self.stats.lbd_count -= 1;
            }
        }
        if (2..12).contains(&size) {
            if self.stats.size_distribution[size - 2] > 0 {
                self.stats.size_distribution[size - 2] -= 1;
            }
        } else if size >= 12 && self.stats.size_distribution[9] > 0 {
            self.stats.size_distribution[9] -= 1;
        }
    }

    /// Add a clause from literals.
    ///
    /// # Soundness: ids are never reused
    ///
    /// Slots are append-only in the arena and `refs` only grows, so a
    /// `ClauseId` maps to exactly one clause for its entire lifetime – stale
    /// watch-list entries and trail reasons holding a removed id see the
    /// deleted flag (and are skipped), never an unrelated new clause. This
    /// preserves the no-slot-reuse rule the previous `Vec<Clause>` database
    /// documented.
    fn add_lits(&mut self, lits: impl IntoIterator<Item = Lit>, learned: bool) -> ClauseId {
        let lits: SmallVec<[Lit; 8]> = lits.into_iter().collect();
        self.update_stats_add_fields(learned, lits.len());
        let r = self.arena.alloc(&lits, learned);
        let id = ClauseId::new(self.refs.len() as u32);
        self.refs.push(r);
        if learned {
            self.num_learned += 1;
        } else {
            self.num_original += 1;
        }
        id
    }

    /// Add a clause (kept for API compatibility; preprocessors and tests
    /// construct `Clause`s).
    pub fn add(&mut self, clause: Clause) -> ClauseId {
        self.add_lits(clause.lits.iter().copied(), clause.learned)
    }

    /// Add an original clause.
    pub fn add_original(&mut self, lits: impl IntoIterator<Item = Lit>) -> ClauseId {
        self.add_lits(lits, false)
    }

    /// Add a learned clause.
    pub fn add_learned(&mut self, lits: impl IntoIterator<Item = Lit>) -> ClauseId {
        self.add_lits(lits, true)
    }

    /// Mark a clause as deleted and update the live counters and stats.
    pub fn remove(&mut self, id: ClauseId) {
        let Some(v) = self.view(id).filter(|v| !v.deleted) else {
            return;
        };
        let (learned, tier, lbd, size) = (v.learned, v.tier, v.lbd, v.lits.len());
        if let Some(r) = self.ref_of(id) {
            self.arena.delete(r);
        }
        if learned {
            self.num_learned -= 1;
        } else {
            self.num_original -= 1;
        }
        self.update_stats_remove_fields(learned, tier, lbd, size);
    }

    /// Compaction hook. The arena is append-only by design (see
    /// `memory.rs`): deleted slots are never reclaimed, so this is a no-op
    /// retained for API compatibility. Memory is bounded the same way the
    /// old database's was – a deleted slot costs its 24+ bytes instead of a
    /// full 64-byte `Clause`.
    pub fn compact(&mut self) {}

    /// Get the number of live clauses.
    #[must_use]
    pub fn len(&self) -> usize {
        self.num_original + self.num_learned
    }

    /// Check if empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get the number of live original clauses.
    #[must_use]
    pub fn num_original(&self) -> usize {
        self.num_original
    }

    /// Get the number of live learned clauses.
    #[must_use]
    pub fn num_learned(&self) -> usize {
        self.num_learned
    }

    /// Number of allocated clause slots (dense id upper bound).
    #[must_use]
    pub fn num_slots(&self) -> usize {
        self.refs.len()
    }

    /// Iterate over all non-deleted clause IDs, in id (allocation) order –
    /// the same order the previous `Vec<Clause>` index walked.
    pub fn iter_ids(&self) -> impl Iterator<Item = ClauseId> + '_ {
        (0..self.refs.len())
            .map(|i| ClauseId::new(i as u32))
            .filter(|&id| !self.view(id).is_some_and(|v| v.deleted))
    }

    /// Bump activity of a clause.
    pub fn bump_activity(&mut self, id: ClauseId, increment: f32) {
        if let Some(r) = self.ref_of(id) {
            self.arena.add_activity(r, increment);
        }
    }

    /// Multiply every live clause's activity by `factor` (the decay/rescale
    /// passes; relative order preserved).
    ///
    /// Iterates the **refs table** (the authoritative slot list, exact under
    /// `shrink`) rather than walking arena memory by recomputed strides –
    /// see `ClauseArena::scale_activity` for why walking is unsound.
    pub fn scale_live_activities(&mut self, factor: f32) {
        let refs: Vec<ClauseRef> = self.refs.clone();
        for r in refs {
            self.arena.scale_activity(r, factor);
        }
    }

    /// Alias kept for the existing call site (`Solver::decay_clause_activity`
    /// overflow rescale).
    pub fn rescale_activity(&mut self, factor: f32) {
        self.scale_live_activities(factor);
    }

    /// Get statistics about the clause database.
    #[must_use]
    pub fn stats(&self) -> &ClauseDatabaseStats {
        &self.stats
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Var;

    #[test]
    fn test_clause_database() {
        let mut db = ClauseDatabase::new();

        let c1 = db.add_original([Lit::pos(Var::new(0)), Lit::neg(Var::new(1))]);
        let _c2 = db.add_learned([Lit::pos(Var::new(2))]);

        assert_eq!(db.len(), 2);
        assert_eq!(db.num_original(), 1);
        assert_eq!(db.num_learned(), 1);

        db.remove(c1);
        assert_eq!(db.len(), 1);
        assert_eq!(db.num_original(), 0);
    }

    #[test]
    fn test_clause_normalize() {
        let mut clause = Clause::original([
            Lit::pos(Var::new(2)),
            Lit::pos(Var::new(0)),
            Lit::pos(Var::new(2)), // duplicate
            Lit::pos(Var::new(1)),
        ]);

        let is_tautology = clause.normalize();
        assert!(!is_tautology);
        assert_eq!(clause.len(), 3); // duplicate removed
        // Check sorted order
        assert_eq!(clause.lits[0], Lit::pos(Var::new(0)));
        assert_eq!(clause.lits[1], Lit::pos(Var::new(1)));
        assert_eq!(clause.lits[2], Lit::pos(Var::new(2)));
    }

    #[test]
    fn test_clause_normalize_tautology() {
        let mut clause = Clause::original([
            Lit::pos(Var::new(0)),
            Lit::neg(Var::new(0)), // tautology
            Lit::pos(Var::new(1)),
        ]);

        let is_tautology = clause.normalize();
        assert!(is_tautology);
    }

    #[test]
    fn test_clause_subsumes() {
        let mut c1 = Clause::original([Lit::pos(Var::new(0)), Lit::pos(Var::new(1))]);
        let mut c2 = Clause::original([
            Lit::pos(Var::new(0)),
            Lit::pos(Var::new(1)),
            Lit::pos(Var::new(2)),
        ]);

        c1.normalize();
        c2.normalize();

        assert!(c1.subsumes(&c2)); // c1 ⊆ c2
        assert!(!c2.subsumes(&c1)); // c2 ⊈ c1
    }

    #[test]
    fn test_clause_self_subsuming_resolvent() {
        // C1: (a v b), C2: (~a v b v c)
        // C1 can strengthen C2 to (b v c) by removing ~a
        let mut c1 = Clause::original([Lit::pos(Var::new(0)), Lit::pos(Var::new(1))]);
        let mut c2 = Clause::original([
            Lit::neg(Var::new(0)),
            Lit::pos(Var::new(1)),
            Lit::pos(Var::new(2)),
        ]);

        c1.normalize();
        c2.normalize();

        if let Some(lit_to_remove) = c1.self_subsuming_resolvent(&c2) {
            assert_eq!(lit_to_remove, Lit::neg(Var::new(0)));
        } else {
            panic!("Expected self-subsuming resolvent");
        }
    }
}

#[cfg(test)]
mod size_check {
    use super::*;
    #[test]
    fn clause_size() {
        let s = std::mem::size_of::<Clause>();
        println!("Clause (SmallVec<[Lit;7]>): {} bytes", s);
        assert!(s <= 64, "Clause must fit in 1 cache line, got {} bytes", s);
    }
}
