//! Optional, solver-local accounting for the actual propagation paths.
//!
//! This module is absent unless `bcp-work` is enabled. Counts cover calls to
//! this solver's `propagate`, including inprocessing, not the whole solve.
//! They do not select a scanner and must never feed a budget or policy.

/// Cumulative BCP work, owned by one solver (no process-global atomics).
///
/// Snapshot before and after a phase to obtain its work. Counts include
/// repeated visits after backtracking and failed lucky attempts (whose legacy
/// propagation counter is rolled back), but not other propagation engines,
/// analysis, allocation, proof work or clause maintenance. Enabling this
/// feature adds measurement overhead; use ordinary builds to measure speed.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct PropagationWork {
    /// Trail entries dequeued, including a possible step-limit abort.
    pub dequeued: u64,
    /// Entries whose scan starts after passing the step-limit check.
    pub started: u64,
    /// Started literals with at least one binary edge in either span.
    pub binary_lists: u64,
    /// Primary CSR edges actually visited (excludes an unvisited suffix).
    pub binary_primary_visits: u64,
    /// Post-build overflow edges actually visited.
    pub binary_overflow_visits: u64,
    /// Assignments made by binary implications, excluding decisions/facts.
    pub binary_assignments: u64,
    /// Binary conflicts encountered, including repeated encounters.
    pub binary_conflicts: u64,
    /// Sum of ceil(primary bytes / 128) and ceil(overflow bytes / 128),
    /// using the full lengths at scan entry, even after an early conflict.
    pub binary_list_lines: u64,
    /// Nonempty long-watch lists reached after the binary scan succeeds.
    pub long_lists: u64,
    /// Sum of ceil(long-watch bytes / 128) at entry to reached lists.
    /// Includes an unvisited suffix on conflict, as in reference tick models.
    pub long_list_lines: u64,
    /// Long watchers actually visited; copying a conflict suffix is not a visit.
    pub long_visits: u64,
    /// Clause-arena lookups on blocker misses, including deleted headers.
    pub clause_reads: u64,
    /// Clause reads rejected as deleted/non-live.
    pub deleted: u64,
    /// Live clause reads satisfied by the other watched literal.
    pub first_satisfied: u64,
    /// Tail literals whose assignment is inspected while finding a replacement.
    pub tail_probes: u64,
    /// Scans parked on a true tail literal without moving the watch.
    pub tail_satisfied: u64,
    /// Watches moved to an undefined tail literal's destination list.
    pub watch_moves: u64,
    /// Assignments made from long clauses (not decisions or input units).
    pub long_assignments: u64,
    /// Conflicts encountered in long-watch scans.
    pub long_conflicts: u64,
}

impl PropagationWork {
    /// Long-watch visits discharged by the blocker without reading the clause.
    pub fn blocker_hits(&self) -> u64 {
        self.long_visits - self.clause_reads
    }

    /// Reference-shaped estimate, with Nixie's actual list representations:
    /// started literals + estimated list lines + clause reads + moves + assigns.
    ///
    /// This is neither measured cache traffic nor Kissat's `search_ticks`:
    /// scopes, entry widths, binary layout and true-tail handling differ.
    /// Tail probes and other raw counts remain available separately. A kernel
    /// rewrite can change CPU cost while leaving this estimate identical.
    /// `u128` keeps the sum of individually valid `u64` counters exact.
    pub fn estimated_ticks(&self) -> u128 {
        u128::from(self.started)
            + u128::from(self.binary_list_lines)
            + u128::from(self.long_list_lines)
            + u128::from(self.clause_reads)
            + u128::from(self.watch_moves)
            + u128::from(self.binary_assignments)
            + u128::from(self.long_assignments)
    }

    // Cursor-local counters survive prefix/suffix transitions and unit yields.
    // Merge and clear after each advance, including conflict/Done, so no exit
    // loses events and unit resumption never counts the same prefix twice.
    pub(super) fn take_watch_scan(&mut self, scan: &mut Self) {
        self.long_visits += scan.long_visits;
        self.clause_reads += scan.clause_reads;
        self.deleted += scan.deleted;
        self.first_satisfied += scan.first_satisfied;
        self.tail_probes += scan.tail_probes;
        self.tail_satisfied += scan.tail_satisfied;
        self.watch_moves += scan.watch_moves;
        self.long_assignments += scan.long_assignments;
        self.long_conflicts += scan.long_conflicts;
        *scan = Self::default();
    }
}

/// The callers pass actual Vec/span lengths, so the represented bytes fit
/// in the address space. This estimates 128-byte lines, not physical misses.
pub(super) fn list_lines<T>(len: usize) -> u64 {
    ((len as u64) * core::mem::size_of::<T>() as u64).div_ceil(128)
}
