//! Variable Move-To-Front (VMTF) branching heuristic.
//!
//! VMTF keeps every variable on a doubly-linked list ordered by recency of
//! conflict involvement: bumping a variable moves it to the most-recent end.
//! The next decision is simply the most-recently-bumped variable that is
//! still unassigned, which in the common case is a cheap O(1) lookup rather
//! than the heap pop/rebuild VSIDS needs.
//!
//! # Design note: the persistent search cursor
//!
//! A naive implementation would rescan the list from the most-recent end on
//! every decision to skip already-assigned variables — correct, but O(n) per
//! decision once the search has assigned a long prefix of "recent" variables.
//! Instead this implementation keeps a cursor (`VMTF::cursor`, a private
//! field) that persists across decisions: it only ever moves toward the "least recent"
//! end as decisions consume variables, and jumps back toward the
//! "most recent" end when [`VMTF::on_unassign`] reports a freshly-freed
//! variable that was bumped more recently than wherever the cursor currently
//! sits. Net effect: a decision is O(1) amortized instead of O(n), and the
//! cursor always represents "the best candidate we know about so far".
//!
//! Reference: this mirrors the decision-queue technique used by modern
//! CDCL solvers such as CaDiCaL and Kissat (their `queue.cpp` / `queue.c`),
//! generalizing the fixed-position VMTF originally described by Ryan
//! ("Efficient algorithms for clause-learning SAT solvers", 2004).

use crate::literal::Var;

/// Sentinel meaning "no such neighbour" in [`Link`]'s `prev`/`next` fields.
/// Using a packed `u32` array (rather than `Option<Var>`) keeps a decision's
/// hot-path list walk to plain integer loads with no enum tag to unpack.
const NIL: u32 = u32::MAX;

/// One variable's position in the move-to-front list plus the tick at which
/// it was last bumped.
#[derive(Debug, Clone, Copy)]
struct Link {
    prev: u32,
    next: u32,
    /// Logical timestamp of the variable's last bump; higher = more recent.
    /// Used to decide, in [`VMTF::on_unassign`], whether a newly-freed
    /// variable should pull the search cursor toward it.
    last_bump: u64,
}

impl Link {
    const fn empty() -> Self {
        Self {
            prev: NIL,
            next: NIL,
            last_bump: 0,
        }
    }
}

/// Move-to-front decision queue.
///
/// `oldest` is the list end holding the variable bumped longest ago (or
/// never); `newest` is the most-recently-bumped end. Decisions are drawn by
/// walking from `VMTF::cursor` (a private field) toward `oldest` (via `prev` links) for the
/// first still-unassigned variable.
#[derive(Debug, Clone)]
pub struct VMTF {
    links: Vec<Link>,
    oldest: u32,
    newest: u32,
    /// Persistent decision cursor; see the module-level design note.
    cursor: u32,
    /// Monotonic bump counter, source of [`Link::last_bump`] timestamps.
    clock: u64,
}

impl VMTF {
    /// Build a queue over `num_vars` variables, initially ordered `0, 1, 2,
    /// ...` from oldest to newest (i.e. variable 0 starts as the *least*
    /// preferred candidate).
    #[must_use]
    pub fn new(num_vars: usize) -> Self {
        let mut q = Self {
            links: vec![Link::empty(); num_vars],
            oldest: NIL,
            newest: NIL,
            cursor: NIL,
            clock: 0,
        };
        for i in 0..num_vars {
            q.links[i].prev = if i == 0 { NIL } else { (i - 1) as u32 };
            q.links[i].next = if i + 1 == num_vars {
                NIL
            } else {
                (i + 1) as u32
            };
        }
        if num_vars > 0 {
            q.oldest = 0;
            q.newest = (num_vars - 1) as u32;
            q.cursor = q.newest;
        }
        q
    }

    /// Grow the queue to cover `num_vars` variables. A no-op if it is
    /// already at least that large — the queue never shrinks (mirrors the
    /// crate's other decision-order structures, `vsids::VSIDS` and
    /// `lrb::LRB`, both in private modules: freeing a slot back down
    /// is the caller's job via a full rebuild, see `Solver::reset`).
    pub fn resize(&mut self, num_vars: usize) {
        let old_len = self.links.len();
        if num_vars <= old_len {
            return;
        }
        self.links.resize(num_vars, Link::empty());
        for i in old_len..num_vars {
            let v = i as u32;
            self.links[i].prev = self.newest;
            self.links[i].next = NIL;
            if self.newest == NIL {
                self.oldest = v;
            } else {
                self.links[self.newest as usize].next = v;
            }
            self.newest = v;
        }
        // A freshly-grown queue had no candidates before; give the cursor
        // something to point at.
        if self.cursor == NIL {
            self.cursor = self.newest;
        }
    }

    fn unlink(&mut self, v: u32) {
        let (prev, next) = (self.links[v as usize].prev, self.links[v as usize].next);
        if prev == NIL {
            self.oldest = next;
        } else {
            self.links[prev as usize].next = next;
        }
        if next == NIL {
            self.newest = prev;
        } else {
            self.links[next as usize].prev = prev;
        }
    }

    fn link_as_newest(&mut self, v: u32) {
        self.links[v as usize].prev = self.newest;
        self.links[v as usize].next = NIL;
        if self.newest == NIL {
            self.oldest = v;
        } else {
            self.links[self.newest as usize].next = v;
        }
        self.newest = v;
    }

    /// Move `var` to the "most recent" end and stamp it with a fresh
    /// timestamp. `assigned` reports whether `var` currently has a value on
    /// the trail: only an *unassigned* bumped variable is eligible to be the
    /// next decision, so the cursor only jumps to it in that case — bumping
    /// an already-assigned variable (e.g. one on the trail from a conflict's
    /// resolution) still records recency for when it is later freed, but
    /// must not make it the immediate next pick.
    pub fn bump(&mut self, var: Var, assigned: bool) {
        let Ok(v) = u32::try_from(var.index()) else {
            return;
        };
        if (v as usize) >= self.links.len() {
            return;
        }
        if self.newest != v {
            self.unlink(v);
            self.link_as_newest(v);
        }
        self.clock += 1;
        self.links[v as usize].last_bump = self.clock;
        if !assigned {
            self.cursor = v;
        }
    }

    /// Draw the next decision: the most-recently-bumped variable that
    /// `assigned` reports as still unassigned, searching from the cursor
    /// toward the oldest end. Returns `None` only if every variable in the
    /// queue is assigned.
    ///
    /// The cursor only ever *decreases in recency* through this method (it
    /// tracks along); it is restored to a fresher position by
    /// [`Self::on_unassign`] when backtracking frees a more-recently-bumped
    /// variable that the cursor had already walked past.
    pub fn next_decision<F>(&mut self, mut assigned: F) -> Option<Var>
    where
        F: FnMut(Var) -> bool,
    {
        let found = self.scan_from(self.cursor, &mut assigned);
        let found = found.or_else(|| {
            // The cursor had walked past every unassigned variable toward
            // the oldest end without success — this happens when a
            // backtrack frees variables that [`Self::on_unassign`] judged
            // less recent than the cursor's position at the time, but which
            // are nonetheless the only unassigned candidates left. A full
            // rescan from the newest end is the correctness fallback; it is
            // rare (only after a deep backtrack) so its O(n) cost is
            // amortized away.
            self.scan_from(self.newest, &mut assigned)
        });
        if let Some(v) = found {
            self.cursor = v;
        }
        found.map(Var::new)
    }

    /// Read-only counterpart to [`Self::next_decision`]: which variable the
    /// next call *would* return, without moving the cursor.
    ///
    /// Exists for a caller that only wants to know *where the queue's
    /// candidate ranking currently sits* — e.g. `Solver::reuse_trail`
    /// comparing past decisions against "whatever would be decided next" to
    /// pick a partial-restart prefix — and must not perturb the actual
    /// decision state to find out: the cursor's position affects every
    /// *real* decision `next_decision` returns downstream, so a query like
    /// this one has to be side-effect-free.
    #[must_use]
    pub fn peek_next_decision<F>(&self, mut assigned: F) -> Option<Var>
    where
        F: FnMut(Var) -> bool,
    {
        self.scan_from(self.cursor, &mut assigned)
            .or_else(|| self.scan_from(self.newest, &mut assigned))
            .map(Var::new)
    }

    fn scan_from<F>(&self, start: u32, assigned: &mut F) -> Option<u32>
    where
        F: FnMut(Var) -> bool,
    {
        let mut at = start;
        while at != NIL {
            if !assigned(Var::new(at)) {
                return Some(at);
            }
            at = self.links[at as usize].prev;
        }
        None
    }

    /// Notify the queue that `var` was just unassigned (a backtrack freed
    /// it). If `var` was bumped more recently than whatever the cursor
    /// currently points at, pull the cursor forward to `var` so the next
    /// decision reconsiders it instead of a rescan discovering it later.
    pub fn on_unassign(&mut self, var: Var) {
        let Ok(v) = u32::try_from(var.index()) else {
            return;
        };
        if (v as usize) >= self.links.len() {
            return;
        }
        let freed_bump = self.links[v as usize].last_bump;
        let cursor_bump = if self.cursor == NIL {
            0
        } else {
            self.links[self.cursor as usize].last_bump
        };
        if freed_bump > cursor_bump {
            self.cursor = v;
        }
    }

    /// Last-bump timestamp of `var` (0 if it was never bumped or is out of
    /// range). Exposed for diagnostics/statistics; not used by decision
    /// logic itself.
    #[must_use]
    pub fn activity(&self, var: Var) -> u64 {
        self.links.get(var.index()).map_or(0, |link| link.last_bump)
    }

    /// Snapshot of queue-wide counters.
    #[must_use]
    pub fn stats(&self) -> VmtfStats {
        VmtfStats {
            tracked_vars: self.links.len(),
            total_bumps: self.clock,
        }
    }
}

/// Point-in-time statistics for a [`VMTF`] queue.
#[derive(Debug, Clone, Copy, Default)]
pub struct VmtfStats {
    /// Number of variables the queue currently tracks.
    pub tracked_vars: usize,
    /// Total number of bumps performed since construction.
    pub total_bumps: u64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pr26_vmtf_bump_promotes_to_next_decision() {
        let mut q = VMTF::new(4);
        q.bump(Var::new(0), false);
        assert_eq!(q.next_decision(|_| false), Some(Var::new(0)));
    }

    #[test]
    fn test_pr26_vmtf_search_pointer_skips_assigned() {
        let mut q = VMTF::new(3);
        q.bump(Var::new(2), false);
        // Variable 2 is on the trail (assigned): the queue must skip it and
        // fall through to the next-most-recent unassigned candidate.
        let picked = q.next_decision(|v| v == Var::new(2)).expect("candidate");
        assert_eq!(picked, Var::new(1));
    }

    #[test]
    fn test_pr26_vmtf_notify_unassigned_moves_pointer() {
        let mut q = VMTF::new(5);
        // Bump 4 twice so it is clearly the most recent, then "assign" it
        // (bump with assigned=true keeps the cursor from jumping to it).
        q.bump(Var::new(4), true);
        // Cursor sits at the initial newest (4) already from `new`; move it
        // down by consuming decisions for 3, 2 so it lags behind.
        assert_eq!(q.next_decision(|v| v == Var::new(4)), Some(Var::new(3)));
        assert_eq!(
            q.next_decision(|v| v == Var::new(4) || v == Var::new(3)),
            Some(Var::new(2))
        );
        // Now free variable 4 (a backtrack). Its bump timestamp is higher
        // than the cursor's (which sits at 2), so the pointer should jump
        // back to it.
        q.on_unassign(Var::new(4));
        assert_eq!(q.next_decision(|_| false), Some(Var::new(4)));
    }

    #[test]
    fn test_pr26_vmtf_next_decision_none_when_all_assigned() {
        let mut q = VMTF::new(3);
        assert_eq!(q.next_decision(|_| true), None);
    }

    #[test]
    fn test_pr26_vmtf_resize_grows_and_stays_selectable() {
        let mut q = VMTF::new(2);
        q.resize(5);
        assert_eq!(q.stats().tracked_vars, 5);
        // Every one of the 5 variables must eventually be reachable.
        let mut seen = [false; 5];
        while let Some(v) = q.next_decision(|v: Var| seen[v.index()]) {
            assert!(!seen[v.index()], "must not repeat a variable");
            seen[v.index()] = true;
        }
        assert!(
            seen.iter().all(|&s| s),
            "every variable reachable: {seen:?}"
        );
    }

    #[test]
    fn test_pr26_vmtf_resize_noop_when_shrinking_requested() {
        let mut q = VMTF::new(5);
        q.resize(2); // must not shrink or panic
        assert_eq!(q.stats().tracked_vars, 5);
    }

    #[test]
    fn test_pr26_vmtf_activity_reflects_bump_recency() {
        let mut q = VMTF::new(3);
        let before = q.activity(Var::new(0));
        q.bump(Var::new(0), false);
        assert!(q.activity(Var::new(0)) > before);
    }

    #[test]
    fn test_pr26_vmtf_out_of_range_bump_is_noop() {
        let mut q = VMTF::new(2);
        // Must not panic on a var beyond the tracked range.
        q.bump(Var::new(10), false);
        q.on_unassign(Var::new(10));
        assert_eq!(q.activity(Var::new(10)), 0);
    }
}
