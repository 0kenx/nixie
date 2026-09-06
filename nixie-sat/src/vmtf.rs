//! Variable Move-To-Front (VMTF) branching – faithful port of cadical's
//! focused-mode decision queue (`queue.cpp`, `analyze.cpp::bump_queue`).
//!
//! Conflict-involved variables are moved to the tail of a doubly-linked list;
//! the next decision is the most-recently-bumped *unassigned* variable, found
//! by scanning backward from a persistent search pointer. The pointer is
//! updated only for unassigned bumped variables (cadical `update_queue_unassigned`),
//! so a decision never re-scans the whole list – the bug in the previous
//! implementation (which reset the pointer on every bump → O(n) per decision).

use crate::literal::Var;

const NULL: u32 = u32::MAX;

/// VMTF move-to-front decision queue (cadical focused-mode branching).
#[derive(Debug)]
pub struct VMTF {
    /// `prev[v]` / `next[v]`: doubly-linked list links (NULL = none).
    prev: Vec<u32>,
    next: Vec<u32>,
    /// head = oldest, tail = most-recently-bumped.
    head: u32,
    tail: u32,
    /// Persistent search pointer: scan backward (via `prev`) from here.
    search: u32,
    /// Per-variable bump timestamp (cadical `btab`).
    btab: Vec<u64>,
    bumped: u64,
}

impl VMTF {
    /// Construct a VMTF decision queue for `num_vars` variables.
    #[must_use]
    pub fn new(num_vars: usize) -> Self {
        let mut s = Self {
            prev: vec![NULL; num_vars],
            next: vec![NULL; num_vars],
            head: NULL,
            tail: NULL,
            search: NULL,
            btab: vec![0; num_vars],
            bumped: 0,
        };
        for i in 0..num_vars {
            s.prev[i] = if i == 0 { NULL } else { (i - 1) as u32 };
            s.next[i] = if i + 1 == num_vars {
                NULL
            } else {
                (i + 1) as u32
            };
        }
        if num_vars > 0 {
            s.head = 0;
            s.tail = (num_vars - 1) as u32;
            s.search = s.tail;
        }
        s
    }

    /// Grow the queue to cover `num_vars` variables (no-op if already large enough).
    pub fn resize(&mut self, num_vars: usize) {
        if num_vars <= self.prev.len() {
            return;
        }
        let old = self.prev.len();
        self.prev.resize(num_vars, NULL);
        self.next.resize(num_vars, NULL);
        self.btab.resize(num_vars, 0);
        for i in old..num_vars {
            if self.tail != NULL {
                self.next[self.tail as usize] = i as u32;
            } else {
                self.head = i as u32;
            }
            self.prev[i] = if self.tail == NULL { NULL } else { self.tail };
            self.next[i] = NULL;
            self.tail = i as u32;
        }
    }

    fn dequeue(&mut self, v: u32) {
        let p = self.prev[v as usize];
        let n = self.next[v as usize];
        if p != NULL {
            self.next[p as usize] = n;
        } else {
            self.head = n;
        }
        if n != NULL {
            self.prev[n as usize] = p;
        } else {
            self.tail = p;
        }
    }

    fn enqueue(&mut self, v: u32) {
        self.prev[v as usize] = self.tail;
        self.next[v as usize] = NULL;
        if self.tail != NULL {
            self.next[self.tail as usize] = v;
        } else {
            self.head = v;
        }
        self.tail = v;
    }

    /// Move `var` to the tail (most-recent) and bump its timestamp (cadical
    /// `bump_queue`). `is_assigned` reports assignment status so the search
    /// pointer is updated only for unassigned bumped variables.
    pub fn bump<F>(&mut self, var: Var, is_assigned: F)
    where
        F: Fn(Var) -> bool,
    {
        let v = match u32::try_from(var.index()) {
            Ok(v) if (v as usize) < self.next.len() => v,
            _ => return,
        };
        // Already the tail (most-recent): nothing to do.
        if self.next[v as usize] == NULL {
            // still bump the timestamp + maybe update search pointer.
        } else {
            self.dequeue(v);
            self.enqueue(v);
        }
        self.bumped = self.bumped.saturating_add(1);
        self.btab[v as usize] = self.bumped;
        if !is_assigned(var) {
            self.search = v;
        }
    }

    /// Pick the next decision variable: the most-recently-bumped unassigned
    /// variable, scanning backward from the search pointer. Returns `None` if
    /// every variable is assigned.
    ///
    /// Under `NIXIE_VMTF_SCAN=1` each pick adds its walked-link count to
    /// [`crate::DIAG_VMTF_SCAN`] – divide by decision count for the mean scan
    /// length; a growing value means the search pointer sits in stale,
    /// fully-assigned list territory (decision-stagnation studies read this).
    /// The gate keeps the default path free of the counter update.
    pub fn next_decision<F>(&mut self, mut is_assigned: F) -> Option<Var>
    where
        F: FnMut(Var) -> bool,
    {
        if self.head == NULL {
            return None;
        }
        #[cfg(feature = "std")]
        let diag = crate::vmtf_scan_enabled();
        #[cfg(not(feature = "std"))]
        let diag = false;
        let mut steps: u64 = 1;
        let mut res = self.search;
        while res != NULL && is_assigned(Var::new(res)) {
            res = self.prev[res as usize];
            steps += 1;
        }
        if res == NULL {
            // Search pointer exhausted toward the head (lagged behind a
            // backtrack): retry from the tail.
            res = self.tail;
            while res != NULL && is_assigned(Var::new(res)) {
                res = self.prev[res as usize];
                steps += 1;
            }
        }
        if res == NULL {
            return None;
        }
        if diag {
            crate::DIAG_VMTF_SCAN.fetch_add(steps, core::sync::atomic::Ordering::Relaxed);
        }
        self.search = res;
        Some(Var::new(res))
    }

    /// Called when a variable is unassigned (backtrack): if this variable's
    /// bump timestamp is more recent than the search pointer's, move the
    /// pointer here (cadical `unassign` → `update_queue_unassigned`). This is
    /// what keeps the pointer at the most-recently-bumped unassigned variable
    /// – without it the pointer stalls and every decision re-scans.
    pub fn notify_unassigned(&mut self, var: Var) {
        let v = match u32::try_from(var.index()) {
            Ok(v) if (v as usize) < self.btab.len() => v,
            _ => return,
        };
        let var_bumped = self.btab[v as usize];
        let search_bumped = if self.search != NULL {
            self.btab[self.search as usize]
        } else {
            0
        };
        if var_bumped > search_bumped {
            self.search = v;
        }
    }

    /// kissat `adjust_scores_and_phases_of_fresh_variables` (factor.c): move
    /// each var to the **head** (oldest end — the *last* decided), then
    /// restamp the whole list in head→tail order and point `search` at the
    /// tail.  kissat uses this to make freshly introduced factor-hub
    /// variables the LEAST prominent decisions in both VMTF (oldest end)
    /// and VSIDS (score 0) — see `solver/factor.rs`'s port notes: the list's
    /// tail is the *next* decision (`bump` moves conflict vars there), so
    /// linking the fresh vars at the head schedules them last, not first.
    pub fn enqueue_oldest_and_restamp(&mut self, vars: &[Var]) {
        for &var in vars {
            let v = match u32::try_from(var.index()) {
                Ok(v) if (v as usize) < self.next.len() => v,
                _ => continue,
            };
            // Already unlinked (never enqueued): nothing to dequeue.
            if self.prev[v as usize] != NULL || self.next[v as usize] != NULL || self.head == v {
                self.dequeue(v);
            }
        }
        // Relink at the head in iteration order: the LAST var of `vars`
        // ends up as the very head (kissat links each at `queue->first`
        // in the same order).
        for &var in vars {
            let v = match u32::try_from(var.index()) {
                Ok(v) if (v as usize) < self.next.len() => v,
                _ => continue,
            };
            self.prev[v as usize] = NULL;
            self.next[v as usize] = self.head;
            if self.head != NULL {
                self.prev[self.head as usize] = v;
            } else {
                self.tail = v;
            }
            self.head = v;
        }
        // Restamp: btab order = list order (head = 1 … tail = n), search at
        // the tail — exactly kissat's restamp loop.  This keeps
        // `notify_unassigned`'s timestamp comparison consistent with the
        // relinked order.
        let mut stamp = 0u64;
        let mut idx = self.head;
        while idx != NULL {
            stamp += 1;
            self.btab[idx as usize] = stamp;
            idx = self.next[idx as usize];
        }
        self.bumped = self.bumped.max(stamp);
        self.search = self.tail;
    }

    /// Bump timestamp of a variable (no list move) – kept for API compatibility.
    pub fn activity(&self, var: Var) -> u64 {
        self.btab.get(var.index()).copied().unwrap_or(0)
    }
}

/// Statistics stub (kept for the public re-export `pub use vmtf::{VMTF, VmtfStats}`).
#[derive(Debug, Clone, Default)]
pub struct VmtfStats {
    /// Total bumps.
    pub total_bumps: u64,
}

impl VMTF {
    /// Return a snapshot of VMTF statistics (bump count, etc.).
    #[must_use]
    pub fn stats(&self) -> VmtfStats {
        VmtfStats {
            total_bumps: self.bumped,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bump_then_pick() {
        let mut q = VMTF::new(4); // tail = 3
        q.bump(Var::new(0), |_| false); // 0 → tail
        let d = q.next_decision(|_| false).expect("decision");
        assert_eq!(d, Var::new(0), "most-recently-bumped picked first");
    }

    #[test]
    fn skip_assigned() {
        let mut q = VMTF::new(3);
        q.bump(Var::new(2), |_| false); // tail = 2
        // var 2 assigned → pick next most-recent unassigned.
        let d = q.next_decision(|v| v == Var::new(2)).expect("decision");
        assert_eq!(d, Var::new(1));
    }

    #[test]
    fn enqueue_oldest_puts_vars_at_head_decided_last() {
        // kissat `adjust_scores_and_phases_of_fresh_variables`: fresh vars
        // land at the head (oldest end).  The tail remains the next
        // decision; the fresh vars are only reached after everything else.
        let mut q = VMTF::new(4); // list 0→1→2→3, tail = 3
        q.bump(Var::new(1), |_| false); // 1 → tail; order 0,2,3,1
        q.enqueue_oldest_and_restamp(&[Var::new(2)]); // 2 → head; order 2,0,3,1
        assert_eq!(
            q.next_decision(|_| false),
            Some(Var::new(1)),
            "tail still first"
        );
        assert_eq!(q.next_decision(|v| v == Var::new(1)), Some(Var::new(3)));
        assert_eq!(
            q.next_decision(|v| v.index() >= 3 || v == Var::new(1)),
            Some(Var::new(0))
        );
        assert_eq!(
            q.next_decision(|v| v != Var::new(2)),
            Some(Var::new(2)),
            "the fresh head var is decided last"
        );
    }

    #[test]
    fn enqueue_oldest_restamps_in_list_order() {
        let mut q = VMTF::new(3);
        q.bump(Var::new(0), |_| false); // order 1,2,0
        q.enqueue_oldest_and_restamp(&[Var::new(1), Var::new(2)]);
        // Links: 2,1(head side… both moved),0 → order 2,1,0? 2 is the very
        // head (last linked), then 1, then 0 at the tail.
        let mut order = Vec::new();
        let mut idx = q.head;
        while idx != NULL {
            order.push(idx);
            idx = q.next[idx as usize];
        }
        assert_eq!(order, vec![2, 1, 0]);
        // btab is strictly increasing along the list (restamp invariant).
        assert!(q.btab[2] < q.btab[1] && q.btab[1] < q.btab[0]);
        assert_eq!(q.search, 0, "search points at the tail");
    }
}
