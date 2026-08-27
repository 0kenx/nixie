//! ProbSAT local search ("walk") – faithful port of the *mechanism* of
//! CaDiCaL's `walk.cpp`, wired into the rephase schedule as the `walk`
//! strategy.
//!
//! CaDiCaL schedules a random walk (`rephase_walk`) between stable/focused
//! search phases: starting from the current decision phases, run ProbSAT
//! (pick a random *broken* clause, flip one of its literals with probability
//! `cb^-break`) under a tick budget proportional to the search effort since
//! the last walk, and write the best assignment seen back into the saved
//! phases. The next CDCL descent then restarts from a phase that falsifies
//! fewer original clauses.
//!
//! Divergences from CaDiCaL's implementation (behaviour-preserving or
//! strictly local):
//!
//! * **Tick accounting**: CaDiCaL charges every occurrence-list visit through
//!   its `ticks` model; this port charges `1 + Σ|occ|` per flip, which has the
//!   same budget semantics (walk length scales with search effort).
//! * **Best-model memory**: CaDiCaL stores a compressed flip trail instead of
//!   snapshotting all values on every improvement; this port snapshots the
//!   `values` vector (improvements are monotonically decreasing, so the copy
//!   is rare) and pays `O(num_vars)` per improvement instead.
//! * **Warmup** (`opts.warmup`, a propagation-based phase improvement run
//!   before the walk) is not implemented.
//! * Like CaDiCaL's `rephase_walk`, a walk that reaches zero broken clauses
//!   only writes the phases (CaDiCaL's `walk()` discards the model); the
//!   satisfying assignment is reached again through ordinary search.
//!
//! Level-0 (fixed) variables are never flipped: their forced value seeds the
//! assignment and clauses satisfied by a fixed literal are permanently
//! satisfied, mirroring CaDiCaL removing fixed variables through garbage
//! collection before a walk round.

use super::*;

impl Solver {
    /// One ProbSAT round over the original clauses (cadical `walk()`):
    /// tick-budgeted, seeded from the current decision phases, writing the
    /// best assignment found back into the saved phases.
    pub(super) fn walk(&mut self) {
        // Budget: per-mille of the search ticks accumulated since the last
        // walk (cadical `walkeffort`, default 80 = 8%), clamped to
        // [walkmineff, 1e3·walkmaxeff] = [0, 1e10].
        let ticks = self.ticks_focused.saturating_add(self.ticks_stable);
        let delta = ticks.saturating_sub(self.last_walk_ticks);
        self.last_walk_ticks = ticks;
        let limit = delta.saturating_mul(self.config.walk_effort) / 1000;
        if self.config.walk_warmup {
            self.warmup();
        }
        self.walk_round(limit.min(10_000_000_000));
    }

    /// cadical `warmup()` (plain-CNF shape): decide + propagate to a full
    /// assignment, IGNORING conflicts, and seed the saved phases with it.
    ///
    /// Local search is bad at following propagation chains; CDCL propagation
    /// is nothing but.  Each conflict is counted and skipped — the queue
    /// literal is consumed by `next_to_propagate` before its watchers are
    /// scanned, so re-invoking `propagate` after an ignored conflict drains
    /// onward without spinning.  Values never flip mid-pass (assignment is
    /// monotone), so one post-pass trail→phase copy equals cadical's
    /// write-at-assign-time.  Eliminated variables stay unassigned (their
    /// phases persist from the search) exactly like cadical's dummy
    /// decisions leave them at their current phase.  The pass ends with the
    /// trail back at root, same state the rephase step guarantees today.
    fn warmup(&mut self) {
        if self.num_vars == 0 {
            return;
        }
        self.stats.walk.warmups += 1;
        // Decision order: a flat index cursor, NOT the decision queues —
        // `pick_branch_var` pops the VMTF/VSIDS heaps destructively and
        // falls back to an O(num_vars) scan once they drain, which is
        // quadratic over a full-assignment pass.  cadical decides by score
        // order; the pass is propagation-consistent-from-phases either way
        // (measurement below judges whether score order matters here).
        for i in 0..self.num_vars {
            let var = Var::new(i as u32);
            if self.trail.is_assigned(var) || self.var_eliminated(var) {
                continue;
            }
            self.trail.new_decision_level();
            let pol = self.decision_polarity(var);
            self.trail
                .assign_decision(if pol { Lit::pos(var) } else { Lit::neg(var) });
            while let Some(_conflict) = self.propagate() {
                self.stats.walk.warmup_conflicts += 1;
                // `propagate`'s conflict paths re-queue the conflicted
                // literal for the CDCL re-visit contract; popping it again
                // here would re-find the same conflict forever (warmup
                // never backtracks).  Pop-and-discard the re-queued entry:
                // the pass moves on to the next queue literal; the skipped
                // literal's remaining watchers are only ever *more*
                // falsified later in the pass, so re-scanning could not
                // have produced new assignments.  (`backtrack_to_root`
                // clamps the head at pass end; the queue contract is
                // restored for the next solve.)
                let _ = self.trail.next_to_propagate();
            }
        }
        for &lit in self.trail.assignments() {
            let vi = lit.var().index();
            if vi < self.phase.len() {
                self.phase[vi] = lit.is_pos();
            }
        }
        self.backtrack_to_root();
    }

    /// cadical `walk_round (limit, false)` over the original clauses.
    fn walk_round(&mut self, limit: u64) {
        self.stats.walk.count += 1;
        if self.num_vars == 0 {
            return;
        }

        // Level-0 facts survive the root backtrack that precedes every walk;
        // their values are forced. `values[v]` is the walk's working
        // assignment: `true` makes the positive literal of `v` true.
        let mut values = vec![false; self.num_vars];
        let mut fixed = vec![false; self.num_vars];
        for i in 0..self.num_vars {
            let var = Var::new(i as u32);
            match self.trail.value(var) {
                LBool::True => {
                    values[i] = true;
                    fixed[i] = true;
                }
                LBool::False => fixed[i] = true,
                LBool::Undef => {
                    // cadical initializes from `decide_phase (idx, target)`:
                    // the target phase while target phases are active, else
                    // the saved phase.
                    values[i] = if self.target_phase_active() {
                        self.target_phase.get(i).copied().unwrap_or(false)
                    } else {
                        self.phase.get(i).copied().unwrap_or(false)
                    };
                }
            }
        }

        // Occurrence lists over the original (irredundant), non-deleted
        // clauses of size >= 2; units are level-0 facts already in `fixed`.
        // `slots` dense-indexes the participants; `true_count` counts true
        // literals per clause so flip updates are O(occurrences). Literal
        // lists are copied into `slots` (the clause database stays borrowed
        // only during collection, and the flip loop needs `&mut self` for the
        // RNG) – the same order of work cadical pays rebuilding its walk
        // watches each round.
        let mut occ: Vec<Vec<u32>> = vec![Vec::new(); self.num_vars * 2];
        let mut slots: Vec<Vec<Lit>> = Vec::new();
        let mut true_count: Vec<u32> = Vec::new();
        let mut lit_sum = 0u64;
        for id in self.clauses.iter_ids() {
            let Some(clause) = self.clauses.get(id) else {
                continue;
            };
            if clause.learned || clause.lits.len() < 2 {
                continue;
            }
            // Permanently satisfied by a fixed true literal / permanently
            // broken only if every literal is fixed-false (impossible: that
            // clause is falsified at level 0 and the solver is UNSAT).
            if clause.lits.iter().any(|&l| {
                let vi = l.var().index();
                vi < self.num_vars && fixed[vi] && values[vi] == l.is_pos()
            }) {
                continue;
            }
            // A clause with a fixed literal can never be repaired by
            // flipping (its fixed-false literals stay false), so keep it out
            // of `broken` (it would wedge the picker) and out of the
            // occurrence lists entirely.
            if clause.lits.iter().any(|&l| fixed[l.var().index()]) {
                continue;
            }
            let slot = slots.len() as u32;
            let n_true = clause
                .lits
                .iter()
                .filter(|&&l| values[l.var().index()] == l.is_pos())
                .count() as u32;
            for &l in clause.lits {
                occ[l.code() as usize].push(slot);
                lit_sum = lit_sum.saturating_add(1);
            }
            slots.push(clause.lits.to_vec());
            let _ = &clause;
            true_count.push(n_true);
        }
        if slots.is_empty() {
            return;
        }

        // Broken clauses (true_count == 0), in_broken for O(1) lazy removal.
        let mut broken: Vec<u32> = Vec::new();
        let mut in_broken = vec![false; slots.len()];
        let mut broken_count: u64 = 0;
        for (slot, &n) in true_count.iter().enumerate() {
            if n == 0 {
                broken.push(slot as u32);
                in_broken[slot] = true;
                broken_count += 1;
            }
        }
        let mut minimum = broken.len() as u64;
        // cadical records the starting assignment as the first best
        // (`walk_save_minimum` before the loop), so the phase write-back at
        // the end always happens – even a zero-improvement walk imports the
        // target phases into `saved` (that is a real cadical behaviour).
        let mut best_values = values.clone();

        // ProbSAT scoring table (cadical `populate_table`): probabilities
        // cb^-i with cb picked from the average clause size (Balint's CB
        // values, piecewise-linear interpolated). `use_size_based_cb` only
        // every second round, like cadical.
        let average_size = lit_sum as f64 / slots.len() as f64;
        let cb = if self.stats.walk.count.is_multiple_of(2) {
            fit_cb_value(average_size)
        } else {
            2.0
        };
        let base = 1.0 / cb;
        let mut table: SmallVec<[f64; 64]> = SmallVec::new();
        let mut next = 1.0f64;
        loop {
            table.push(next);
            let scaled = next * base;
            if scaled == 0.0 || scaled == next {
                break;
            }
            next = scaled;
        }

        let mut ticks: u64 = 0;
        let mut flip: u64 = 0;
        while broken_count > 0 && ticks < limit {
            // cadical's walk loop checks `terminated_asynchronously` every
            // flip; checking the flag's atomic load every flip is wasteful,
            // so this port polls every 1024 flips (a walk that must stop
            // loses at most 1024 flips of work; the search loop re-checks
            // immediately after and returns Unknown).
            flip += 1;
            if flip.is_multiple_of(1024)
                && let Some(flag) = &self.interrupt
                && flag.load(core::sync::atomic::Ordering::Relaxed)
            {
                break;
            }
            self.stats.walk.flips += 1;
            self.stats.walk.broken += broken_count;

            // Pick a random broken clause (cadical `walk_pick_clause`).
            // Entries fixed by an earlier flip are lazily removed here.
            let picked = loop {
                if broken.is_empty() {
                    break u32::MAX;
                }
                let pos = (self.rand_u64() % broken.len() as u64) as usize;
                let slot = broken[pos];
                if !in_broken[slot as usize] {
                    broken.swap_remove(pos);
                    continue;
                }
                break slot;
            };
            if picked == u32::MAX {
                break;
            }
            let clause_lits = &slots[picked as usize];

            // Score every candidate literal by its break count: the number of
            // occurrence clauses of the negated literal that are satisfied
            // *solely* by it (cadical `walk_break_value`). A candidate whose
            // break count exceeds the table is unflippable (prob 0), like
            // cadical's implicit table bound.
            ticks = ticks.saturating_add(1);
            let mut scores: SmallVec<[f64; 8]> = SmallVec::new();
            let mut sum = 0.0f64;
            for &lit in clause_lits {
                let mut brk = 0u32;
                for &slot in &occ[lit.negate().code() as usize] {
                    if true_count[slot as usize] == 1 {
                        brk += 1;
                    }
                }
                ticks = ticks.saturating_add(occ[lit.negate().code() as usize].len() as u64);
                let score = table.get(brk as usize).copied().unwrap_or(0.0);
                scores.push(score);
                sum += score;
            }

            // Select by cumulative distribution (cadical `walk_pick_lit`):
            // the first literal whose cumulative score passes a uniform
            // point under `sum` (the first literal in the degenerate all-zero
            // case, matching cadical's roulette scan).
            let lim = sum * self.rand_f64();
            let mut acc = 0.0;
            let mut chosen = clause_lits[0];
            for (&lit, &score) in clause_lits.iter().zip(scores.iter()) {
                acc += score;
                if acc > lim {
                    chosen = lit;
                    break;
                }
            }

            // Flip: the old true literal `t` turns false, `!t` turns true.
            let var_idx = chosen.var().index();
            let t = if values[var_idx] {
                Lit::pos(Var::new(var_idx as u32))
            } else {
                Lit::neg(Var::new(var_idx as u32))
            };
            values[var_idx] = !values[var_idx];
            for &slot in &occ[t.code() as usize] {
                let n = &mut true_count[slot as usize];
                *n = n.saturating_sub(1);
                if *n == 0 && !in_broken[slot as usize] {
                    in_broken[slot as usize] = true;
                    broken.push(slot);
                    broken_count += 1;
                }
            }
            for &slot in &occ[t.negate().code() as usize] {
                let n = &mut true_count[slot as usize];
                *n += 1;
                if *n == 1 && in_broken[slot as usize] {
                    in_broken[slot as usize] = false; // satisfied now
                    broken_count -= 1;
                }
            }
            ticks = ticks.saturating_add(occ[t.code() as usize].len() as u64);
            ticks = ticks.saturating_add(occ[t.negate().code() as usize].len() as u64);

            // New global minimum: snapshot the best assignment
            // (cadical `walk_save_minimum`).
            if broken_count < minimum {
                minimum = broken_count;
                best_values.copy_from_slice(&values);
            }

            // Compaction keeps the lazily-deleted tail from growing without
            // bound (each satisfied entry stays until its slot is picked).
            if broken.len() > 4 * (broken_count as usize).max(8) {
                broken.retain(|&s| in_broken[s as usize]);
            }
        }

        if self.stats.walk.minimum == 0 || minimum < self.stats.walk.minimum {
            self.stats.walk.minimum = minimum;
        }
        self.stats.walk.ticks += ticks;

        // cadical `save_final_minimum`: write the best assignment into the
        // saved phases (fixed variables keep their forced value).
        for i in 0..self.num_vars {
            if !fixed[i] {
                self.phase[i] = best_values[i];
            }
        }
    }
}

/// cadical `fitcbval`: piecewise-linear interpolation of Adrian Balint's CB
/// values over the average clause size.
fn fit_cb_value(size: f64) -> f64 {
    const CB: [[f64; 2]; 6] = [
        [0.0, 2.00],
        [3.0, 2.50],
        [4.0, 2.85],
        [5.0, 3.70],
        [6.0, 5.10],
        [7.0, 7.40],
    ];
    if size <= CB[0][0] {
        return CB[0][1];
    }
    if size >= CB[CB.len() - 1][0] {
        return CB[CB.len() - 1][1];
    }
    for w in CB.windows(2) {
        let (x1, y1) = (w[0][0], w[0][1]);
        let (x2, y2) = (w[1][0], w[1][1]);
        if size >= x1 && size <= x2 {
            return (y2 - y1) / (x2 - x1) * (size - x1) + y1;
        }
    }
    CB[CB.len() - 1][1]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fit_cb_value_matches_table() {
        assert!((fit_cb_value(0.0) - 2.0).abs() < 1e-12);
        assert!((fit_cb_value(3.0) - 2.5).abs() < 1e-12);
        assert!((fit_cb_value(7.0) - 7.4).abs() < 1e-12);
        assert!((fit_cb_value(100.0) - 7.4).abs() < 1e-12);
        // Midpoint between 4 and 5 interpolates between 2.85 and 3.70.
        assert!((fit_cb_value(4.5) - (2.85 + 3.70) / 2.0).abs() < 1e-12);
        // Monotone over the whole range.
        let mut prev = 0.0;
        let mut size = 0.0;
        while size <= 8.0 {
            assert!(fit_cb_value(size) >= prev);
            prev = fit_cb_value(size);
            size += 0.25;
        }
    }
}
