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
    pub(super) fn warmup(&mut self) {
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
    pub(super) fn walk_round(&mut self, limit: u64) {
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
        // clauses; units are level-0 facts already in `fixed`.
        // `slots` dense-indexes the participants; `true_count` counts true
        // literals per clause so flip updates are O(occurrences). Literal
        // lists are copied into `slots` (the clause database stays borrowed
        // only during collection, and the flip loop needs `&mut self` for the
        // RNG) – the same order of work cadical pays rebuilding its walk
        // watches each round.
        // **Fixed-false literal stripping** (`OXIZ_WALK_STRIP_FIXED=1`,
        // default OFF): cadical runs `garbage_collection()` before every
        // walk with new fixed variables, flushing fixed literals out of all
        // clauses globally, so its walk optimizes the FULL residual clause
        // set and a zero-broken completion is a true residual model. Our
        // default keeps the historical exclusion of fixed-literal clauses:
        // the stripping port (walk-objective parity) measured chaos-shaped
        // on multi-seed – summle53/summle11 wins at half the seeds, deep
        // regressions at the others (Timetable seed-0 32.8 k conflicts →
        // timeout) – the same single-policy-port failure mode the four
        // 2026-08 cadical ports hit. The knob keeps the study reproducible.
        let strip_fixed = crate::walk_strip_fixed_enabled();
        // Packed objective (CSR): slot literals and occurrence lists live in
        // two flat buffers with cumulative end offsets. The previous
        // `Vec<Vec<_>>` shapes paid one heap `Vec` per clause (~40 B of
        // header + block overhead each) and one per literal — on
        // clause-dense instances (worker-class, 10M originals) that was
        // ~500 MB of *transient* allocation per walk round and the entire
        // search-time RSS climb (measured: peak 1387 MB base vs 814 MB with
        // the walk off; see the standing-gap study's memory map). Packing
        // preserves contents and per-literal order exactly — the flip loop
        // reads identical data in identical order, so the trajectory is
        // untouched (54-file identity gate applies verbatim).
        let mut occ_end: Vec<u32> = vec![0; self.num_vars * 2];
        let mut slot_buf: Vec<Lit> = Vec::new();
        let mut slot_end: Vec<u32> = Vec::new();
        let mut true_count: Vec<u32> = Vec::new();
        let mut lit_sum = 0u64;
        let mut stripped: SmallVec<[Lit; 8]> = SmallVec::new();
        for id in self.clauses.iter_ids() {
            let Some(clause) = self.clauses.get(id) else {
                continue;
            };
            if clause.learned || clause.lits.len() < 2 {
                continue;
            }
            // Permanently satisfied by a fixed true literal: out of the
            // objective entirely.
            if clause.lits.iter().any(|&l| {
                let vi = l.var().index();
                vi < self.num_vars && fixed[vi] && values[vi] == l.is_pos()
            }) {
                continue;
            }
            // Fixed-literal clauses: with `OXIZ_WALK_STRIP_FIXED`, their
            // fixed-false literals are constant and the clause's
            // satisfiability rides on the remaining (flippable) literals
            // alone; by default the whole clause stays out of the objective
            // (flipping can never repair its fixed-false literals).
            // (The explicit borrow sidesteps SmallVec's `Deref` coercion –
            // every alternate spelling trips a different clippy lint here.)
            #[allow(clippy::needless_borrow)]
            let full: &[Lit] = &clause.lits;
            stripped.clear();
            let mut has_fixed = false;
            if strip_fixed {
                for &l in full.iter() {
                    if fixed[l.var().index()] {
                        has_fixed = true;
                    } else {
                        stripped.push(l);
                    }
                }
            } else if full.iter().any(|&l| fixed[l.var().index()]) {
                continue;
            }
            let lits: &[Lit] = if has_fixed {
                if stripped.is_empty() {
                    // Every literal fixed-false: falsified at level 0 – the
                    // solver is UNSAT and will say so on the next propagate;
                    // a permanently-broken slot would wedge the picker.
                    continue;
                }
                &stripped
            } else {
                full
            };
            let n_true = lits
                .iter()
                .filter(|&&l| values[l.var().index()] == l.is_pos())
                .count() as u32;
            slot_buf.extend_from_slice(lits);
            slot_end.push(slot_buf.len() as u32);
            true_count.push(n_true);
            lit_sum = lit_sum.saturating_add(lits.len() as u64);
        }
        let slot_count = slot_end.len();
        if slot_count == 0 {
            return;
        }
        // CSR occurrence build: count per literal (the slot scan above is a
        // single pass; counts come from the packed slots), prefix into ends,
        // then fill one flat buffer preserving clause-visit order per
        // literal exactly as the per-literal `push`es did.
        for i in 0..slot_count {
            let start = if i == 0 { 0 } else { slot_end[i - 1] as usize };
            for &l in &slot_buf[start..slot_end[i] as usize] {
                occ_end[l.code() as usize] += 1;
            }
        }
        let mut occ_buf: Vec<u32> = {
            let mut acc = 0u32;
            for e in occ_end.iter_mut() {
                acc += *e;
                *e = acc;
            }
            vec![0; acc as usize]
        };
        {
            let mut cursor: Vec<u32> = {
                let mut c = Vec::with_capacity(occ_end.len());
                let mut prev = 0u32;
                for &e in occ_end.iter() {
                    c.push(prev);
                    prev = e;
                }
                c
            };
            for slot in 0..slot_count {
                let start = if slot == 0 {
                    0
                } else {
                    slot_end[slot - 1] as usize
                };
                for &l in &slot_buf[start..slot_end[slot] as usize] {
                    let code = l.code() as usize;
                    occ_buf[cursor[code] as usize] = slot as u32;
                    cursor[code] += 1;
                }
            }
        }
        // Occurrence slice of `lit` (identical contents and order to the
        // previous per-literal Vec).
        let occ_of = |lit: Lit| -> &[u32] {
            let code = lit.code() as usize;
            let start = if code == 0 {
                0
            } else {
                occ_end[code - 1] as usize
            };
            &occ_buf[start..occ_end[code] as usize]
        };
        // Slot literal slice.
        let slot_of = |slot: u32| -> &[Lit] {
            let i = slot as usize;
            let start = if i == 0 { 0 } else { slot_end[i - 1] as usize };
            &slot_buf[start..slot_end[i] as usize]
        };

        // Broken clauses (true_count == 0), in_broken for O(1) lazy removal.
        let mut broken: Vec<u32> = Vec::new();
        let mut in_broken = vec![false; slot_count];
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
        let average_size = lit_sum as f64 / slot_count as f64;
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
            let clause_lits: &[Lit] = slot_of(picked);

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
                for &slot in occ_of(lit.negate()) {
                    if true_count[slot as usize] == 1 {
                        brk += 1;
                    }
                }
                ticks = ticks.saturating_add(occ_of(lit.negate()).len() as u64);
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
            for &slot in occ_of(t) {
                let n = &mut true_count[slot as usize];
                *n = n.saturating_sub(1);
                if *n == 0 && !in_broken[slot as usize] {
                    in_broken[slot as usize] = true;
                    broken.push(slot);
                    broken_count += 1;
                }
            }
            for &slot in occ_of(t.negate()) {
                let n = &mut true_count[slot as usize];
                *n += 1;
                if *n == 1 && in_broken[slot as usize] {
                    in_broken[slot as usize] = false; // satisfied now
                    broken_count -= 1;
                }
            }
            ticks = ticks.saturating_add(occ_of(t).len() as u64);
            ticks = ticks.saturating_add(occ_of(t.negate()).len() as u64);

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

        // Monotone best-across-walks: an earlier 0 must never be
        // overwritten by a later walk's worse minimum. The previous
        // `== 0 ||` disjunct re-assigned on *every* later walk, hiding
        // completions that had actually happened (found while studying the
        // zero-broken shadowing below – see
        // `docs/studies/2026-08-30-analyze-quadratics.md`).
        if minimum < self.stats.walk.minimum {
            self.stats.walk.minimum = minimum;
        }
        // OXIZ_PREWALK diagnostics: the pre-search phase-initialisation
        // knob needs its transfer signal visible (broken-count of the best
        // assignment; 0 = the walk found a model).
        #[cfg(feature = "std")]
        if std::env::var("OXIZ_PREWALK").is_ok() {
            eprintln!("prewalk: best_broken={minimum} vars={}", self.num_vars);
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
