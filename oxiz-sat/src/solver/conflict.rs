//! Conflict analysis, clause minimization, and assumption handling

use super::*;
use smallvec::SmallVec;

/// Compute LBD (Literals per Block Distance / "glue" score) from a set of clause literals.
///
/// LBD = number of distinct decision levels among the literals, excluding level 0.
/// Level-0 literals are excluded because they are consequences of unit propagation at the
/// root level and are always true – they do not contribute to the "block distance" that
/// measures how spread across the search tree a learned clause is.
///
/// This is an O(n) computation with no heap allocation in the common case
/// (`SmallVec<[u32; 32]>` avoids a heap allocation for clauses up to 32 distinct decision
/// levels, which covers the overwhelming majority of real CDCL learned clauses).
///
/// This is the standard Glucose/MiniSat LBD definition applied to the **actual learned
/// (1-UIP) clause literals**, so the value it returns satisfies `lbd <= literals.len()`.
/// It is a pure function (no shared scratch state) so it can be called at sites where a
/// `&mut self` borrow of the solver is unavailable – in particular after `self.learnt`
/// has been finalized but while `&self.trail` is borrowed to fire the external hook.
/// Compute LBD (Literal Block Distance) of a clause: the number of distinct
/// decision levels (excluding level 0) among its literals.
///
/// Slow reference form (linear scan with a `contains` over a SmallVec,
/// O(n·levels)): used by the unit tests below and as the semantics oracle
/// for the stamped hot-path variant [`Solver::compute_learnt_lbd_stamped`].
/// Stamped O(n) LBD over `literals`, excluding level 0 – the exact
/// semantics of [`compute_lbd_from_literals`] without the O(n·levels)
/// `contains` scan. `mark` is a generation counter owned by the caller
/// (shared with [`Solver::compute_lbd`]'s `lbd_mark`); `level_marks` grows on
/// demand so a literal at decision level == num_vars is *counted*, not
/// silently skipped – the reference function has no bound and neither does
/// this one.
fn compute_lbd_stamped(
    level_marks: &mut Vec<u32>,
    mark: &mut u32,
    literals: &[Lit],
    trail: &Trail,
) -> u32 {
    *mark = mark.wrapping_add(1);
    if *mark == 0 {
        // Wrapped onto the sentinel value virgin slots carry (`0`): a fresh
        // generation 0 would collide with every never-touched slot and
        // undercount. Reset the table once (O(num_levels), once per 2^32
        // analyses) and restart the generation sequence at 1.
        level_marks.fill(0);
        *mark = 1;
    }
    let m = *mark;
    let mut count = 0u32;
    for &lit in literals.iter() {
        let level = trail.level(lit.var());
        if level == 0 {
            continue;
        }
        let lv = level as usize;
        if lv >= level_marks.len() {
            level_marks.resize(lv + 1, 0);
        }
        if level_marks[lv] != m {
            level_marks[lv] = m;
            count += 1;
        }
    }
    count
}

#[cfg(test)]
fn compute_lbd_from_literals(literals: &[Lit], trail: &Trail) -> u32 {
    let mut levels: SmallVec<[u32; 32]> = SmallVec::new();
    for &lit in literals {
        let level = trail.level(lit.var());
        if level > 0 && !levels.contains(&level) {
            levels.push(level);
        }
    }
    levels.len() as u32
}

/// Stable insertion sort by `u64` key on pre-extracted `(key, item)` pairs.
///
/// Output is element-for-element identical to `[T]::sort_by_key` (both are
/// stable: equal keys keep their original relative order), so swapping this in
/// cannot change the search trajectory. Used for the per-conflict VMTF bump
/// sort, whose arrays are usually tiny (typically ≤ 40 analyzed variables)
/// where the generic driftsort machinery costs more than the quadratic move
/// count of a plain insertion sweep; keys are read once (decorated) so the
/// sweep does O(n) score lookups instead of O(n²).
///
/// Only used up to [`BUMP_SORT_INSERTION_LIMIT`] elements. Above that the
/// sweep degenerates exactly where CDCL hurts for it: instances whose
/// conflicts resolve through giant clauses (the worker-scheduling class
/// resolves ~1900 analyzed literals per conflict) burn millions of
/// instructions per conflict in the element-shifting loop. Above the limit
/// the caller uses the stable O(n log n) `sort_by_key` instead – identical
/// output either way, mirroring cadical's `MSORT` (std::sort below its
/// `radixsortlim`, default 800; radix sort above).
pub(super) const BUMP_SORT_INSERTION_LIMIT: usize = 64;

fn insertion_sort_by_key_stable<K: Copy + PartialOrd, T: Copy>(v: &mut [(K, T)]) {
    for i in 1..v.len() {
        let cur = v[i];
        let k = cur.0;
        let mut j = i;
        while j > 0 && v[j - 1].0 > k {
            v[j] = v[j - 1];
            j -= 1;
        }
        v[j] = cur;
    }
}

/// Split-borrow bundle for the 1-UIP reason-literal marking step.
///
/// `analyze`'s reason walk must iterate a reason clause's literals *in the
/// arena* while mutating the analysis tables. The previous shape copied
/// every reason clause into a heap-allocating SmallVec per resolution step
/// ("snapshot the literals so the shared marking helper may take `&mut
/// self`") – linear, but one allocation plus a full literal copy per
/// non-inline reason, which dominates on instances whose conflicts resolve
/// through giant clauses (worker-scheduling class: ~1900-literal reasons).
/// Bundling exactly the tables the marker touches lets the walk hold the
/// immutable arena borrow across the whole loop.
///
/// The LRAT level-0 branch cannot resolve `proof_unit_id` from inside the
/// split borrow, so it records the dimacs literal in `lrat_units` for the
/// caller to flush **immediately after the marking loop** – nothing else
/// appends to `unit_chain` inside the loop, so the pushed sequence is
/// identical to the eager form.
struct AnalysisMark<'a> {
    seen: &'a mut [bool],
    trail: &'a Trail,
    learnt: &'a mut SmallVec<[Lit; 32]>,
    seen_levels: &'a mut Vec<u32>,
    seen_level_count: &'a mut [u32],
    seen_level_trail: &'a mut [u32],
    lrat: bool,
    lrat_units: &'a mut SmallVec<[i32; 4]>,
}

impl AnalysisMark<'_> {
    /// Record that `var` at decision level `level` (both > 0) was marked
    /// `seen` during the current analysis, maintaining the per-level
    /// statistics clause minimization depends on. Faithful port of the tail
    /// of cadical's `analyze_literal` (same body as
    /// [`Solver::note_seen_level`], on the split-borrowed tables).
    fn note_seen_level(&mut self, var: Var, level: u32) {
        let lv = level as usize;
        if lv >= self.seen_level_count.len() {
            return;
        }
        if self.seen_level_count[lv] == 0 {
            self.seen_levels.push(level);
        }
        self.seen_level_count[lv] += 1;
        let ti = self.trail.trail_index(var);
        if ti < self.seen_level_trail[lv] {
            self.seen_level_trail[lv] = ti;
        }
    }

    /// Mark one reason-clause literal (same body as the removed
    /// `Solver::analyze_mark_antecedent`, on the split-borrowed tables).
    fn mark_antecedent(
        &mut self,
        lit: Lit,
        current_level: u32,
        counter: &mut i32,
        vars_to_bump: &mut SmallVec<[Var; 32]>,
    ) {
        let var = lit.var();
        let level = self.trail.level(var);

        if !self.seen[var.index()] && level > 0 {
            self.seen[var.index()] = true;
            vars_to_bump.push(var);
            self.note_seen_level(var, level);
            if level == current_level {
                *counter += 1;
            } else {
                // The conflict clause has all literals FALSE; keeping the
                // literal as-is means the learned clause demands it TRUE.
                self.learnt.push(lit);
            }
        } else if self.lrat && level == 0 && !self.seen[var.index()] {
            // LRAT: a level-0 (fixed) antecedent. With the level-0 flush
            // every level-0 literal is a unit with an id, so reference it
            // directly (cadical's `analyze_literal` level-0 branch). `lit`
            // is FALSE; its true form `¬lit` is the unit.
            self.seen[var.index()] = true;
            self.lrat_units.push(lit.negate().to_dimacs());
        }
    }
}

/// Outcome of one block-walk step (cadical `shrink_literal` return codes).
#[derive(Clone, Copy, PartialEq, Eq)]
enum ShrinkStep {
    /// A lower-level antecedent is not removable: abort the block walk.
    Fail,
    /// Already accounted for (level-0, shrinkable, or removable).
    Skip,
    /// Newly marked shrinkable at the block's level.
    NewlyShrinkable,
}

/// Consecutive missed trail positions after which the block scan consults
/// the chunk summary (see `shrink_block`): dense blocks stay under it and
/// keep the original pure-scan cost, sparse stretches start jumping 64
/// positions per summary read.  Any small value behaves equivalently
/// (the pop sequence is unchanged for all of them); 8 keeps dense-class
/// blocks (measured 2–7 misses per pop) on the fast path.
const SHRINK_SUMMARY_AFTER: u32 = 8;

/// One analyze's block-walk statistics (debug instrumentation).
#[derive(Default, Clone, Copy)]
struct ShrinkTraceDbg {
    learnt_len: usize,
    singleton_blocks: u64,
    multi_blocks: u64,
    multi_block_lits: u64,
    walk_success: u64,
    walk_fail: u64,
    fallback_saved: u64,
}

impl Solver {
    /// Analyze conflict and learn clause
    /// Mark one antecedent literal during 1-UIP resolution in [`Self::analyze`].
    ///
    /// Unseen above-level-0 literals are marked seen, queued for activity
    /// bumping, and either counted (conflict level) or appended to the learned
    /// clause (lower level). Level-0 literals are recorded as LRAT unit
    /// antecedents instead. Shared by the stored-clause path and the lazy
    /// theory-explanation path so both resolve with identical semantics.
    #[inline]
    /// Stamped hot-path LBD over `self.learnt`, excluding level 0 – the exact
    /// semantics of [`compute_lbd_from_literals`] at O(n) instead of
    /// O(n·levels). See [`compute_lbd_stamped`] for the equivalence argument;
    /// the property test below pins the two implementations together.
    fn compute_learnt_lbd_stamped(&mut self) -> u32 {
        let Self {
            level_marks,
            lbd_mark,
            learnt,
            trail,
            ..
        } = self;
        compute_lbd_stamped(level_marks, lbd_mark, learnt, trail)
    }

    /// Record that `var` at decision level `level` (both > 0) was marked
    /// `seen` during the current analysis, maintaining the per-level
    /// statistics clause minimization depends on. Faithful port of the tail
    /// of cadical's `analyze_literal`:
    /// ```text
    /// Level &l = control[v.level];
    /// if (!l.seen.count++) levels.push_back (v.level);
    /// if (v.trail < l.seen.trail) l.seen.trail = v.trail;
    /// ```
    /// Guarded on the table size exactly like `compute_lbd`'s level marks:
    /// decision levels are bounded by `num_vars`, and a caller above
    /// `new_var` bookkeeping must degrade to "no statistics" (which only
    /// makes minimization keep more literals) rather than panic.
    #[inline]
    fn note_seen_level(&mut self, var: Var, level: u32) {
        let lv = level as usize;
        if lv >= self.seen_level_count.len() {
            return;
        }
        if self.seen_level_count[lv] == 0 {
            self.seen_levels.push(level);
        }
        self.seen_level_count[lv] += 1;
        let ti = self.trail.trail_index(var);
        if ti < self.seen_level_trail[lv] {
            self.seen_level_trail[lv] = ti;
        }
    }

    /// Reset the per-level `seen` statistics after an analysis finished
    /// (cadical `clear_analyzed_levels`: `control[l].reset()` sets
    /// `seen.count = 0`, `seen.trail = INT_MAX`). Must run *after*
    /// minimization, which is the only consumer of the statistics.
    fn clear_analyzed_levels(&mut self) {
        for &l in &self.seen_levels {
            let lv = l as usize;
            if lv < self.seen_level_count.len() {
                self.seen_level_count[lv] = 0;
                self.seen_level_trail[lv] = u32::MAX;
            }
        }
        self.seen_levels.clear();
    }

    /// Walk the trail backwards for the most recent still-unresolved (`seen`)
    /// literal at `current_level` – the next 1-UIP pivot. Returns `None` when
    /// the trail is exhausted (degenerate conflict state). Shared by
    /// [`Self::analyze`]'s clause and lazy-theory paths.
    ///
    /// Static + immutable on purpose: it borrows neither the clause database
    /// nor any mutable solver state, so callers may invoke it between `&mut
    /// self` steps of the resolution loop.
    fn analyze_scan_pivot(
        seen: &[bool],
        trail: &Trail,
        index: &mut usize,
        current_level: u32,
    ) -> Option<Lit> {
        loop {
            if *index == 0 {
                // Trail exhausted: no unresolved conflict-level literal left
                // (degenerate theory-conflict state). Mirrors the original
                // inline walk's underflow guard.
                return None;
            }
            *index -= 1;
            let lit = trail.assignments()[*index];
            let var = lit.var();
            if seen[var.index()] && trail.level(var) == current_level {
                return Some(lit);
            }
        }
    }

    pub(super) fn analyze(&mut self, conflict: ClauseId) -> (u32, SmallVec<[Lit; 32]>) {
        // Debug: print conflict info (only with analyze-debug feature)
        #[cfg(feature = "analyze-debug")]
        if self.num_vars <= 5 {
            eprintln!("[ANALYZE] Conflict clause id={:?}", conflict);
            if let Some(c) = self.clauses.get(conflict) {
                let lits_str: Vec<String> = c
                    .lits
                    .iter()
                    .map(|lit| {
                        let val = self.trail.lit_value(*lit);
                        let level = self.trail.level(lit.var());
                        let sign = if lit.is_pos() { "" } else { "~" };
                        format!("{}v{}@{}={:?}", sign, lit.var().index(), level, val)
                    })
                    .collect();
                eprintln!("[ANALYZE] Conflict clause: ({})", lits_str.join(" | "));
            }
            eprintln!("[ANALYZE] Trail:");
            for &lit in self.trail.assignments() {
                let var = lit.var();
                let level = self.trail.level(var);
                let reason = self.trail.reason(var);
                let sign = if lit.is_pos() { "" } else { "~" };
                eprintln!("  {}v{}@{} reason={:?}", sign, var.index(), level, reason);
            }
        }

        self.learnt.clear();
        self.learnt.push(Lit::from_code(0)); // Placeholder for asserting literal

        let mut counter = 0;
        let mut p = None;
        let mut index = self.trail.assignments().len();

        // The "conflict level" is the highest decision level among the conflict
        // clause's literals. In textbook CDCL this always equals
        // `trail.decision_level()`, because propagation is run to completion at
        // every level before a new decision is taken. However, clauses added
        // *on the fly* – theory reason/lemma clauses in CDCL(T), or clauses
        // encountered after chronological backtracking – can be falsified at a
        // level strictly BELOW the current decision level. Running 1-UIP
        // resolution relative to `decision_level()` in that situation is
        // unsound for backtracking: the conflict clause contributes NO literal
        // at the pivot level, so the current-level counter starts at 0, the
        // trail walk underflows it, and the asserting literal ends up at a level
        // <= the computed backtrack level. Backtracking then fails to unassign
        // that variable and `learn_clause` re-assigns it in place – corrupting
        // the trail (observed as a wrong top-level UNSAT on disjunctive LIA).
        // Anchoring the analysis at the genuine conflict level restores the
        // 1-UIP invariant (asserting literal strictly above the backtrack
        // level) for both the normal and the on-the-fly-clause cases.
        let current_level = {
            let mut lvl = 0;
            if let Some(c) = self.clauses.get(conflict) {
                for &lit in c.lits {
                    let l = self.trail.level(lit.var());
                    if l > lvl {
                        lvl = l;
                    }
                }
            }
            lvl
        };

        // A conflict whose genuine level is 0 has EVERY literal falsified under
        // unconditional (level-0) assignments – a root-level refutation, so the
        // instance is UNSAT. This can happen above decision level 0 when an
        // on-the-fly clause (a theory reason/lemma clause) is added already
        // fully falsified at the root: the watched-literal scheme only visits it
        // on the next propagation, which may run at a higher decision level.
        // There is no asserting literal to learn, so we return an empty clause
        // (backtrack level 0) – the caller treats an empty learned clause as
        // fundamental UNSAT, exactly as `analyze_theory_conflict` already does.
        // Fabricating a 1-UIP clause here instead would resolve the trail's
        // bottom literal into a spurious unit clause that contradicts a
        // level-0 fact, corrupting the trail (the earlier `decision_level()`
        // fallback did precisely this, tripping the trail-consistency assert).
        if current_level == 0 {
            // Root-level refutation: every conflict literal is falsified under
            // unconditional (level-0) facts, so the empty clause is derivable.
            // The LRAT chain is built later by [`Self::build_chain_for_empty`]
            // (a trail-order reason walk mirroring this function), invoked from
            // the UNSAT emission site. Leave `lrat_chain` empty here so that
            // path runs.
            self.learnt.clear();
            return (0, SmallVec::new());
        }
        // Record the genuine conflict level for the minimizer (cadical reads
        // its `level` member, which always equals the conflict level; here the
        // two can differ under chronological backtracking, and minimizing
        // through a conflict-level literal over-strengthens the clause).
        self.current_conflict_level = current_level;

        // Reset seen flags
        for s in &mut self.seen {
            *s = false;
        }

        // Collect variables to bump in batch (avoids repeated heap sift-ups)
        let mut vars_to_bump: SmallVec<[Var; 32]> = SmallVec::new();

        let mut reason_clause = conflict;

        'resolve: while let Some(clause) = self.clauses.get(reason_clause) {
            // Process reason clause (must exist, as it's either conflict or a propagation reason)
            let is_learned = clause.learned;

            // LRAT: this reason clause is an antecedent in the 1-UIP resolution
            // chain. Record its id in walk order (conflict-first); the chain is
            // reversed into checker order at the end of `analyze` (mirrors
            // `analyze_reason`'s `lrat_chain.push_back(reason->id)`).
            if self.lrat {
                self.lrat_chain.push(self.proof_clause_id(reason_clause));
            }

            // Record clause usage for tier promotion and bump activity (if it's a learned clause)
            if is_learned && self.clauses.get(reason_clause).is_some() {
                self.clauses.record_usage(reason_clause);
                // cadical `bump_clause`: restamp the used counter to max_used
                // on every analysis use (the reduce port's recency signal).
                if crate::cadical_reduce_enabled() || crate::cadical_reduce_null_enabled() {
                    let slot = reason_clause.index();
                    if slot >= self.cadical_used.len() {
                        self.cadical_used.resize(slot + 1, 0);
                    }
                    self.cadical_used[slot] = 31;
                }
                // Promote to Core if LBD ≤ 2 (GLUE clause)
                if self.clauses.get(reason_clause).is_some_and(|c| c.lbd <= 2) {
                    self.clauses.promote_to_core(reason_clause);
                }
                // Bump clause activity (MapleSAT-style). The increment
                // schedule stays f64 (precision of the growth/decay cycle);
                // the accumulated activity itself is f32 in the arena.
                self.clauses
                    .bump_activity(reason_clause, self.clause_bump_increment as f32);
            }

            let Some(clause) = self.clauses.get(reason_clause) else {
                break;
            };
            // Iterate the reason clause's literals IN THE ARENA (no snapshot
            // copy): the marking tables are split-borrowed through
            // [`AnalysisMark`], so the immutable clause-arena borrow lives
            // across the whole loop. Each reason used to pay one heap
            // allocation plus a full literal copy here (`SmallVec<[Lit; 8]>`
            // collect), which dominated on giant-clause instances.
            {
                let Solver {
                    seen,
                    trail,
                    learnt,
                    seen_levels,
                    seen_level_count,
                    seen_level_trail,
                    lrat,
                    ..
                } = self;
                let mut lrat_units: SmallVec<[i32; 4]> = SmallVec::new();
                {
                    let mut mark = AnalysisMark {
                        seen: &mut seen[..],
                        trail,
                        learnt,
                        seen_levels,
                        seen_level_count: &mut seen_level_count[..],
                        seen_level_trail: &mut seen_level_trail[..],
                        lrat: *lrat,
                        lrat_units: &mut lrat_units,
                    };
                    for &lit in clause.lits.iter() {
                        // When resolving a *reason* clause (`p` is Some), the
                        // propagated literal `p` is the one being resolved
                        // out: it is TRUE on the trail and must NOT be added
                        // to the learned clause. We skip it BY VALUE rather
                        // than by a fixed index, because
                        // binary-implication-graph propagation (propagate.rs)
                        // records the reason without moving the implied
                        // literal to index 0 – so the propagated literal may
                        // sit at index 1. Skipping index 0 positionally would
                        // drop the false antecedent at index 0, producing
                        // over-strong (unsound) learned clauses. For the
                        // initial conflict clause `p` is None, so every
                        // literal is processed.
                        if p == Some(lit) {
                            continue;
                        }
                        mark.mark_antecedent(lit, current_level, &mut counter, &mut vars_to_bump);
                    }
                }
                // LRAT level-0 units, flushed in walk order the moment the
                // arena borrow ends (nothing inside the loop could have
                // appended to `unit_chain`, so the sequence is identical to
                // the eager form).
                for dimacs in lrat_units {
                    self.unit_chain.push(self.proof_unit_id(dimacs));
                }
            }

            // Find next literal to resolve on: the most recently assigned
            // still-unresolved literal AT THE CONFLICT LEVEL.
            //
            // The level check (inside `analyze_scan_pivot`) is what makes this
            // walk correct under chronological backtracking. The trail is no
            // longer sorted by decision level – a literal implied at a low
            // level can sit near the top of the trail – so "the last `seen`
            // literal" is not necessarily a conflict-level literal any more.
            // Resolving on a lower-level one would decrement the conflict-level
            // counter for a literal that was never counted in it, terminating
            // the 1-UIP loop early and emitting a clause that is missing
            // literals, i.e. stronger than what resolution actually derives.
            // Reference: Z3's `sat_solver.cpp`, whose 1-UIP loop skips marked
            // literals with `lvl(c_var) != m_conflict_lvl` for the same reason.
            let Some(next_lit) =
                Self::analyze_scan_pivot(&self.seen, &self.trail, &mut index, current_level)
            else {
                break 'resolve;
            };
            p = Some(next_lit);

            counter -= 1;
            if counter == 0 {
                break 'resolve;
            }

            // Dispatch on the pivot's reason. A stored clause re-enters the
            // outer loop. A **lazily explained** theory propagation is
            // resolved through inline: its stored tail is exactly what a
            // materialized reason clause would have carried after its head
            // (the head itself – the pivot, TRUE on the trail – is resolved
            // out and, unlike the clause path, needs no by-value skip because
            // the tail never contains it). Several consecutive theory
            // antecedents can chain before the next clause (or the UIP).
            let mut pivot = next_lit.var();
            loop {
                match self.trail.reason(pivot) {
                    Reason::Propagation(c) => {
                        reason_clause = c;
                        break;
                    }
                    Reason::Theory => {
                        let Some(tail) = self.theory_reason_tail(pivot).cloned() else {
                            // No lazy explanation available (proof connected
                            // mid-search, or a stale entry): treat like a
                            // decision and stop resolving, mirroring `_ =>`.
                            break 'resolve;
                        };
                        {
                            let Solver {
                                seen,
                                trail,
                                learnt,
                                seen_levels,
                                seen_level_count,
                                seen_level_trail,
                                lrat,
                                ..
                            } = self;
                            let mut lrat_units: SmallVec<[i32; 4]> = SmallVec::new();
                            {
                                let mut mark = AnalysisMark {
                                    seen: &mut seen[..],
                                    trail,
                                    learnt,
                                    seen_levels,
                                    seen_level_count: &mut seen_level_count[..],
                                    seen_level_trail: &mut seen_level_trail[..],
                                    lrat: *lrat,
                                    lrat_units: &mut lrat_units,
                                };
                                for &lit in &tail {
                                    mark.mark_antecedent(
                                        lit,
                                        current_level,
                                        &mut counter,
                                        &mut vars_to_bump,
                                    );
                                }
                            }
                            for dimacs in lrat_units {
                                self.unit_chain.push(self.proof_unit_id(dimacs));
                            }
                        }
                        let Some(next) = Self::analyze_scan_pivot(
                            &self.seen,
                            &self.trail,
                            &mut index,
                            current_level,
                        ) else {
                            break 'resolve;
                        };
                        p = Some(next);
                        counter -= 1;
                        if counter == 0 {
                            break 'resolve;
                        }
                        pivot = next.var();
                    }
                    _ => break 'resolve,
                }
            }
        }

        // Set asserting literal (p is guaranteed to be Some at this point)
        if let Some(lit) = p {
            self.learnt[0] = lit.negate();
        }

        // Repair an early exit from the resolution loop.
        //
        // The loop above stops as soon as it reaches a literal with no clausal
        // reason (a decision, or a theory propagation whose explanation is not a
        // clause in the database). If `counter` has not reached 0 by then, some
        // conflict-level literals were counted but never resolved away, and they
        // are simply missing from `self.learnt` – an over-strong clause, which is
        // unsound: it can drive the solver to a bogus root-level unit and hence
        // to a false `unsat`. Every such literal is still `seen`, and its
        // contribution to the resolvent is the negation of its trail assignment
        // (the resolvent's literals are all false), so adding those recovers a
        // clause that resolution genuinely derives.
        if counter > 0 {
            let uip_var = p.map(|lit| lit.var());
            for &lit in self.trail.assignments() {
                let var = lit.var();
                if self.seen[var.index()]
                    && self.trail.level(var) == current_level
                    && Some(var) != uip_var
                {
                    // Stays `seen`: that flag is how minimization recognises the
                    // literals that are in the learned clause.
                    self.learnt.push(lit.negate());
                }
            }
        }

        // Improve the learned clause (block-UIP shrinking by default, plain
        // recursive minimization as fallback / under LRAT) BEFORE bumping:
        // shrinking adds each block-UIP variable to the bump set, exactly
        // where cadical adds it to `analyzed` ahead of `bump_variables`.
        self.improve_learnt_clause(&mut vars_to_bump);

        // Which decision structure receives the analysis signal this conflict?
        //
        // cadical `analyze.cpp::bump_variable`: `if (use_scores ())
        // bump_variable_score (lit) else bump_queue (lit)` with
        // `use_scores () = opts.score && stable`. With VMTF owning focused
        // mode (`focused_vmtf`, the CaDiCaL-preset default), the faithful
        // routing is: stable → scores only, focused → queue only. The
        // historical oxiz behavior – both structures bumped on every conflict
        // – remains the default (unset env); the treatment/null switches for
        // the study live in `lib.rs`.
        //
        // Configs where VSIDS owns both modes (`focused_vmtf = false`, or no
        // VMTF at all) keep unconditional score bumps: there is no inactive
        // structure to gate.
        let scores_active = !self.config.use_vmtf || !self.config.focused_vmtf || self.stable;
        let gate = crate::bump_mode_gate_enabled() || crate::bump_mode_gate_null_enabled();

        if scores_active || !gate {
            if gate && crate::bump_mode_gate_null_enabled() && self.config.use_vmtf {
                // NULL ARM: same bump count, same heap work, scrambled signal –
                // each analyzed slot is replaced by a pseudo-random variable
                // before it reaches the score heap. Deterministic per seed.
                let mut scrambled: SmallVec<[Var; 32]> =
                    SmallVec::with_capacity(vars_to_bump.len());
                for _ in 0..vars_to_bump.len() {
                    let r = self.rand_u64();
                    let idx = (r % (self.num_vars.max(1) as u64)) as u32;
                    scrambled.push(Var::new(idx));
                }
                self.vsids.bump_batch(&scrambled);
            } else {
                // Batch bump all collected variables at once (single heap rebuild)
                self.vsids.bump_batch(&vars_to_bump);
            }
        }
        // CHB's `bump_batch` performs an O(num_vars) heap rebuild and LRB's
        // `on_conflict` does a periodic O(num_vars) participation scan. Both
        // are pure waste when the heuristic is not the active branching
        // strategy: their heaps/scores are only ever read inside the matching
        // `pick_branch_var` branch. Gating them removes a ~35% hot-spot when
        // the default (VMTF/VSIDS) heuristic is in use.
        if self.config.use_chb_branching {
            self.chb.bump_batch(&vars_to_bump);
        }
        if self.config.use_lrb_branching {
            self.lrb.on_reason_batch(&vars_to_bump);
        }
        // VMTF move-to-front: bump conflict-involved variables (cadical sorts
        // them by bump-order first to preserve relative order; the bump is
        // idempotent for vars already at the tail). Sort `vars_to_bump` in
        // place – its only later use (external-heuristic notification) is
        // order-independent – avoiding a per-conflict SmallVec clone.
        //
        // Mode-gated under the study switches (cadical bumps the queue only
        // when scores are NOT in use): in stable mode the queue stops
        // receiving analysis signal, exactly mirroring the score-side gate
        // above. Default (gates unset) keeps double maintenance.
        let vmtf_active = self.config.use_vmtf && (!gate || !scores_active);
        if vmtf_active {
            // Sort by bump timestamp (cadical MSORT on `analyzed_bumped_rank`)
            // to preserve relative queue order of bumped variables.
            //
            // Keys are read once into (key, var) pairs: an undecorated
            // insertion sweep re-evaluates the key O(n²) times (each a bounds-
            // checked btab load), which measured *slower* than the generic
            // driftsort it replaced; decorating makes it O(n) reads and keeps
            // the stable tie order intact.
            //
            // Giant-clause instances push thousands of analyzed variables
            // through here per conflict; the insertion sweep is quadratic and
            // cadical switches algorithms at 800 (`MSORT`). Both branches
            // below are stable, so the order – and therefore the whole search
            // trajectory – is identical to the pure insertion sweep.
            let mut keyed: SmallVec<[(u64, Var); 32]> = vars_to_bump
                .iter()
                .map(|&v| (self.vmtf.activity(v), v))
                .collect();
            if keyed.len() <= BUMP_SORT_INSERTION_LIMIT {
                insertion_sort_by_key_stable(&mut keyed);
            } else {
                keyed.sort_by_key(|&(k, _)| k);
            }
            for (i, &(_, v)) in keyed.iter().enumerate() {
                vars_to_bump[i] = v;
            }
            for &v in &vars_to_bump {
                self.vmtf.bump(v, |v| self.trail.is_assigned(v));
            }
        }

        // LRAT chain finalization (faithful to the tail of cadical's `analyze`):
        // append the level-0 unit ids collected during the reason walk, then
        // reverse the whole chain into the checker's forward-propagation order.
        // `minimize_clause_lrat` (when active) has already appended the
        // minimization sub-chains ahead of this.
        if self.lrat {
            // Finalize the LRAT chain: append the level-0 unit ids collected
            // during the walk, then reverse the whole chain into the checker's
            // forward-propagation order (cadical's tail of `analyze`).
            self.lrat_chain.append(&mut self.unit_chain);
            self.lrat_chain.reverse();
            self.unit_analyzed.clear();
        }

        // Compute the real LBD from the FINAL learned (1-UIP) clause literals.
        // This is the standard Glucose definition: the number of distinct decision
        // levels in the learned clause itself (level 0 excluded), not the larger
        // `vars_to_bump` set. It is computed AFTER minimization so it reflects the
        // exact clause that will be stored, and therefore satisfies lbd <= clause len.
        let lbd = self.compute_learnt_lbd_stamped();

        // Notify external heuristic of each conflict-involved variable with the
        // learned-clause LBD score.
        if let Some(ref ext) = self.config.external_branching
            && let Ok(mut h) = ext.lock()
        {
            for &var in &vars_to_bump {
                h.on_conflict_var_with_lbd(var, lbd);
            }
        }

        // Order the clause so that its two highest-level literals occupy the
        // watched positions, `learnt[0]` being the highest.
        //
        // For a textbook 1-UIP clause `learnt[0]` is already the unique
        // conflict-level literal, so this only moves the second watch into place.
        // Under chronological backtracking that is no longer guaranteed: the
        // asserting literal is assigned at its true implication level, which may
        // sit *below* another literal of the clause. Leaving such a clause
        // unordered would compute a backtrack level above `learnt[0]`'s level, so
        // backtracking would not unassign it and the learned clause would
        // re-assign an already-assigned variable, corrupting the trail. Z3 does
        // the same swap in `learn_lemma_and_backjump` ("with scope tracking and
        // chronological backtracking, consequent may not be at highest decision
        // level").
        let uip_level = self.reorder_learnt_watches();

        // Level at which the clause becomes unit (the second highest level).
        let assertion_level = if self.learnt.len() <= 1 {
            0
        } else {
            self.trail.level(self.learnt[1].var())
        };

        // Apply chronological backtracking if enabled, then cadical's
        // `chronoreusetrail` case: on a *short* jump (where the plain helper
        // backjumps to the assertion level), find the most-recently-bumped
        // variable in the to-be-discarded trail region and stop only at its
        // level, keeping the trail content above it (cadical
        // `analyze.cpp::determine_actual_backtrack_level`).  Sound on the
        // level-filtered trail: the kept out-of-order literals survive later
        // backtracks by recorded level, and `backtrack_to_with_callback`
        // re-propagates the kept region from the level boundary.
        let plain = self.chrono_backtrack.compute_backtrack_level(
            &self.trail,
            &self.learnt,
            uip_level,
            assertion_level,
        );
        let backtrack_level = if self.config.chrono_reuse
            && self.stats.conflicts >= self.config.chrono_reuse_after
            && plain == assertion_level
            && uip_level > assertion_level.saturating_add(1)
        {
            self.chrono_reuse_level(uip_level, assertion_level)
                .unwrap_or(plain)
        } else {
            plain
        };

        // Track chronological vs non-chronological backtracks
        if backtrack_level != assertion_level {
            self.stats.chrono_backtracks += 1;
        } else {
            self.stats.non_chrono_backtracks += 1;
        }

        // Debug: print learned clause (only with analyze-debug feature)
        #[cfg(feature = "analyze-debug")]
        if self.num_vars <= 5 {
            let lits_str: Vec<String> = self
                .learnt
                .iter()
                .map(|lit| {
                    let sign = if lit.is_pos() { "" } else { "~" };
                    format!("{}v{}", sign, lit.var().index())
                })
                .collect();
            eprintln!(
                "[ANALYZE] Learned clause: ({}), backtrack_level={}",
                lits_str.join(" | "),
                backtrack_level
            );
        }

        // Trail-consistency invariants (debug builds only, so no release-path
        // panic on user input). A well-formed 1-UIP learned clause has its
        // asserting literal (learnt[0]) at the conflict level and every other
        // literal strictly below the backtrack level, so backtracking is
        // guaranteed to unassign the asserting variable before `learn_clause`
        // re-asserts it. If either invariant is violated the trail would be
        // corrupted by an in-place re-assignment.
        debug_assert!(
            self.learnt.is_empty()
                || !self.trail.is_assigned(self.learnt[0].var())
                || self.trail.level(self.learnt[0].var()) > backtrack_level,
            "asserting literal must be above the backtrack level (uip level {}, backtrack {})",
            self.trail.level(self.learnt[0].var()),
            backtrack_level
        );
        debug_assert!(
            self.learnt
                .iter()
                .skip(1)
                .all(|lit| self.trail.level(lit.var()) <= backtrack_level),
            "every non-asserting literal must be at or below the backtrack level"
        );

        // Snapshot the analysis-walk glue before the level statistics are
        // cleared: `seen_levels` at this point holds exactly cadical's
        // `levels` set (every decision level that contributed a literal to
        // the resolution walk), so `len - 1` is cadical's `glue` – the
        // statistic the restart EMAs are fed with (see
        // `Solver::analysis_walk_glue`).
        self.analysis_walk_glue =
            u32::try_from(self.seen_levels.len().saturating_sub(1)).unwrap_or(u32::MAX);

        // Reset the per-level `seen` statistics now that minimization (their
        // only consumer) has run (cadical `clear_analyzed_levels`).
        self.clear_analyzed_levels();

        (backtrack_level, self.learnt.clone())
    }

    /// Move the two highest-level literals of `self.learnt` into the watched
    /// positions – `learnt[0]` highest, `learnt[1]` second highest – and return
    /// `learnt[0]`'s decision level.
    ///
    /// This is the standard "watch the two literals falsified latest" invariant.
    /// For a textbook 1-UIP clause `learnt[0]` already holds the unique
    /// conflict-level literal, so only the second watch actually moves.
    fn reorder_learnt_watches(&mut self) -> u32 {
        if self.learnt.is_empty() {
            return 0;
        }

        let mut max_idx = 0;
        let mut max_level = self.trail.level(self.learnt[0].var());
        for i in 1..self.learnt.len() {
            let level = self.trail.level(self.learnt[i].var());
            if level > max_level {
                max_level = level;
                max_idx = i;
            }
        }
        self.learnt.swap(0, max_idx);

        if self.learnt.len() > 1 {
            let mut second_idx = 1;
            let mut second_level = self.trail.level(self.learnt[1].var());
            for i in 2..self.learnt.len() {
                let level = self.trail.level(self.learnt[i].var());
                if level > second_level {
                    second_level = level;
                    second_idx = i;
                }
            }
            self.learnt.swap(1, second_idx);
        }

        max_level
    }

    /// Minimize the learned clause by removing redundant literals
    ///
    /// A literal can be removed if it is implied by the remaining literals.
    /// Build the RUP hint chain for the empty clause – faithful to cadical's
    /// `build_chain_for_empty`. With the level-0 flush every level-0 literal is
    /// a unit with an id, so the chain is simply `[unit id of each conflict
    /// literal's true form] ++ [conflict clause id]`: under the (empty) negation
    /// the units force the conflict clause's literals false, falsifying it →
    /// conflict. No-op when LRAT is off or the chain was already populated.
    pub(super) fn build_chain_for_empty(&mut self, conflict: Option<ClauseId>) {
        if !self.lrat || !self.lrat_chain.is_empty() {
            return;
        }
        let Some(cid) = conflict else {
            return;
        };
        let clits: SmallVec<[Lit; 8]> = self
            .clauses
            .get(cid)
            .map(|c| c.lits.iter().copied().collect())
            .unwrap_or_default();
        for lit in clits {
            // `lit` is falsified; its negation is the level-0 unit.
            self.lrat_chain
                .push(self.proof_unit_id(lit.negate().to_dimacs()));
        }
        self.lrat_chain.push(self.proof_clause_id(cid));
    }

    /// LRAT-path learned-clause minimization with RUP-chain extension –
    /// faithful port of cadical's `minimize_clause` / `minimize_literal` /
    /// `calculate_minimize_chain`. Drops redundant literals from the 1-UIP
    /// LRAT-path learned-clause minimization with RUP-chain extension –
    /// faithful port of cadical's `minimize_clause` / `minimize_literal` /
    /// `calculate_minimize_chain`. Drops redundant literals from the 1-UIP
    /// clause and extends [`Solver::lrat_chain`] with each removed literal's
    /// reason sub-graph so the smaller clause stays RUP-checkable. Enabled by
    /// the level-0-to-units flush ([`Self::flush_level0_unit`]).
    fn minimize_clause_lrat(&mut self) {
        let n = self.learnt.len();
        if n <= 2 {
            return;
        }
        // `learnt[0]` is the asserting literal and is always kept. Process the
        // rest in trail (assignment) order so that an earlier clause literal a
        // later one resolves through is already decided (kept→`MF_KEEP`, or
        // dropped→`MF_REMOVABLE`) before it is reached – the recursive base case
        // (cadical `minimize_sort_clause`).
        let asserting = self.learnt[0];
        let mut order: SmallVec<[Lit; 32]> = self.learnt[1..].iter().copied().collect();
        order.sort_by_key(|&l| self.trail.trail_index(l.var()));

        let mut kept: SmallVec<[Lit; 32]> = SmallVec::new();
        let mut minimize_chain: Vec<i64> = Vec::new();
        for &lit in &order {
            // `lit` is FALSE (a learnt literal); check its TRUE form's reason graph.
            if self.minimize_literal_lrat(lit.negate(), 0) {
                // Removable: drop `lit` and extend the chain with its antecedents.
                self.calculate_minimize_chain_lrat(lit.negate());
                // cadical: `minimize_chain` accumulates `mini_chain` forward.
                for &id in &self.mini_chain {
                    minimize_chain.push(id);
                }
                self.mini_chain.clear();
            } else {
                self.mf_set(lit.var(), MF_KEEP);
                kept.push(lit);
            }
        }
        // Rebuild the learnt clause: asserting literal first, then the kept ones.
        self.learnt.clear();
        self.learnt.push(asserting);
        self.learnt.extend(kept);
        // Clear the per-var minimize flags touched above.
        self.clear_minimize_flags();
        // Append the minimization sub-chains (reversed) to `lrat_chain`, ahead of
        // the final level-0/unit assembly (mirrors cadical's tail of
        // `minimize_clause`: `lrat_chain += reverse(minimize_chain)`; the later
        // global reverse in `analyze` flips it back to forward order).
        for &id in minimize_chain.iter().rev() {
            self.lrat_chain.push(id);
        }
    }

    /// Plain-path removable check: the exact recursion of the guarded port
    /// (`minimize_literal_lrat`, itself a port of cadical's
    /// `minimize_literal`), minus the LRAT chain bookkeeping.  `lit` is the
    /// TRUE form of a learnt literal; returns `true` if it can be resolved out.
    /// Early-exit classification shared by the root and every pushed child
    /// of [`Solver::minimize_literal_plain`]: `Ok(cid)` means the literal
    /// must be resolved through its reason clause; `Err(res)` is an early
    /// exit with that result (no flag marking, no `lrat_minimized` record –
    /// exactly the recursive form's pre-children returns).
    ///
    /// Counter/debug gates mirror the recursive form: the `mini_reject_*`
    /// diagnostics and Don Knuth's `seen.count < 2` gate fire only at
    /// depth 0; the `v.trail <= l.seen.trail` early abort fires at every
    /// depth (its counter still only at depth 0).
    fn minimize_classify(&mut self, lit: Lit, depth: u32) -> Result<ClauseId, bool> {
        const MINIMIZE_DEPTH_LIMIT: u32 = 100;
        let var = lit.var();
        let f = self.mf_get(var);
        let level = self.trail.level(var);
        if level == 0 || (f & MF_REMOVABLE) != 0 || (f & MF_KEEP) != 0 {
            return Err(true);
        }
        let reason = self.trail.reason(var);
        let no_reason = !matches!(reason, Reason::Propagation(_));
        if depth == 0 {
            if no_reason {
                self.mini_reject_no_reason += 1;
            } else if (f & MF_POISON) != 0 {
                self.mini_reject_poison += 1;
            } else if level == self.current_conflict_level {
                self.mini_reject_conflict_level += 1;
            }
        }
        // cadical compares against the conflict level (`v.level == level`),
        // not the current decision level: under chronological backtracking
        // the two differ, and treating a conflict-level literal as removable
        // resolves the UIP's own level through the clause – over-strengthening
        // it into a clause resolution does not derive (false UNSAT on
        // `circuit_48in64out…dist128_seed1`, SAT verified by CaDiCaL).
        if no_reason || (f & MF_POISON) != 0 || level == self.current_conflict_level {
            return Err(false);
        }
        // Don Knuth's gate (cadical `!depth && l.seen.count < 2`): at the top
        // of the recursion, a literal whose level contributed only one seen
        // literal (itself) cannot be resolved out through its own level.
        if depth == 0 {
            let lv = level as usize;
            if lv < self.seen_level_count.len() && self.seen_level_count[lv] < 2 {
                self.mini_reject_knuth += 1;
                return Err(false);
            }
        }
        // Early abort (cadical `v.trail <= l.seen.trail`): assigned before
        // every seen literal of its level, so its reason graph cannot reach
        // one of them; walking it would only chase lower levels in vain.
        {
            let lv = level as usize;
            if lv < self.seen_level_trail.len()
                && self.trail.trail_index(var) <= self.seen_level_trail[lv]
            {
                if depth == 0 {
                    self.mini_reject_early_abort += 1;
                }
                return Err(false);
            }
        }
        if depth > MINIMIZE_DEPTH_LIMIT {
            return Err(false);
        }
        let Reason::Propagation(cid) = reason else {
            return Err(false);
        };
        Ok(cid)
    }

    /// Removable check, **iterative** (explicit heap stack per the repo's
    /// recursion policy – the previous recursive form was depth-capped at
    /// 100 but paid a frame and a reason-clause SmallVec copy per node).
    /// `lit` is the TRUE form of a learnt literal; returns `true` if it can
    /// be resolved out (its reason graph reaches only level-0 literals,
    /// kept clause literals, or already-removable literals). Sets
    /// `MF_REMOVABLE`/`MF_POISON` and records the var for cleanup.
    ///
    /// Semantics are the recursive form's, including its short-circuit: a
    /// child returning `false` stops the parent's remaining children (they
    /// are never classified) and poisons it. Frames keep `(var, reason id,
    /// cursor)` and re-read literals from the arena on demand – the clause
    /// set is not mutated during analysis, so this equals the recursive
    /// form's per-node snapshot. A missing reason clause reads as "no
    /// children" (removable), matching the old `unwrap_or_default`.
    fn minimize_literal_plain(&mut self, lit: Lit, depth: u32) -> bool {
        let root_cid = match self.minimize_classify(lit, depth) {
            Err(res) => return res,
            Ok(cid) => cid,
        };

        struct Frame {
            var: Var,
            cid: ClauseId,
            next: usize,
            depth: u32,
            failed: bool,
        }
        let mut stack: SmallVec<[Frame; 32]> = SmallVec::new();
        stack.push(Frame {
            var: lit.var(),
            cid: root_cid,
            next: 0,
            depth,
            failed: false,
        });

        while !stack.is_empty() {
            // Post-order for a failed frame: poison this literal and
            // short-circuit the parent (its remaining children are never
            // classified, exactly like the recursive form's `break`).
            if stack.last().is_some_and(|f| f.failed) {
                if let Some(frame) = stack.pop() {
                    self.mf_set(frame.var, MF_POISON);
                    self.lrat_minimized.push(frame.var.index() as i32);
                }
                if let Some(parent) = stack.last_mut() {
                    parent.failed = true;
                }
                continue;
            }
            // Next child: the next reason literal after `next` that is not
            // the frame's own variable (the recursive form skipped the
            // resolved-out literal BY VALUE, not position).
            let (child, child_depth) = {
                let Some(frame) = stack.last_mut() else {
                    break;
                };
                let depth = frame.depth + 1;
                let mut child: Option<Lit> = None;
                if let Some(clause) = self.clauses.get(frame.cid) {
                    let mut i = frame.next;
                    while i < clause.lits.len() {
                        let l = clause.lits[i];
                        i += 1;
                        if l.var() != frame.var {
                            child = Some(l);
                            break;
                        }
                    }
                    frame.next = i;
                } else {
                    // Missing reason clause: no children (removable), like
                    // the recursive form's `unwrap_or_default`.
                    frame.next = usize::MAX;
                }
                (child, depth)
            };
            let Some(child_lit) = child else {
                // Children exhausted without failure: removable.
                if let Some(frame) = stack.pop() {
                    self.mf_set(frame.var, MF_REMOVABLE);
                    self.lrat_minimized.push(frame.var.index() as i32);
                }
                continue;
            };
            match self.minimize_classify(child_lit.negate(), child_depth) {
                Err(true) => {} // early-true child: skip it
                Err(false) => {
                    if let Some(frame) = stack.last_mut() {
                        frame.failed = true; // short-circuit this frame
                    }
                }
                Ok(cid) => stack.push(Frame {
                    var: child_lit.var(),
                    cid,
                    next: 0,
                    depth: child_depth,
                    failed: false,
                }),
            }
        }

        // The root's outcome: it was marked by its own post-order step; a
        // root that never failed is removable. (`stack` is empty here.)
        (self.mf_get(lit.var()) & MF_REMOVABLE) != 0
    }

    /// Recursive removable check (faithful port of `minimize_literal`). `lit` is
    /// the TRUE form of a learnt literal; returns `true` if it can be resolved
    /// out (its reason graph reaches only level-0 literals, kept clause
    /// literals, or already-removable literals). Sets `MF_REMOVABLE`/`MF_POISON`
    /// and records the var for cleanup. Depth-limited to bound the stack.
    fn minimize_literal_lrat(&mut self, lit: Lit, depth: u32) -> bool {
        const MINIMIZE_DEPTH_LIMIT: u32 = 100;
        let var = lit.var();
        let f = self.mf_get(var);
        let level = self.trail.level(var);
        if level == 0 || (f & MF_REMOVABLE) != 0 || (f & MF_KEEP) != 0 {
            return true;
        }
        let reason = self.trail.reason(var);
        let no_reason = !matches!(reason, Reason::Propagation(_));
        // See `minimize_literal_plain`: the conflict level, not
        // `decision_level()`.
        if no_reason || (f & MF_POISON) != 0 || level == self.current_conflict_level {
            return false;
        }
        if depth == 0 {
            let lv = level as usize;
            if lv < self.seen_level_count.len() && self.seen_level_count[lv] < 2 {
                return false;
            }
        }
        {
            let lv = level as usize;
            if lv < self.seen_level_trail.len()
                && self.trail.trail_index(var) <= self.seen_level_trail[lv]
            {
                return false;
            }
        }
        if depth > MINIMIZE_DEPTH_LIMIT {
            return false;
        }
        let Reason::Propagation(cid) = reason else {
            return false;
        };
        // Snapshot the reason clause's literals (release the borrow) before
        // recursing through `&mut self`.
        let others: SmallVec<[Lit; 8]> = self
            .clauses
            .get(cid)
            .map(|c| {
                c.lits
                    .iter()
                    .filter(|&&l| l.var() != var)
                    .copied()
                    .collect()
            })
            .unwrap_or_default();
        let mut res = true;
        for other in others {
            if !self.minimize_literal_lrat(other.negate(), depth + 1) {
                res = false;
                break;
            }
        }
        if res {
            self.mf_set(var, MF_REMOVABLE);
        } else {
            self.mf_set(var, MF_POISON);
        }
        self.lrat_minimized.push(var.index() as i32);
        res
    }

    /// Iterative reason-graph walk collecting the LRAT chain for a minimized-away
    /// literal `lit` (TRUE form) – faithful port of `calculate_minimize_chain`.
    /// Reason-clause ids go to [`Solver::mini_chain`] in post-order; level-0
    /// units go to [`Solver::unit_chain`]. Per-var flags indexed by `var.index()`.
    ///
    /// The stack uses **1-based** variable indices so that the "emit this var's
    /// reason id" marker (the negated index) never collides with var index 0 –
    /// cadical is safe because its `vidx` is already 1-based, but oxiz vars are
    /// 0-based, so `-0 == 0` would otherwise alias var 0 with its own marker.
    fn calculate_minimize_chain_lrat(&mut self, lit: Lit) {
        debug_assert!(self.lrat);
        self.mini_chain.clear();
        let mut stack: SmallVec<[i32; 64]> = SmallVec::new();
        stack.push(lit.var().index() as i32 + 1); // 1-based
        while let Some(idx) = stack.pop() {
            if idx < 0 {
                // Marker: emit this var's reason-clause id.
                let var = Var::new(((-idx) - 1) as u32);
                if let Reason::Propagation(cid) = self.trail.reason(var) {
                    self.mini_chain.push(self.proof_clause_id(cid));
                }
                continue;
            }
            let var = Var::new((idx - 1) as u32);
            let f = self.mf_get(var);
            if (f & (MF_KEEP | MF_ADDED | MF_POISON)) != 0 {
                continue;
            }
            let level = self.trail.level(var);
            if level == 0 {
                // Every level-0 literal is a unit with an id (level-0 flush), so
                // reference it directly – cadical's level-0 branch.
                if (f & MF_SEEN) != 0 {
                    continue;
                }
                self.mf_set(var, MF_SEEN);
                self.unit_analyzed.push(var.index() as i32);
                let true_dimacs = self.true_lit_dimacs(var);
                self.unit_chain.push(self.proof_unit_id(true_dimacs));
                continue;
            }
            let reason = self.trail.reason(var);
            let Reason::Propagation(cid) = reason else {
                // No usable reason (Decision at level>0 / Theory) – skip.
                continue;
            };
            // level > 0 (or level-0 propagated): mark added, walk its reason clause.
            self.mf_set(var, MF_ADDED);
            let reason_lits: SmallVec<[Lit; 8]> = self
                .clauses
                .get(cid)
                .map(|c| c.lits.iter().copied().collect())
                .unwrap_or_default();
            // Marker (processed after descendants) then the antecedent vars.
            stack.push(-idx);
            for &other in &reason_lits {
                if other.var() == var {
                    continue;
                }
                stack.push(other.var().index() as i32 + 1); // 1-based
            }
        }
    }

    /// The DIMACS form of the literal currently TRUE for `var` (for level-0
    /// unit-id lookups during minimization).
    fn true_lit_dimacs(&self, var: Var) -> i32 {
        if self.trail.lit_value(Lit::pos(var)).is_true() {
            Lit::pos(var).to_dimacs()
        } else {
            Lit::neg(var).to_dimacs()
        }
    }

    /// Per-var minimization-flag accessors (flags live in [`Solver::lrat_flags`],
    /// indexed by `var.index()`).
    fn mf_get(&self, var: Var) -> u8 {
        let i = var.index();
        if i < self.lrat_flags.len() {
            self.lrat_flags[i]
        } else {
            0
        }
    }
    fn mf_set(&mut self, var: Var, bit: u8) {
        let i = var.index();
        if i < self.lrat_flags.len() {
            self.lrat_flags[i] |= bit;
        }
    }
    fn mf_unset(&mut self, var: Var, bit: u8) {
        let i = var.index();
        if i < self.lrat_flags.len() {
            self.lrat_flags[i] &= !bit;
        }
    }

    /// Clear every minimization flag touched during [`Self::minimize_clause_lrat`]:
    /// removable/poison/added for minimized vars, keep for kept (learnt) vars,
    /// seen for level-0 vars reached by the chain walk.
    /// Debug instrumentation for the shrink study (OXIZ_SHRINK_TRACE=1).
    fn shrink_trace_enabled(&self) -> bool {
        // OnceLock: this fires once per conflict (every
        // `shrink_and_minimize_clause`); an uncached `env::var` here was
        // 10 %+ of a profiled dev run in `getenv` (environ is ~280
        // entries on this box, so each lookup is a linear scan).
        #[cfg(feature = "std")]
        {
            use std::sync::OnceLock;
            static FLAG: OnceLock<bool> = OnceLock::new();
            *FLAG.get_or_init(|| std::env::var("OXIZ_SHRINK_TRACE").is_ok())
        }
        #[cfg(not(feature = "std"))]
        {
            false
        }
    }

    #[cfg(feature = "std")]
    fn shrink_trace_record(&mut self, dbg: ShrinkTraceDbg) {
        self.shrink_trace.0 += 1;
        self.shrink_trace.1 += dbg.learnt_len as u64;
        self.shrink_trace.2 += dbg.singleton_blocks;
        self.shrink_trace.3 += dbg.multi_blocks;
        self.shrink_trace.4 += dbg.multi_block_lits;
        self.shrink_trace.5 += dbg.walk_success;
        self.shrink_trace.6 += dbg.walk_fail;
        self.shrink_trace.7 += dbg.fallback_saved;
    }

    #[cfg(not(feature = "std"))]
    fn shrink_trace_record(&mut self, _dbg: ShrinkTraceDbg) {}

    fn clear_minimize_flags(&mut self) {
        // Disjoint-field iteration (index into `lrat_minimized`, mutate
        // `lrat_flags`): the previous `drain(..).collect()` made a fresh
        // SmallVec per conflict — a heap allocation + copy on every
        // conflict whose analyzed set exceeds the inline capacity (the
        // common case once shrink marks are included; `clear_minimize_flags`
        // was 11.5 % self-time in the 2026-08-21 noL profile).
        const MINIMIZED_MASK: u8 = MF_REMOVABLE | MF_POISON | MF_ADDED | MF_SHRINKABLE;
        let n = self.lrat_minimized.len();
        for i in 0..n {
            let vi = self.lrat_minimized[i] as usize;
            if vi < self.lrat_flags.len() {
                self.lrat_flags[vi] &= !MINIMIZED_MASK;
            }
        }
        self.lrat_minimized.clear();
        let m = self.learnt.len();
        for i in 0..m {
            let vi = self.learnt[i].var().index();
            if vi < self.lrat_flags.len() {
                self.lrat_flags[vi] &= !MF_KEEP;
            }
        }
        let a = self.unit_analyzed.len();
        for i in 0..a {
            let vi = self.unit_analyzed[i] as usize;
            if vi < self.lrat_flags.len() {
                self.lrat_flags[vi] &= !MF_SEEN;
            }
        }
        self.unit_analyzed.clear();
    }

    /// We use a recursive check: a literal l is redundant if its reason clause
    /// contains only literals that are either:
    /// - Already in the learnt clause (marked as seen)
    /// - At decision level 0 (always true in the learned clause context)
    /// - Themselves redundant (recursive check)
    ///
    /// This also performs clause strengthening by checking for stronger implications
    /// Learned-clause improvement dispatcher (cadical `analyze.cpp`:
    /// `if (opts.shrink) shrink_and_minimize_clause (); else if (opts.minimize)
    /// minimize_clause ();`).  With block shrinking enabled the LRAT path runs
    /// the same shrink walk as the plain path: since the 2026-09 port of
    /// cadical's direct-LRAT shrink (`shrink.cpp`'s `old_clause_lrat` scheme)
    /// the walk extends the RUP chain per removed literal, so proofs no
    /// longer force the weaker plain minimizer and both modes share one
    /// search shape.  `OXIZ_SHRINK_NULL` runs the full shrink walk and
    /// discards its result — the matched null for the seed study
    /// (docs/BENCHMARKING.md).
    ///
    /// Takes `vars_to_bump` so a successful shrink can add each block-UIP
    /// variable to the conflict's bump set exactly where cadical adds it to
    /// `analyzed` (`shrunken_block_uip`), ahead of the batch bump.
    pub(super) fn improve_learnt_clause(&mut self, vars_to_bump: &mut SmallVec<[Var; 32]>) {
        if !self.config.enable_shrink {
            self.minimize_learnt_clause();
            return;
        }
        if crate::shrink_null_enabled() {
            let saved = self.learnt.clone();
            self.shrink_and_minimize_clause(vars_to_bump);
            self.learnt = saved;
            self.minimize_learnt_clause();
        } else {
            self.shrink_and_minimize_clause(vars_to_bump);
        }
    }

    /// cadical's `chronoreusetrail` scan (see the call site): over the trail
    /// region strictly above `jump`'s boundary, find the variable with the
    /// highest bump key (VMTF stamp while focused, VSIDS score bits while
    /// stable — cadical's `bumped`/`score_smaller` split), then walk `res`
    /// up from `jump` while the next level's boundary starts at or below
    /// that variable's trail position (`control[res+1].trail <= best_pos`).
    /// Returns `None` when the scan finds nothing to reuse (fall back to the
    /// plain level).  Matched null (`OXIZ_CHRONOREUSE_NULL=1`): the bump key
    /// is scrambled (same scan, same work, no selection semantics).
    fn chrono_reuse_level(&self, level: u32, jump: u32) -> Option<u32> {
        let start = self.trail.level_start(jump + 1);
        let trail = self.trail.assignments();
        if start >= trail.len() {
            return None;
        }
        let null = crate::chrono_reuse_null_enabled();
        let use_scores = self.config.enable_stabilize && self.stable;
        let mut best: Option<Var> = None;
        let mut best_key = 0u64;
        for &lit in &trail[start..] {
            let var = lit.var();
            let mut key = if use_scores {
                // VSIDS activities are non-negative f64s; their IEEE bit
                // patterns order identically, so `to_bits` preserves the
                // score order as a u64 key.
                self.vsids.activity(var).to_bits()
            } else {
                self.vmtf.activity(var)
            };
            if null {
                key ^= key << 13;
                key ^= key >> 7;
                key ^= key << 17;
            }
            if best.is_none() || key > best_key {
                best = Some(var);
                best_key = key;
            }
        }
        let best = best?;
        let best_pos = self.trail.trail_index(best) as usize;
        let mut res = jump;
        while res < level.saturating_sub(1) && self.trail.level_start(res + 1) <= best_pos {
            res += 1;
        }
        if res == jump { None } else { Some(res) }
    }

    /// cadical `shrink_and_minimize_clause` (`shrink.cpp`, the `opts.shrink ==
    /// 3` "full" default): shrink the raw 1-UIP clause by blocks.
    ///
    /// The clause's literals at one common decision level (below the conflict
    /// level) form a *block*; resolving the block's literals against their
    /// reasons, restricted to that level and iterated to its own 1-UIP,
    /// derives a clause that subsumes the block — so the whole block is
    /// replaced by the single block-UIP literal (`¬uip`, false at that
    /// level).  On stable-300-class instances cadical removes ~68% of learned
    /// literals this way (vs ~30-40% for plain recursive minimization), which
    /// is the difference between thin clauses that propagate (and keep trails
    /// dense) and fat ones that never fire.
    ///
    /// Blocks with fewer than two literals are kept as-is.  When a block's
    /// walk fails (an antecedent at a lower level is not removable, or a
    /// non-clausal reason is met), the block falls back to per-literal
    /// recursive minimization (`shrunken_block_no_uip`).
    pub(super) fn shrink_and_minimize_clause(&mut self, vars_to_bump: &mut SmallVec<[Var; 32]>) {
        let n = self.learnt.len();
        if n <= 2 {
            // cadical gates on `size > 1`; a binary clause has a one-literal
            // "block" at most and nothing to shrink.
            return;
        }
        let original_len = n;
        // Sentinel marking removed slots (cadical reuses `uip0 = clause[0]`,
        // which cannot occur elsewhere in the deduplicated clause).
        let sentinel = self.learnt[0];

        // Sort `learnt[1..]` by (decision level, trail index) DESCENDING
        // (cadical `shrink_trail_negative_rank` MSORT; `learnt[0]` is the
        // conflict-level asserting literal and stays pinned at index 0).
        // Level-first ordering is what makes chronological backtracking safe
        // here: blocks are same-level runs regardless of trail order.
        {
            let mut keyed: SmallVec<[(u64, Lit); 16]> = self.learnt[1..]
                .iter()
                .map(|&l| {
                    let key = ((self.trail.level(l.var()) as u64) << 32)
                        | u64::from(self.trail.trail_index(l.var()));
                    (key, l)
                })
                .collect();
            keyed.sort_unstable_by_key(|&(key, _)| std::cmp::Reverse(key));
            for (i, (_, lit)) in keyed.into_iter().enumerate() {
                self.learnt[i + 1] = lit;
            }
        }

        // Under LRAT, snapshot the sorted clause (cadical `shrink.cpp`'s
        // `old_clause_lrat`): every position whose literal the block walks
        // below change (sentinel-replaced block members, the block-UIP
        // replacement, fallback-minimized literals) owes the ORIGINAL
        // literal's resolution sub-graph as RUP hints, collected during the
        // compaction below and appended (reversed) to `lrat_chain` — the
        // exact scheme cadical added for direct LRAT output, where the same
        // `calculate_minimize_chain` walk serves both plain minimization and
        // the shrink ("we cannot create the chain directly during shrinking
        // but afterwards ... the same algorithm works for both", cadical
        // `analyze.cpp`).
        let old_clause: SmallVec<[Lit; 32]> = if self.lrat {
            self.learnt[1..].iter().copied().collect()
        } else {
            SmallVec::new()
        };
        let mut minimize_chain: Vec<i64> = Vec::new();

        // Blocks: contiguous same-level runs over `learnt[1..]`, visited from
        // the lowest level (clause tail) toward the front.
        let mut total_shrunken: u64 = 0;
        let mut total_minimized: u64 = 0;
        let trace = self.shrink_trace_enabled();
        #[allow(clippy::default_constructed_unit_structs)]
        let mut dbg = ShrinkTraceDbg {
            learnt_len: n,
            ..ShrinkTraceDbg::default()
        };
        let mut i = n - 1;
        while i >= 1 {
            let blevel = self.trail.level(self.learnt[i].var());
            let mut j = i;
            while j > 1 && self.trail.level(self.learnt[j - 1].var()) == blevel {
                j -= 1;
            }
            if i - j + 1 < 2 {
                // Singleton block: kept (nothing to resolve against).
                dbg.singleton_blocks += 1;
                self.mf_set(self.learnt[i].var(), MF_KEEP);
            } else {
                dbg.multi_blocks += 1;
                dbg.multi_block_lits += (i - j + 1) as u64;
                let (s, m) = self.shrink_block(j, i, blevel, sentinel, vars_to_bump);
                if s > 0 {
                    dbg.walk_success += 1;
                } else {
                    dbg.walk_fail += 1;
                }
                dbg.fallback_saved += m;
                total_shrunken += s;
                total_minimized += m;
            }
            i = j - 1;
        }
        if trace {
            self.shrink_trace_record(dbg);
        }

        // Compaction: drop the sentinel slots (cadical's in-place `i`/`j`
        // filter over the clause).  Under LRAT, each position whose literal
        // no longer equals the sorted snapshot's is collected as a chain
        // obligation FIRST: the stored literal was resolved away by the
        // block walk (a sentinel slot), replaced by the block's UIP
        // negation, or minimized by a fallback — in every case the
        // ORIGINAL literal is the one the resolution derivation owes, and
        // `calculate_minimize_chain_lrat` walks its reason graph through
        // the still-live keep/removable/poison flags (so this must run
        // BEFORE `clear_minimize_flags`).  An unchanged position whose
        // literal happens to be its own block-UIP replacement owes nothing,
        // which the equality check expresses exactly.
        let mut w = 1;
        for r in 1..n {
            let lit = self.learnt[r];
            if self.lrat {
                let old = old_clause[r - 1];
                if lit != old {
                    self.calculate_minimize_chain_lrat(old.negate());
                    for &id in &self.mini_chain {
                        minimize_chain.push(id);
                    }
                    self.mini_chain.clear();
                }
            }
            if lit == sentinel && r != 0 {
                continue;
            }
            self.learnt[w] = lit;
            w += 1;
        }
        self.learnt.truncate(w);

        // Minimize-flag hygiene, exactly like `minimize_learnt_clause`'s tail:
        // every flag this pass touched (keep on kept literals,
        // removable/poison/shrinkable on walk-touched vars, recorded in
        // `lrat_minimized`) must be reset before the next analysis reads
        // them.  A stale `MF_SHRINKABLE` bit surviving into the next
        // conflict's block walk makes its trail scan pop a foreign-level
        // variable (caught by the replacement-level debug assert on
        // `si2-b03-m800-03`; in release it would silently mis-shrink).
        self.clear_minimize_flags();

        // LRAT: append the shrink's minimization sub-chains (reversed) to
        // `lrat_chain`, mirroring `minimize_clause_lrat`'s tail (cadical's
        // `lrat_chain += reverse (minimize_chain)`); `analyze`'s later unit
        // append + global reverse turns them into checker replay order.
        if self.lrat {
            for &id in minimize_chain.iter().rev() {
                self.lrat_chain.push(id);
            }
        }

        let final_len = self.learnt.len();
        if final_len < original_len {
            self.stats.minimizations += 1;
            self.stats.literals_removed += (original_len - final_len) as u64;
        }
        self.stats.shrunken += total_shrunken;
        self.stats.minishrunken += total_minimized;
    }

    /// Shrink one block: `learnt[start..=end]` all sit at decision level
    /// `blevel` (with `end` holding the block's lowest trail position after
    /// the sort).  Returns `(shrunken, minimized)` literal counts.  See
    /// [`Self::shrink_and_minimize_clause`].
    fn shrink_block(
        &mut self,
        start: usize,
        end: usize,
        blevel: u32,
        sentinel: Lit,
        vars_to_bump: &mut SmallVec<[Var; 32]>,
    ) -> (u64, u64) {
        // Mark every block literal shrinkable; `open` counts undischarged
        // shrinkable literals.
        let mut open: u32 = 0;
        let mut max_trail: usize = 0;
        let mut shrinkable: SmallVec<[Var; 32]> = SmallVec::new();
        // Literals at `blevel` marked shrinkable by this block's reason walk
        // (not in the block itself); cadical's `shrinkable` vector holds both
        // and is fully reset after every block.
        let mut walk_marked: SmallVec<[Var; 32]> = SmallVec::new();
        // Chunk-summary state for this block: lazily activated by the scan
        // below after `SHRINK_SUMMARY_AFTER` consecutive probe misses (the
        // signature of a sparse stretch).  Until then the block pays
        // nothing — no epoch bump, no sizing, no marking.  `shrink_literal`
        // reads this to decide whether to mark walk-discovered literals.
        self.shrink_active_epoch = None;
        for k in start..=end {
            let var = self.learnt[k].var();
            let ti = self.trail.trail_index(var) as usize;
            self.mf_set(var, MF_SHRINKABLE);
            self.lrat_minimized.push(var.index() as i32);
            shrinkable.push(var);
            max_trail = max_trail.max(ti);
            open += 1;
        }

        // Backward trail scan (cadical `shrink_next` without the reap): the
        // next literal to discharge is the most recently assigned shrinkable
        // one.  The cursor only descends; reason antecedents always sit
        // below their implier on the trail, so nothing is missed.
        //
        // The popped literal's trail index is captured *at pop time*
        // (`uip_pos = pos` inside the loop below).  A previous revision
        // recomputed it as `cursor + 1` after the loop, which is wrong when
        // the UIP sits at trail index 0: the cursor's `saturating_sub` then
        // leaves it at 0 instead of wrapping, `cursor + 1` points at the
        // *next* literal above, and the block was replaced by that literal's
        // negation – a literal resolution never derived.  On the 194-block
        // incremental tautology regression this produced the unentailed
        // clause `[3,4,5,-7,6,-8]` (block `{-8,-1}` at level 1, UIP = the
        // level-1 decision `-1`, replaced by `-8`) and a false `unsat`.
        let mut cursor = max_trail;
        let mut failed = false;
        let mut uip_var: Option<Var> = None;
        let mut uip_pos: usize = max_trail;
        while !failed {
            // `shrink_next`: pop the newest shrinkable literal.
            //
            // Two mechanisms, one pop order:
            //
            // * **Probe** (always first): plain per-position descent, in
            //   groups of `SHRINK_SUMMARY_AFTER` positions.  Dense blocks
            //   (2–7 skipped entries per pop, the frb45/noL/circuit class)
            //   always find their literal inside the first group and never
            //   touch the summary — their cost is the original scan plus
            //   the group-loop induction, nothing else.
            // * **Summary jump** (after a full group misses): a 64-position
            //   chunk summary of `MF_SHRINKABLE`, epoch-stamped per
            //   activation.  Sparse stretches (worker-class: 52 skipped
            //   entries per pop) then descend one summary word per chunk
            //   instead of one load per position.
            //
            // The summary is exact for this block: at activation the
            // complete flagged set (`shrinkable` + `walk_marked`) is
            // bulk-marked, and every later marking site marks
            // incrementally under the same epoch; the flagged set only
            // grows and positions never move within a block.  Stale
            // entries from earlier blocks read as empty (epoch mismatch).
            // `mf_get` remains authoritative for every popped literal —
            // the summary only decides where to look next, never what
            // pops — so the pop order (newest flagged first) is the scan's
            // in every mix, and even a wrong summary could not mis-pop.
            let popped;
            'pop: loop {
                if self.shrink_active_epoch.is_none() {
                    let mut probes = 0;
                    loop {
                        let pos = cursor;
                        let uip_lit = self.trail.assignments()[pos];
                        cursor = cursor.saturating_sub(1);
                        if self.mf_get(uip_lit.var()) & MF_SHRINKABLE != 0 {
                            popped = Some((pos, uip_lit));
                            break 'pop;
                        }
                        probes += 1;
                        if probes == SHRINK_SUMMARY_AFTER {
                            break;
                        }
                    }
                    // A whole group missed: activate the summary for this
                    // block.  One-time O(open + walk-marked) bulk mark of
                    // the complete flagged set (positions already popped
                    // included — harmless, the cursor never revisits them),
                    // then the summary-jump path below takes over.
                    self.shrink_epoch = self.shrink_epoch.wrapping_add(1);
                    let epoch = self.shrink_epoch;
                    let chunks_needed = self.trail.assignments().len().div_ceil(64);
                    if self.shrink_summary.len() < chunks_needed {
                        self.shrink_summary
                            .resize(chunks_needed, ShrinkChunk::EMPTY);
                    }
                    for &var in shrinkable.iter().chain(walk_marked.iter()) {
                        self.shrink_flag_position(self.trail.trail_index(var) as usize, epoch);
                    }
                    self.shrink_active_epoch = Some(epoch);
                }
                // Summary-jump descent (the epoch is always valid here:
                // the probe path above activates before falling through).
                let epoch = self.shrink_active_epoch.unwrap_or(u64::MAX);
                let c = cursor >> 6;
                let in_pos = cursor & 63;
                let avail = {
                    let s = &self.shrink_summary[c];
                    if s.epoch == epoch {
                        s.bits & (u64::MAX >> (63 - in_pos))
                    } else {
                        0
                    }
                };
                if avail == 0 {
                    if c == 0 {
                        // Trail exhausted with flagged literals unaccounted:
                        // impossible while the open-count invariant holds
                        // (every open literal is flagged, hence summarized).
                        // Degrade to the sound fallback rather than spin or
                        // fabricate a UIP.
                        popped = None;
                        break 'pop;
                    }
                    cursor = (c << 6) - 1;
                    continue 'pop;
                }
                let pos = (c << 6) + (63 - avail.leading_zeros() as usize);
                cursor = pos.saturating_sub(1);
                let uip_lit = self.trail.assignments()[pos];
                if self.mf_get(uip_lit.var()) & MF_SHRINKABLE != 0 {
                    popped = Some((pos, uip_lit));
                    break 'pop;
                }
                // Exactness makes this unreachable; clear the phantom bit
                // anyway so the descent always makes progress (liveness
                // guard, not a correctness path).
                self.shrink_summary[c].bits &= !(1 << (pos & 63));
            }
            // `popped` is `None` only on the impossible-exhaustion path above.
            let Some((pos, uip_lit)) = popped else {
                failed = true;
                break;
            };
            open -= 1;
            if open == 0 {
                uip_var = Some(uip_lit.var());
                uip_pos = pos;
                break;
            }
            // `shrink_along_reason`: resolve the popped literal against its
            // reason (`resolve_large_clauses` is unconditionally true under
            // `shrink == 3`).
            let Reason::Propagation(cid) = self.trail.reason(uip_lit.var()) else {
                failed = true;
                break;
            };
            let reason_lits: SmallVec<[Lit; 8]> = self
                .clauses
                .get(cid)
                .map(|c| {
                    c.lits
                        .iter()
                        .filter(|&&l| l.var() != uip_lit.var())
                        .copied()
                        .collect()
                })
                .unwrap_or_default();
            if reason_lits.is_empty() {
                failed = true;
                break;
            }
            for &lit in &reason_lits {
                match self.shrink_literal(lit, blevel) {
                    ShrinkStep::Fail => {
                        failed = true;
                        break;
                    }
                    ShrinkStep::NewlyShrinkable => {
                        // Walk-discovered literal: record it so the flag
                        // reset below covers it too (cadical's `shrinkable`
                        // member collects exactly these; a stale
                        // MF_SHRINKABLE from this block's walk leaking into
                        // a later block's trail scan within the same clause
                        // makes it pop a foreign literal and mis-derive the
                        // replacement).
                        walk_marked.push(lit.var());
                        open += 1;
                    }
                    ShrinkStep::Skip => {}
                }
                if failed {
                    break;
                }
            }
        }

        if failed {
            // `reset_shrinkable` + `shrunken_block_no_uip`: fall back to
            // per-literal recursive minimization inside the block.  Reset
            // covers the walk-marked literals too (cadical resets its whole
            // `shrinkable` vector).
            for &var in shrinkable.iter().chain(walk_marked.iter()) {
                self.mf_unset(var, MF_SHRINKABLE);
            }
            let mut minimized: u64 = 0;
            // NOTE: cadical iterates oldest-first here (reverse iterators),
            // and oldest-first measured +2.4 fallback literals/analyze with
            // the poison cascade gone (`2026-08-satcomp-standing-gap.md`,
            // "SOLVED" section) — but it REVERTED again: the changed learned
            // clauses explode the `wisas/xs_8_13` determinism canary by
            // 50×+ CPU (11 s → >515 s user, both profiles; 20-core box, 4×
            // oversubscribed controls isolate CPU from load).  A designated
            // canary gates landings, so the semantic win stays unlanded
            // until wisas's trajectory fragility is understood.  Newest-first
            // (the pre-existing order) is equally SOUND — each removal is
            // still individually justified; it merely saves less.
            for k in start..=end {
                let lit = self.learnt[k];
                if self.minimize_literal_plain(lit.negate(), 0) {
                    self.learnt[k] = sentinel;
                    minimized += 1;
                } else {
                    self.mf_set(lit.var(), MF_KEEP);
                }
            }
            (0, minimized)
        } else {
            // `shrunken_block_uip`: replace the block by the negation of its
            // UIP.  `uip_lit` is TRUE on the trail; the clause stores false
            // literals, so the replacement is its negation, at `blevel`.
            let Some(uvar) = uip_var else {
                return (0, 0);
            };
            let repl = self.trail.assignments()[uip_pos].negate();
            debug_assert_eq!(self.trail.level(repl.var()), blevel);
            self.learnt[end] = repl;
            for k in start..end {
                self.learnt[k] = sentinel;
            }
            let block_shrunken = (end - start) as u64;
            // Keep-flag + analysis bookkeeping (cadical marks the replacement
            // `keep`, adds it to `analyzed`, and resets the level's seen
            // statistics as if it were the level's sole contributor).
            self.mf_set(uvar, MF_KEEP);
            if !self.seen[uvar.index()] {
                self.seen[uvar.index()] = true;
                if !vars_to_bump.contains(&uvar) {
                    vars_to_bump.push(uvar);
                }
            }
            let bl = blevel as usize;
            if bl < self.seen_level_count.len() {
                self.seen_level_count[bl] = 1;
                self.seen_level_trail[bl] = self.trail.trail_index(uvar);
            }
            // `mark_shrinkable_as_removable`: block and chain literals were
            // resolved away; they carry the REMOVABLE flag until the
            // analysis-wide reset (recorded above via `lrat_minimized`).
            for &var in shrinkable.iter().chain(walk_marked.iter()) {
                self.mf_unset(var, MF_SHRINKABLE);
                self.mf_set(var, MF_REMOVABLE);
            }
            (block_shrunken, 0)
        }
    }

    /// OR trail position `ti` into the current block's chunk summary (see
    /// [`Solver::shrink_summary`]).  Called from every `MF_SHRINKABLE`
    /// marking site; the summary is sized by the caller for the whole
    /// trail (immutable during analysis).
    #[inline]
    fn shrink_flag_position(&mut self, ti: usize, epoch: u64) {
        let c = ti >> 6;
        debug_assert!(c < self.shrink_summary.len());
        let e = &mut self.shrink_summary[c];
        if e.epoch != epoch {
            e.epoch = epoch;
            e.bits = 1 << (ti & 63);
        } else {
            e.bits |= 1 << (ti & 63);
        }
    }

    /// One step of the block's resolution walk (cadical `shrink_literal`).
    /// `lit` is FALSE on the trail.  `Skip` covers level-0 literals,
    /// already-shrinkable ones, and lower-level literals that are (or probe)
    /// removable; `Fail` aborts the block walk (a lower-level antecedent that
    /// is not removable).
    fn shrink_literal(&mut self, lit: Lit, blevel: u32) -> ShrinkStep {
        let var = lit.var();
        let level = self.trail.level(var);
        if level == 0 {
            return ShrinkStep::Skip;
        }
        let f = self.mf_get(var);
        if f & MF_SHRINKABLE != 0 {
            return ShrinkStep::Skip;
        }
        if level < blevel {
            if f & MF_REMOVABLE != 0 {
                return ShrinkStep::Skip;
            }
            // `shrink > 2`: try minimization for lower-level antecedents.
            if self.minimize_literal_plain(lit.negate(), 1) {
                return ShrinkStep::Skip;
            }
            self.shrink_fail_low += 1;
            return ShrinkStep::Fail;
        }
        if level > blevel {
            // cadical asserts reasons never reach above the block's level;
            // under our chronological backtracking that invariant is not
            // guaranteed, so degrade to failure (the block falls back to
            // plain minimization) instead of resolving through it.
            self.shrink_fail_above += 1;
            return ShrinkStep::Fail;
        }
        self.mf_set(var, MF_SHRINKABLE);
        self.lrat_minimized.push(var.index() as i32);
        // Walk-discovered marking site: keep the chunk summary exact once
        // the block's scan has activated it (dense blocks never do — see
        // `shrink_block`).
        if let Some(epoch) = self.shrink_active_epoch {
            self.shrink_flag_position(self.trail.trail_index(var) as usize, epoch);
        }
        ShrinkStep::NewlyShrinkable
    }

    pub(super) fn minimize_learnt_clause(&mut self) {
        if self.learnt.len() <= 2 {
            // Don't minimize very small clauses
            return;
        }

        // Under LRAT, recursive minimization runs the chain-extending port
        // (`minimize_clause_lrat` + `calculate_minimize_chain_lrat`), which drops
        // redundant literals and extends the RUP chain per removed literal so
        // the smaller clause stays checkable. The plain (non-LRAT) recursive
        // minimization + strengthening below is the non-proof path.
        if self.lrat {
            self.minimize_clause_lrat();
            return;
        }

        let original_len = self.learnt.len();

        // Faithful port of cadical's `minimize_clause` (plain, proof-off
        // path).  The previous implementation was a MiniSat-style DFS that
        // trusted the analysis `seen` stamps as a removable shortcut; that
        // shortcut is only sound in classic CDCL (resolved-away literals sit
        // above the UIP, out of reach of the downward reason walk) and, with
        // chronological backtracking enabled, it resolved through conflict-
        // level literals whose obligation analysis never discharged –
        // over-strengthening learned clauses into a false UNSAT on
        // SATISFIABLE input (`summle_X4044…cnf`; the guarded LRAT port answers
        // `sat` on the identical instance).  This port now shares the guarded
        // port's exact semantics: flag-cached recursion with poison
        // propagation, the `v.level == level` rejection, Don Knuth's
        // `seen.count < 2` gate, the `v.trail <= l.seen.trail` early abort,
        // and a depth limit.  The `seen`-stamp shortcut and the separate
        // binary-reason "strengthening" phase are gone entirely.
        {
            // `learnt[0]` is the asserting literal and is always kept.
            // Process the rest in trail order (cadical `minimize_sort_clause`)
            // so a literal another resolves through is already decided
            // (kept → `MF_KEEP`, dropped → `MF_REMOVABLE`) when reached.
            let asserting = self.learnt[0];
            let mut order: SmallVec<[Lit; 32]> = self.learnt[1..].iter().copied().collect();
            order.sort_by_key(|&l| self.trail.trail_index(l.var()));

            let mut kept: SmallVec<[Lit; 32]> = SmallVec::new();
            for &lit in &order {
                if self.minimize_literal_plain(lit.negate(), 0) {
                    self.stats.literals_removed += 1;
                } else {
                    self.mf_set(lit.var(), MF_KEEP);
                    kept.push(lit);
                }
            }
            self.learnt.clear();
            self.learnt.push(asserting);
            self.learnt.extend(kept);
            self.clear_minimize_flags();
        }

        // Track minimization statistics
        let final_len = self.learnt.len();
        if final_len < original_len {
            self.stats.minimizations += 1;
        }
    }

    /// Analyze a theory conflict (given as a list of literals that are all false)
    pub(super) fn analyze_theory_conflict(
        &mut self,
        conflict_lits: &[Lit],
    ) -> (u32, SmallVec<[Lit; 32]>) {
        // A well-formed theory conflict clause is fully falsified – every literal
        // is assigned false on the trail – which is what makes the 1-UIP
        // resolution below well-defined. The MBQI / quantifier-instantiation path,
        // however, can hand us a "conflict" clause that still contains an
        // UNASSIGNED literal. The usual cause is a variable that was assigned when
        // the theory recorded the lemma but has since been unassigned by a
        // backtrack: `Trail` leaves `VarInfo.level` stale on unassignment, so
        // `trail.level()` reports a bogus non-zero level for it.
        //
        // Feeding such a clause into the all-false 1-UIP machinery is unsound. The
        // stale level becomes a spurious `current_level`; the pivot counter is
        // incremented for a literal that is not on the trail, so the backward
        // trail walk can never discharge it and instead resolves against an
        // unrelated variable at a lower level; the asserting literal is then
        // duplicated at the computed backtrack level. That produces
        // `backtrack_level == uip_level` (tripping the debug-assert below in debug
        // builds) and, in release builds, corrupts the trail into a wrong
        // top-level UNSAT on quantified UFLIA.
        //
        // A clause with an open literal is not a conflict at all but an
        // *asserting* theory lemma: it is unit under the current assignment (one
        // open literal, the rest false) and must simply propagate that literal.
        // Route it to a dedicated, trail-safe handler; keep the 1-UIP path for
        // genuine all-false conflicts (and for the pre-existing already-satisfied
        // case, which does not corrupt the trail).
        if conflict_lits
            .iter()
            .any(|&l| self.trail.lit_value(l) == LBool::Undef)
        {
            return self.analyze_theory_asserting_lemma(conflict_lits);
        }
        self.learnt.clear();
        self.learnt.push(Lit::from_code(0)); // Placeholder

        let mut counter = 0;

        // Anchor the analysis at the genuine conflict level – the highest
        // decision level among the (all-false) theory conflict literals –
        // rather than `trail.decision_level()`. A theory conflict can be
        // reported while the SAT trail sits at a strictly higher decision level
        // than any literal actually involved in the conflict; running 1-UIP
        // against `decision_level()` would then leave the asserting literal at
        // or below the backtrack level and corrupt the trail via an in-place
        // re-assignment in `learn_clause`. See the companion note in `analyze`.
        let current_level = {
            let mut lvl = 0;
            for &lit in conflict_lits {
                let l = self.trail.level(lit.var());
                if l > lvl {
                    lvl = l;
                }
            }
            lvl
        };

        // Reset seen flags
        for s in &mut self.seen {
            *s = false;
        }

        // Collect variables for batch bumping
        let mut vars_to_bump: SmallVec<[Var; 32]> = SmallVec::new();

        // Conflict level for the minimizer (see `analyze`).
        self.current_conflict_level = current_level;
        // Process conflict literals
        let mut all_level_zero = true;
        for &lit in conflict_lits {
            let var = lit.var();
            let level = self.trail.level(var);

            if !self.seen[var.index()] && level > 0 {
                all_level_zero = false;
                self.seen[var.index()] = true;
                vars_to_bump.push(var);
                self.note_seen_level(var, level);

                if level == current_level {
                    counter += 1;
                } else {
                    // Add the literal itself (not negated) to the learned clause.
                    // The conflict clause has all literals FALSE. To prevent this
                    // conflict, we need at least one of these literals to become TRUE.
                    // So we add the literal directly to the learned clause.
                    self.learnt.push(lit);
                }
            }
        }

        // If ALL conflict literals are at level 0, this is a fundamental UNSAT
        // that cannot be resolved by backtracking. Return an empty learned clause
        // with backtrack_level=0 as a signal.
        if !conflict_lits.is_empty() && all_level_zero {
            return (0, SmallVec::new());
        }

        // Find UIP by walking back through trail.  Only a CONFLICT-LEVEL
        // seen literal may discharge the counter: the trail is not sorted by
        // decision level under chronological backtracking, so the walk can
        // encounter a marked literal from a lower level (already carried in
        // the learned clause) sitting above the remaining conflict-level
        // literals.  Discharging on it terminates the 1-UIP loop early and
        // emits an asserting literal at or below the backtrack level
        // (`backtrack_level == uip level`, corrupting the trail) — the same
        // defect `analyze`'s `analyze_scan_pivot` guard exists for (Z3
        // `sat_solver.cpp` skips marked literals with
        // `lvl(c_var) != m_conflict_lvl`).  Port that guard here.
        let mut index = self.trail.assignments().len();
        let mut p = None;

        while counter > 0 {
            let Some(current_lit) =
                Self::analyze_scan_pivot(&self.seen, &self.trail, &mut index, current_level)
            else {
                break; // Trail exhausted (degenerate state) – keep `p` as-is.
            };
            p = Some(current_lit);
            let var = current_lit.var();

            counter -= 1;

            if counter > 0
                && let Reason::Propagation(reason_clause) = self.trail.reason(var)
                && let Some(clause) = self.clauses.get(reason_clause)
            {
                // Get reason and process its literals.
                // `current_lit` is the propagated (TRUE) literal being resolved
                // out; skip it BY VALUE rather than assuming it sits at index 0.
                // Binary-implication-graph propagation does not move the implied
                // literal to index 0, so a positional `[1..]` skip would drop the
                // false antecedent at index 0 and yield unsound learned clauses.
                //
                // Split-borrow through [`AnalysisMark`] so the literals are
                // iterated IN THE ARENA (the old shape snapshotted every reason
                // into a heap SmallVec – see the Boolean `analyze` fix).
                // `lrat: false` preserves this path's exact semantics: it has
                // no LRAT level-0 branch (unlike `analyze`), so the bundle's
                // level-0 deferral must stay dormant here.
                {
                    let Solver {
                        seen,
                        trail,
                        learnt,
                        seen_levels,
                        seen_level_count,
                        seen_level_trail,
                        ..
                    } = self;
                    let mut dormant_units: SmallVec<[i32; 4]> = SmallVec::new();
                    let mut mark = AnalysisMark {
                        seen: &mut seen[..],
                        trail,
                        learnt,
                        seen_levels,
                        seen_level_count: &mut seen_level_count[..],
                        seen_level_trail: &mut seen_level_trail[..],
                        lrat: false,
                        lrat_units: &mut dormant_units,
                    };
                    for &lit in clause.lits.iter() {
                        if lit == current_lit {
                            continue;
                        }
                        mark.mark_antecedent(lit, current_level, &mut counter, &mut vars_to_bump);
                    }
                }
            } else if counter > 0
                && let Reason::Theory = self.trail.reason(var)
                && let Some(tail) = self.theory_reason_tail(var).cloned()
            {
                // Lazily explained theory propagation: resolve through the
                // stored tail (exactly the literals a materialized reason
                // clause would carry after its head; the head – the TRUE
                // literal `current_lit` – is absent, so no skip is needed).
                for &lit in &tail {
                    let reason_var = lit.var();
                    let level = self.trail.level(reason_var);

                    if !self.seen[reason_var.index()] && level > 0 {
                        self.seen[reason_var.index()] = true;
                        vars_to_bump.push(reason_var);
                        self.note_seen_level(reason_var, level);

                        if level == current_level {
                            counter += 1;
                        } else {
                            self.learnt.push(lit);
                        }
                    }
                }
            }
        }

        // Batch bump all collected variables
        self.vsids.bump_batch(&vars_to_bump);
        if self.config.use_chb_branching {
            self.chb.bump_batch(&vars_to_bump);
        }
        if self.config.use_lrb_branching {
            self.lrb.on_reason_batch(&vars_to_bump);
        }

        // Set asserting literal
        if let Some(uip) = p {
            self.learnt[0] = uip.negate();
        }

        // Improve (shrink/minimize) the learned clause before the bump batch,
        // mirroring `analyze` (block-UIP vars join the bump set).
        self.improve_learnt_clause(&mut vars_to_bump);

        // Compute the real LBD from the FINAL learned clause literals (post-minimization),
        // matching the standard Glucose definition rather than using the larger
        // `vars_to_bump` proxy. For theory conflicts the learned clause shape may differ
        // from Boolean conflicts, but the distinct-decision-level count of the actual
        // learned clause is the correct glue score and never exceeds the clause length.
        let lbd = self.compute_learnt_lbd_stamped();

        // Notify external heuristic of each conflict-involved variable with the
        // learned-clause LBD score.
        if let Some(ref ext) = self.config.external_branching
            && let Ok(mut h) = ext.lock()
        {
            for &var in &vars_to_bump {
                h.on_conflict_var_with_lbd(var, lbd);
            }
        }

        // Calculate backtrack level
        let backtrack_level = if self.learnt.len() == 1 {
            0
        } else {
            let mut max_level = 0;
            let mut max_idx = 1;
            for (i, &lit) in self.learnt.iter().enumerate().skip(1) {
                let level = self.trail.level(lit.var());
                if level > max_level {
                    max_level = level;
                    max_idx = i;
                }
            }
            self.learnt.swap(1, max_idx);
            max_level
        };

        // Trail-consistency invariants (debug builds only): the asserting
        // literal must sit strictly above the backtrack level so backtracking
        // unassigns it before it is re-asserted, and every other learned
        // literal must be at or below the backtrack level. See `analyze`.
        debug_assert!(
            self.learnt.is_empty()
                || !self.trail.is_assigned(self.learnt[0].var())
                || self.trail.level(self.learnt[0].var()) > backtrack_level,
            "theory: asserting literal must be above the backtrack level (uip level {}, backtrack {})",
            self.trail.level(self.learnt[0].var()),
            backtrack_level
        );
        debug_assert!(
            self.learnt
                .iter()
                .skip(1)
                .all(|lit| self.trail.level(lit.var()) <= backtrack_level),
            "theory: every non-asserting literal must be at or below the backtrack level"
        );

        // Snapshot the analysis-walk glue before the level statistics are
        // cleared: `seen_levels` at this point holds exactly cadical's
        // `levels` set (every decision level that contributed a literal to
        // the resolution walk), so `len - 1` is cadical's `glue` – the
        // statistic the restart EMAs are fed with (see
        // `Solver::analysis_walk_glue`).
        self.analysis_walk_glue =
            u32::try_from(self.seen_levels.len().saturating_sub(1)).unwrap_or(u32::MAX);

        // Reset the per-level `seen` statistics now that minimization (their
        // only consumer) has run (cadical `clear_analyzed_levels`).
        self.clear_analyzed_levels();

        (backtrack_level, self.learnt.clone())
    }

    /// Build a learned clause from a theory lemma that is *asserting* rather than
    /// *conflicting*: at least one of its literals is still unassigned while the
    /// rest are false, so the clause is unit under the current assignment and must
    /// propagate its open literal instead of driving 1-UIP resolution.
    ///
    /// The learned clause is the full, deduplicated theory lemma (dropping a
    /// literal without resolving it would be unsound – the lemma's validity does
    /// not carry over to any strict subset). It is returned with an unassigned
    /// literal at index 0 – the asserting / watch-0 literal that `learn_clause`
    /// will propagate – and the highest-level false literal at index 1 (watch 1).
    ///
    /// The backtrack level is the maximum decision level among the *assigned*
    /// (false) literals only; an unassigned literal's `VarInfo.level` is stale and
    /// must never be consulted. After backtracking to that level every false
    /// literal remains assigned false and index 0 remains unassigned, so the
    /// clause is unit and propagates index 0 – exactly the two-watched-literal
    /// contract `learn_clause` relies on. Computing the level from assigned
    /// literals alone is what keeps it in range with the live trail.
    fn analyze_theory_asserting_lemma(
        &mut self,
        conflict_lits: &[Lit],
    ) -> (u32, SmallVec<[Lit; 32]>) {
        self.learnt.clear();

        // Deduplicate by variable (a lemma may legitimately list a literal twice;
        // it must appear at most once in the learned clause). First occurrence
        // wins, preserving the theory's reported order.
        let mut seen_vars: SmallVec<[u32; 16]> = SmallVec::new();
        let mut asserting_idx: Option<usize> = None;
        let mut vars_to_bump: SmallVec<[Var; 16]> = SmallVec::new();
        for &lit in conflict_lits {
            let vi = lit.var().index() as u32;
            if seen_vars.contains(&vi) {
                continue;
            }
            seen_vars.push(vi);
            let idx = self.learnt.len();
            self.learnt.push(lit);
            if self.trail.lit_value(lit) == LBool::Undef {
                if asserting_idx.is_none() {
                    asserting_idx = Some(idx);
                }
            } else {
                // Assigned (false, or – for the defensive already-satisfied case –
                // true). Bump it so the heuristics still learn from the event.
                vars_to_bump.push(lit.var());
            }
        }

        // A lemma with no literals cannot arise from a real theory conflict; guard
        // by signalling a fundamental refutation (empty clause), matching the
        // all-level-0 convention of `analyze_theory_conflict`.
        if self.learnt.is_empty() {
            return (0, SmallVec::new());
        }

        // Place the (first) unassigned literal at index 0 as the asserting literal.
        // `any(... == Undef)` in the caller guarantees `asserting_idx` is `Some`.
        if let Some(ai) = asserting_idx {
            self.learnt.swap(0, ai);
        }

        // Bump activity for the falsified literals, mirroring 1-UIP conflict
        // analysis so branching heuristics still react to the near-conflict.
        self.vsids.bump_batch(&vars_to_bump);
        if self.config.use_chb_branching {
            self.chb.bump_batch(&vars_to_bump);
        }
        if self.config.use_lrb_branching {
            self.lrb.on_reason_batch(&vars_to_bump);
        }

        // Backtrack level = highest decision level among the *assigned* (false)
        // non-asserting literals; unassigned literals' stale levels are ignored.
        // Promote that literal to index 1 to serve as the second watch.
        let mut backtrack_level = 0u32;
        let mut second_idx = 0usize;
        for i in 1..self.learnt.len() {
            let lit = self.learnt[i];
            if self.trail.is_assigned(lit.var()) {
                let level = self.trail.level(lit.var());
                if level >= backtrack_level {
                    backtrack_level = level;
                    second_idx = i;
                }
            }
        }
        if second_idx >= 1 {
            self.learnt.swap(1, second_idx);
        }

        (backtrack_level, self.learnt.clone())
    }

    /// Extract the core of assumptions responsible for a *directly conflicting*
    /// assumption – one whose required polarity is already falsified on the trail
    /// when it is about to be asserted (index `conflict_idx`).
    ///
    /// The failed assumption's variable sits on the trail with the opposite phase,
    /// implied (transitively) by earlier assumptions through unit propagation.
    /// Seeding the analysis from that variable and resolving every antecedent back
    /// to its decision (assumption) roots yields *all* contributing assumptions,
    /// not merely the failed one. The previous implementation only ever returned
    /// the single failed assumption (its `seen`-based guard was never populated
    /// for this path), so a core such as `{a, b}` for
    /// `a ∧ b ∧ (¬a ∨ ¬b)` under `[a, b]` came back as just `{b}` – an incomplete,
    /// and therefore unsound-for-minimisation, core.
    pub(super) fn extract_assumption_core(
        &mut self,
        assumptions: &[Lit],
        conflict_idx: usize,
    ) -> Vec<Lit> {
        let failed = assumptions[conflict_idx];
        // Only assumptions asserted up to (and including) the failure can be on
        // the trail and thus contribute.
        self.analyze_final_core(&[failed], &[failed], &assumptions[..=conflict_idx])
    }

    /// Analyze a propagation conflict encountered while (or after) asserting the
    /// assumptions, returning every assumption in the unsat core.
    ///
    /// Seeds the analysis from the literals of the actual conflict clause and
    /// walks the implication graph back to the assumption (decision) roots. The
    /// previous implementation inspected only each assumption's *own* trail value
    /// and a never-populated `seen` array, so it systematically dropped
    /// assumptions that contributed only indirectly (through propagated literals)
    /// and, when it found nothing, fell back to returning *every* assumption –
    /// a safe but maximally imprecise core.
    pub(super) fn analyze_assumption_conflict(
        &mut self,
        assumptions: &[Lit],
        conflict: ClauseId,
    ) -> Vec<Lit> {
        let seed: SmallVec<[Lit; 32]> = match self.clauses.get(conflict) {
            Some(c) => c.lits.iter().copied().collect(),
            None => SmallVec::new(),
        };
        let core = self.analyze_final_core(&seed, &[], assumptions);
        if core.is_empty() {
            // Defensive fallback: never return an empty core for an UNSAT result;
            // conservatively blame all assumptions rather than lose soundness.
            return assumptions.to_vec();
        }
        core
    }

    /// Shared "analyze final" implementation (à la MiniSat `analyzeFinal`).
    ///
    /// Marks the `seed` literals' variables, walks the trail from newest to
    /// oldest resolving each marked propagated literal against its reason clause,
    /// and collects the assumption literals sitting at the decision roots. Any
    /// literals in `include` are unconditionally placed in the resulting core
    /// first (used to force the directly-failed assumption into its own core).
    ///
    /// Uses the solver's shared `seen` scratch buffer and restores it to all-false
    /// before returning, so it composes cleanly with the rest of conflict analysis.
    fn analyze_final_core(
        &mut self,
        seed: &[Lit],
        include: &[Lit],
        assumptions: &[Lit],
    ) -> Vec<Lit> {
        use crate::prelude::{HashMap, HashSet};

        // Map each assumption's variable to the assumption literal as it appears
        // on the trail (an assumption `a` is placed via `assign_decision(a)`, so
        // its variable identifies it). First occurrence wins on duplicates.
        let mut assumption_of: HashMap<usize, Lit> = HashMap::new();
        for &a in assumptions {
            assumption_of.entry(a.var().index()).or_insert(a);
        }

        let mut core: Vec<Lit> = Vec::new();
        let mut in_core: HashSet<usize> = HashSet::new();
        for &lit in include {
            if in_core.insert(lit.var().index()) {
                core.push(lit);
            }
        }

        // Seed the marks with every above-root seed variable.
        let mut touched: Vec<usize> = Vec::new();
        for &lit in seed {
            let var = lit.var();
            if self.trail.level(var) > 0 {
                let vi = var.index();
                if vi < self.seen.len() && !self.seen[vi] {
                    self.seen[vi] = true;
                    touched.push(vi);
                }
            }
        }

        // Walk the trail newest-to-oldest. `assignments()` is a snapshot copy so
        // the loop can freely borrow `self.clauses` / `self.trail` / `self.seen`.
        let trail_lits: Vec<Lit> = self.trail.assignments().to_vec();
        for &tlit in trail_lits.iter().rev() {
            let var = tlit.var();
            let vi = var.index();
            if vi >= self.seen.len() || !self.seen[vi] {
                continue;
            }
            self.seen[vi] = false;
            if self.trail.level(var) == 0 {
                continue;
            }
            match self.trail.reason(var) {
                Reason::Decision | Reason::Theory => {
                    // A decision root above level 0: if it is one of our
                    // assumptions, it belongs in the core.
                    if let Some(&alit) = assumption_of.get(&vi)
                        && in_core.insert(vi)
                    {
                        core.push(alit);
                    }
                }
                Reason::Propagation(cid) => {
                    // Resolve against the reason clause: mark every other literal's
                    // variable so its own antecedents are visited in turn.
                    let antecedents: SmallVec<[Var; 8]> = match self.clauses.get(cid) {
                        Some(clause) => clause
                            .lits
                            .iter()
                            .map(|l| l.var())
                            .filter(|&av| av != var)
                            .collect(),
                        None => SmallVec::new(),
                    };
                    for av in antecedents {
                        if self.trail.level(av) > 0 {
                            let avi = av.index();
                            if avi < self.seen.len() && !self.seen[avi] {
                                self.seen[avi] = true;
                                touched.push(avi);
                            }
                        }
                    }
                }
            }
        }

        // Restore the shared scratch buffer (any marks not cleared during the walk).
        for vi in touched {
            if vi < self.seen.len() {
                self.seen[vi] = false;
            }
        }

        core
    }

    /// Get the minimum backtrack level for a conflict
    pub(super) fn analyze_conflict_level(&self, conflict: ClauseId) -> u32 {
        let clause = match self.clauses.get(conflict) {
            Some(c) => c,
            None => return 0,
        };

        let mut min_level = u32::MAX;
        for lit in clause.lits.iter().copied() {
            let level = self.trail.level(lit.var());
            if level > 0 && level < min_level {
                min_level = level;
            }
        }

        if min_level == u32::MAX { 0 } else { min_level }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::trail::Trail;

    // ========  ========
    // Tests for compute_lbd_from_literals
    // ========  ========

    #[test]
    fn test_compute_lbd_all_same_level() {
        // Three literals whose vars are all assigned at level 3 → LBD = 1.
        let n = 4;
        let mut trail = Trail::new(n);
        // Level 0 is implicit; push 3 levels.
        trail.new_decision_level(); // → level 1
        trail.new_decision_level(); // → level 2
        trail.new_decision_level(); // → level 3

        let v0 = Var::new(0);
        let v1 = Var::new(1);
        let v2 = Var::new(2);
        trail.assign_decision(Lit::pos(v0));
        trail.assign_decision(Lit::pos(v1));
        trail.assign_decision(Lit::pos(v2));

        let lits = [Lit::pos(v0), Lit::neg(v1), Lit::pos(v2)];
        let lbd = compute_lbd_from_literals(&lits, &trail);
        assert_eq!(lbd, 1, "all literals at same level → LBD should be 1");
    }

    #[test]
    fn test_compute_lbd_distinct_levels() {
        // Three literals at levels 1, 2, 3 → LBD = 3.
        let n = 4;
        let mut trail = Trail::new(n);

        let v0 = Var::new(0);
        let v1 = Var::new(1);
        let v2 = Var::new(2);

        trail.new_decision_level(); // → level 1
        trail.assign_decision(Lit::pos(v0));

        trail.new_decision_level(); // → level 2
        trail.assign_decision(Lit::pos(v1));

        trail.new_decision_level(); // → level 3
        trail.assign_decision(Lit::pos(v2));

        let lits = [Lit::pos(v0), Lit::pos(v1), Lit::neg(v2)];
        let lbd = compute_lbd_from_literals(&lits, &trail);
        assert_eq!(lbd, 3, "literals at levels 1, 2, 3 → LBD should be 3");
    }

    #[test]
    fn test_compute_lbd_excludes_level_zero() {
        // Literals: one var at level 0 (unit prop), two at level 2 → LBD = 1.
        // Level-0 variables must not be counted.
        let n = 4;
        let mut trail = Trail::new(n);

        let v0 = Var::new(0); // Will be at level 0
        let v1 = Var::new(1); // Will be at level 2
        let v2 = Var::new(2); // Will be at level 2

        // Assign v0 at level 0 (root decision level, no new_decision_level call).
        trail.assign_decision(Lit::pos(v0));

        trail.new_decision_level(); // → level 1 (unused)
        trail.new_decision_level(); // → level 2
        trail.assign_decision(Lit::pos(v1));
        trail.assign_decision(Lit::pos(v2));

        let lits = [Lit::pos(v0), Lit::pos(v1), Lit::pos(v2)];
        let lbd = compute_lbd_from_literals(&lits, &trail);
        assert_eq!(
            lbd, 1,
            "level-0 var must be excluded; only level-2 vars count → LBD = 1"
        );
    }

    #[test]
    fn test_compute_lbd_mixed_duplicates_and_zero() {
        // v0 @ level 0 (excluded), v1 @ level 2, v2 @ level 4, v3 @ level 2 (duplicate)
        // → distinct non-zero levels: {2, 4} → LBD = 2.
        let n = 5;
        let mut trail = Trail::new(n);

        let v0 = Var::new(0);
        let v1 = Var::new(1);
        let v2 = Var::new(2);
        let v3 = Var::new(3);

        trail.assign_decision(Lit::pos(v0)); // level 0

        trail.new_decision_level(); // → 1
        trail.new_decision_level(); // → 2
        trail.assign_decision(Lit::pos(v1));
        trail.assign_decision(Lit::pos(v3));

        trail.new_decision_level(); // → 3
        trail.new_decision_level(); // → 4
        trail.assign_decision(Lit::pos(v2));

        let lits = [Lit::pos(v0), Lit::pos(v1), Lit::neg(v2), Lit::pos(v3)];
        let lbd = compute_lbd_from_literals(&lits, &trail);
        assert_eq!(lbd, 2, "levels {{2, 4}} → LBD = 2");
    }

    #[test]
    fn test_compute_lbd_empty_literals() {
        // Empty literal set → LBD = 0.
        let trail = Trail::new(0);
        let lits: [Lit; 0] = [];
        let lbd = compute_lbd_from_literals(&lits, &trail);
        assert_eq!(lbd, 0, "empty literal set → LBD = 0");
    }

    // ========  ========
    // Integration test: conflict analysis passes LBD to the external hook
    // ========  ========

    #[test]
    fn test_conflict_analysis_passes_lbd_to_hook() {
        // Solve PHP(3,2) – the same UNSAT formula used in the external_branching tests.
        // A ConflictLbdRecordingHeuristic records all LBD values received via
        // on_conflict_var_with_lbd.  After solving, assert:
        //   1. at least one call was made (conflicts happened)
        //   2. all recorded LBD values are > 0 (no degenerate LBD-0 passed through)
        use crate::solver::heuristic::BranchingHeuristic;
        use crate::{Solver, SolverConfig, SolverResult};
        use std::sync::{Arc, Mutex};

        struct ConflictLbdRecordingHeuristic {
            lbd_values: Arc<Mutex<Vec<u32>>>,
        }

        impl BranchingHeuristic for ConflictLbdRecordingHeuristic {
            fn select(&mut self, _candidates: &[Var], _scores: &[f64]) -> Option<Var> {
                None // always defer – VSIDS drives the solve
            }

            fn on_conflict_var_with_lbd(&mut self, _var: Var, lbd: u32) {
                self.lbd_values
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .push(lbd);
            }
        }

        let lbd_values: Arc<Mutex<Vec<u32>>> = Arc::new(Mutex::new(Vec::new()));
        let heuristic = Arc::new(Mutex::new(ConflictLbdRecordingHeuristic {
            lbd_values: Arc::clone(&lbd_values),
        }));

        let config = SolverConfig {
            external_branching: Some(heuristic),
            ..SolverConfig::default()
        };
        let mut solver = Solver::with_config(config);

        // PHP(3,2): 6 variables
        for _ in 0..6 {
            solver.new_var();
        }
        // Each pigeon must be in at least one hole
        solver.add_clause_dimacs(&[1, 2]);
        solver.add_clause_dimacs(&[3, 4]);
        solver.add_clause_dimacs(&[5, 6]);
        // At most one pigeon per hole
        solver.add_clause_dimacs(&[-1, -3]);
        solver.add_clause_dimacs(&[-1, -5]);
        solver.add_clause_dimacs(&[-3, -5]);
        solver.add_clause_dimacs(&[-2, -4]);
        solver.add_clause_dimacs(&[-2, -6]);
        solver.add_clause_dimacs(&[-4, -6]);

        let result = solver.solve();
        assert_eq!(result, SolverResult::Unsat, "PHP(3,2) must be UNSAT");

        let values = lbd_values.lock().unwrap_or_else(|e| e.into_inner());
        assert!(
            !values.is_empty(),
            "on_conflict_var_with_lbd must have been called at least once"
        );
        for &lbd in values.iter() {
            assert!(
                lbd > 0,
                "LBD passed to hook must be > 0 (got {lbd}); level-0 vars should be excluded"
            );
        }
    }

    #[test]
    fn test_lbd_matches_learned_clause_glue() {
        // The LBD passed to the hook must be the glue score of the ACTUAL learned
        // (1-UIP) clause – i.e. the distinct decision-level count of `self.learnt` –
        // NOT the distinct-level count of the larger `vars_to_bump` union.
        //
        // We solve a crafted UNSAT instance with clause deletion effectively disabled
        // so every learned clause persists. The hook records the set of LBD values it
        // receives; the solver stores `clause.lbd` (computed independently in
        // learn.rs::compute_lbd from the same final clause). Since a 1-UIP learned
        // clause never contains level-0 literals, the two definitions coincide, so the
        // set of hook LBDs must be a SUBSET of the stored learned-clause LBD set
        // (plus 1 for unit learned clauses, whose single literal sits at the current
        // decision level). The old `vars_to_bump` proxy would routinely report values
        // ABSENT from any stored clause's LBD, so a subset relation is decisive.
        use crate::solver::heuristic::BranchingHeuristic;
        use crate::{Solver, SolverConfig, SolverResult};
        use std::collections::BTreeSet;
        use std::sync::{Arc, Mutex};

        struct SetRecordingHeuristic {
            lbd_set: Arc<Mutex<BTreeSet<u32>>>,
        }

        impl BranchingHeuristic for SetRecordingHeuristic {
            fn select(&mut self, _candidates: &[Var], _scores: &[f64]) -> Option<Var> {
                None
            }

            fn on_conflict_var_with_lbd(&mut self, _var: Var, lbd: u32) {
                self.lbd_set
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .insert(lbd);
            }
        }

        let lbd_set: Arc<Mutex<BTreeSet<u32>>> = Arc::new(Mutex::new(BTreeSet::new()));
        let heuristic = Arc::new(Mutex::new(SetRecordingHeuristic {
            lbd_set: Arc::clone(&lbd_set),
        }));

        let config = SolverConfig {
            external_branching: Some(heuristic),
            // Disable clause deletion so every learned clause survives for inspection.
            clause_deletion_threshold: usize::MAX,
            ..SolverConfig::default()
        };
        let mut solver = Solver::with_config(config);

        // PHP(3,2): 6 variables, UNSAT, produces multi-level conflicts.
        for _ in 0..6 {
            solver.new_var();
        }
        solver.add_clause_dimacs(&[1, 2]);
        solver.add_clause_dimacs(&[3, 4]);
        solver.add_clause_dimacs(&[5, 6]);
        solver.add_clause_dimacs(&[-1, -3]);
        solver.add_clause_dimacs(&[-1, -5]);
        solver.add_clause_dimacs(&[-3, -5]);
        solver.add_clause_dimacs(&[-2, -4]);
        solver.add_clause_dimacs(&[-2, -6]);
        solver.add_clause_dimacs(&[-4, -6]);

        let result = solver.solve();
        assert_eq!(result, SolverResult::Unsat, "PHP(3,2) must be UNSAT");

        // Gather the LBD of every surviving learned clause from the solver's
        // internal database (these fields are crate-visible). Unit learned clauses
        // (len == 1) keep the default lbd 0 but their hook LBD is 1, so we add 1 for
        // every unit clause to the allowed set.
        let mut stored_lbds: BTreeSet<u32> = BTreeSet::new();
        for &cid in &solver.learned_clause_ids {
            if let Some(clause) = solver.clauses.get(cid) {
                if clause.lits.len() == 1 {
                    stored_lbds.insert(1);
                } else {
                    stored_lbds.insert(clause.lbd);
                }
            }
        }

        let hook_lbds = lbd_set.lock().unwrap_or_else(|e| e.into_inner());
        assert!(!hook_lbds.is_empty(), "hook must have received LBD values");

        // Decisive check: every LBD the hook reported is the glue score of a real
        // learned clause (subset relation). With the old vars_to_bump proxy this
        // would fail because vars_to_bump-derived LBDs exceed any stored clause's LBD.
        for &lbd in hook_lbds.iter() {
            assert!(
                stored_lbds.contains(&lbd),
                "hook LBD {lbd} must match the glue score of an actual learned clause; \
                 stored learned-clause LBDs = {stored_lbds:?}"
            );
        }
    }

    #[test]
    fn test_lbd_le_clause_size() {
        // The LBD of a learned clause can never exceed its literal count: each literal
        // contributes at most one distinct decision level. The fix computes LBD from
        // the actual learned clause, so this invariant must hold for the value handed
        // to the hook (unlike the old vars_to_bump proxy, which could exceed the clause
        // length). We verify it on every surviving learned clause and also confirm the
        // hook never reported an LBD larger than the largest learned clause.
        use crate::solver::heuristic::BranchingHeuristic;
        use crate::{Solver, SolverConfig, SolverResult};
        use std::sync::{Arc, Mutex};

        struct MaxRecordingHeuristic {
            max_lbd: Arc<Mutex<u32>>,
        }

        impl BranchingHeuristic for MaxRecordingHeuristic {
            fn select(&mut self, _candidates: &[Var], _scores: &[f64]) -> Option<Var> {
                None
            }

            fn on_conflict_var_with_lbd(&mut self, _var: Var, lbd: u32) {
                let mut m = self.max_lbd.lock().unwrap_or_else(|e| e.into_inner());
                if lbd > *m {
                    *m = lbd;
                }
            }
        }

        let max_lbd: Arc<Mutex<u32>> = Arc::new(Mutex::new(0));
        let heuristic = Arc::new(Mutex::new(MaxRecordingHeuristic {
            max_lbd: Arc::clone(&max_lbd),
        }));

        let config = SolverConfig {
            external_branching: Some(heuristic),
            clause_deletion_threshold: usize::MAX,
            ..SolverConfig::default()
        };
        let mut solver = Solver::with_config(config);

        // PHP(4,3): 12 variables, UNSAT, deeper search → larger learned clauses.
        for _ in 0..12 {
            solver.new_var();
        }
        // Each of 4 pigeons in at least one of 3 holes (pigeon p, hole h → var 3*(p-1)+h).
        solver.add_clause_dimacs(&[1, 2, 3]);
        solver.add_clause_dimacs(&[4, 5, 6]);
        solver.add_clause_dimacs(&[7, 8, 9]);
        solver.add_clause_dimacs(&[10, 11, 12]);
        // At most one pigeon per hole (for each hole h, no two pigeons share it).
        for hole in 0..3 {
            let h = hole + 1;
            let occupants = [h, h + 3, h + 6, h + 9];
            for i in 0..occupants.len() {
                for j in (i + 1)..occupants.len() {
                    solver.add_clause_dimacs(&[-occupants[i], -occupants[j]]);
                }
            }
        }

        let result = solver.solve();
        assert_eq!(result, SolverResult::Unsat, "PHP(4,3) must be UNSAT");

        // Invariant on every surviving learned clause: lbd <= number of literals.
        let mut max_learnt_len: usize = 0;
        for &cid in &solver.learned_clause_ids {
            if let Some(clause) = solver.clauses.get(cid) {
                let len = clause.lits.len();
                max_learnt_len = max_learnt_len.max(len);
                // Unit clauses store the default lbd 0; the invariant lbd <= len is
                // trivially satisfied. For len >= 2 the stored lbd was computed from
                // the clause literals and must not exceed the literal count.
                assert!(
                    clause.lbd as usize <= len,
                    "learned clause LBD {} exceeds its literal count {len}",
                    clause.lbd
                );
            }
        }

        let observed_max = *max_lbd.lock().unwrap_or_else(|e| e.into_inner());
        assert!(observed_max > 0, "hook must have received a positive LBD");
        assert!(
            observed_max as usize <= max_learnt_len,
            "max hook LBD {observed_max} must not exceed the largest learned clause length \
             {max_learnt_len} – proves LBD is computed from the learned clause, not vars_to_bump"
        );
    }

    // ========  ========
    // Regression: conflict clause whose literals all sit BELOW the current
    // decision level (an on-the-fly / theory-lemma-style clause).
    // ========  ========

    /// Root cause of the disjunctive-LIA wrong-UNSAT: `analyze` used to anchor
    /// its 1-UIP resolution at `trail.decision_level()`. When the conflict
    /// clause contains NO literal at that level (its highest literal is at a
    /// strictly lower level – as happens for theory reason/lemma clauses added
    /// mid-search), the pivot-level counter starts at 0, the trail walk
    /// underflows it, and the asserting literal comes out at or below the
    /// computed backtrack level. Backtracking then fails to unassign the
    /// asserting variable and the clause-learning step re-assigns it in place,
    /// corrupting the trail.
    ///
    /// We reconstruct exactly that state by hand and assert the fixed invariant:
    /// the asserting literal `learnt[0]` must live strictly above the backtrack
    /// level, so a subsequent backtrack unassigns it.
    #[test]
    fn test_analyze_conflict_below_current_level_is_asserting() {
        use crate::Solver;

        let mut solver = Solver::new();
        let v0 = solver.new_var();
        let v1 = solver.new_var();
        let v2 = solver.new_var();

        // Level 1: decide v0 = false.
        solver.trail.new_decision_level();
        solver.trail.assign_decision(Lit::neg(v0));

        // Level 1: propagate v1 = false with reason clause (¬v1 ∨ v0).
        // With v0 false, this clause forces ¬v1.
        let r1 = solver.clauses.add_learned([Lit::neg(v1), Lit::pos(v0)]);
        solver.trail.assign_propagation(Lit::neg(v1), r1);

        // Level 2: an UNRELATED decision v2 = true, lifting the trail's
        // decision level to 2 while the impending conflict lives entirely at
        // level 1.
        solver.trail.new_decision_level();
        solver.trail.assign_decision(Lit::pos(v2));

        assert_eq!(solver.trail.decision_level(), 2);

        // Conflict clause (v0 ∨ v1): both literals are FALSE (v0 = false,
        // v1 = false), so the clause is falsified. Its highest literal level is
        // 1 – strictly below the current decision level 2.
        let conflict = solver.clauses.add_learned([Lit::pos(v0), Lit::pos(v1)]);

        let (backtrack_level, learnt) = solver.analyze(conflict);

        assert!(!learnt.is_empty(), "learned clause must not be empty");

        let uip = learnt[0];
        let uip_level = solver.trail.level(uip.var());

        // The genuine conflict level is 1, so the asserting literal must be at
        // level 1 and the backtrack level must be strictly below it (0 here).
        assert_eq!(
            uip_level, 1,
            "asserting literal must sit at the true conflict level (1), not the \
             stale decision level (2)"
        );
        assert!(
            backtrack_level < uip_level,
            "backtrack level {backtrack_level} must be strictly below the asserting \
             literal's level {uip_level}; otherwise backtracking leaves the variable \
             assigned and clause learning corrupts the trail by re-assigning it"
        );

        // Every non-asserting literal must be unassigned or restorable at the
        // backtrack target (i.e. at a level <= backtrack_level).
        for &lit in learnt.iter().skip(1) {
            assert!(
                solver.trail.level(lit.var()) <= backtrack_level,
                "non-asserting literal at level {} exceeds backtrack level {backtrack_level}",
                solver.trail.level(lit.var())
            );
        }
    }

    /// End-to-end guard: a normal (current-level) conflict must be unaffected by
    /// the conflict-level anchoring – the asserting literal still sits at the
    /// current decision level and the backtrack level below it.
    #[test]
    fn test_analyze_normal_current_level_conflict_unaffected() {
        use crate::Solver;

        let mut solver = Solver::new();
        let v0 = solver.new_var();
        let v1 = solver.new_var();
        let v2 = solver.new_var();

        // Level 1: decide v0 = true.
        solver.trail.new_decision_level();
        solver.trail.assign_decision(Lit::pos(v0));

        // Level 2: decide v1 = true.
        solver.trail.new_decision_level();
        solver.trail.assign_decision(Lit::pos(v1));

        // Level 2: propagate v2 = true with reason (¬v1 ∨ v2).
        let r = solver.clauses.add_learned([Lit::neg(v1), Lit::pos(v2)]);
        solver.trail.assign_propagation(Lit::pos(v2), r);

        // Conflict clause (¬v0 ∨ ¬v1 ∨ ¬v2): all three literals false at their
        // levels; the highest is v2/v1 at level 2 == current decision level.
        let conflict = solver
            .clauses
            .add_learned([Lit::neg(v0), Lit::neg(v1), Lit::neg(v2)]);

        let (backtrack_level, learnt) = solver.analyze(conflict);
        assert!(!learnt.is_empty());
        let uip_level = solver.trail.level(learnt[0].var());
        assert_eq!(uip_level, 2, "asserting literal at current level");
        assert!(
            backtrack_level < uip_level,
            "backtrack level {backtrack_level} must be below asserting level {uip_level}"
        );
    }

    // ========  ========
    // Regression: theory conflict clause containing an UNASSIGNED literal.
    //
    // The MBQI / quantifier-instantiation path builds its conflict clause from a
    // per-atom polarity map that is not pruned on every SAT backtrack (notably a
    // restart). It can therefore hand `analyze_theory_conflict` a "conflict" whose
    // clause still lists a variable that has since been unassigned – its
    // `VarInfo.level` left stale at the level it last held. Two OxiZ z3-parity
    // reproducers (`injective_unsat.smt2`, `nested_quantifiers.smt2`) drove
    // exactly this and panicked at the theory trail-consistency `debug_assert`
    // ("asserting literal must be above the backtrack level"): the stale level
    // became a bogus `current_level`, the 1-UIP counter was charged for a literal
    // absent from the trail, and the asserting literal was duplicated at the
    // backtrack level (`backtrack_level == uip_level`). In release the same trail
    // corruption produced a wrong top-level UNSAT on a SAT instance.
    //
    // The fix recognizes such a clause as an *asserting theory lemma* (unit under
    // the current assignment) and propagates its one open literal, keeping the
    // whole (valid) lemma. These tests reconstruct the exact trail shape by hand.
    // ========  ========

    #[test]
    fn test_theory_conflict_stale_unassigned_literal_is_asserting() {
        use crate::Solver;

        let mut solver = Solver::new();
        let v0 = solver.new_var(); // becomes a false literal @ level 3
        let v1 = solver.new_var(); // the stale, now-unassigned literal
        let v2 = solver.new_var(); // becomes a false literal @ level 1

        // Level 1: decide ¬v2, so the positive literal v2 is FALSE at level 1.
        solver.trail.new_decision_level();
        solver.trail.assign_decision(Lit::neg(v2));

        // Levels 2 and 3.
        solver.trail.new_decision_level(); // level 2
        solver.trail.new_decision_level(); // level 3
        // Propagate ¬v0 at level 3, so the positive literal v0 is FALSE at level 3.
        let r = solver.clauses.add_learned([Lit::neg(v0), Lit::pos(v2)]);
        solver.trail.assign_propagation(Lit::neg(v0), r);

        // Levels 4 and 5: assign v1, then backtrack it away so it becomes
        // UNASSIGNED while `VarInfo.level` stays stale at 5.
        solver.trail.new_decision_level(); // level 4
        solver.trail.new_decision_level(); // level 5
        solver.trail.assign_decision(Lit::pos(v1));
        assert_eq!(solver.trail.decision_level(), 5);

        solver.trail.backtrack_to(3);
        assert_eq!(solver.trail.decision_level(), 3);
        assert!(!solver.trail.is_assigned(v1), "v1 must be unassigned");
        // `Trail::backtrack_to_with_callback` now resets the full `VarInfo`
        // (level included) on unassignment, so an unassigned variable reports
        // level 0 rather than its pre-backtrack level. Previously `level` was
        // left stale (5 here), which forced `analyze_theory_conflict` to route
        // unassigned-literal lemmas through a dedicated handler keyed on
        // `lit_value == Undef`; that routing still applies, but the stale level
        // is no longer there to mislead a naive level-based computation.
        assert_eq!(
            solver.trail.level(v1),
            0,
            "v1's level must be reset to 0 after backtrack (no longer stale)"
        );

        // Theory conflict clause: all three are meant to be the (false) clause
        // literals, but v1 is now unassigned. Pre-fix this panicked / corrupted.
        let conflict_lits = [Lit::pos(v0), Lit::pos(v1), Lit::pos(v2)];
        let (backtrack_level, learnt) = solver.analyze_theory_conflict(&conflict_lits);

        assert!(!learnt.is_empty(), "learned clause must not be empty");

        // The asserting literal (index 0) is the unassigned one – the clause is
        // unit and will propagate it – so backtracking never leaves it assigned.
        assert_eq!(
            learnt[0].var(),
            v1,
            "the unassigned literal must be the asserting (index-0) literal"
        );
        assert!(
            !solver.trail.is_assigned(learnt[0].var()),
            "the asserting literal must be unassigned"
        );

        // Backtrack level is the max level among the *assigned* (false) literals –
        // never the unassigned literal's stale level 5.
        assert_eq!(
            backtrack_level, 3,
            "backtrack level must be the max assigned (false) level, not the stale 5"
        );

        // Soundness: the full theory lemma is preserved – every original literal is
        // present exactly once, none dropped (dropping would strengthen the clause
        // and could be unsound).
        let mut got: Vec<Lit> = learnt.to_vec();
        got.sort_by_key(|l| l.code());
        let mut want = vec![Lit::pos(v0), Lit::pos(v1), Lit::pos(v2)];
        want.sort_by_key(|l| l.code());
        assert_eq!(
            got, want,
            "learned clause must be the full deduplicated lemma"
        );

        // Every non-asserting literal is assigned and at a level <= backtrack level,
        // so after backtracking the clause stays unit on the asserting literal.
        for &lit in learnt.iter().skip(1) {
            assert!(
                solver.trail.is_assigned(lit.var()),
                "non-asserting literal {lit:?} must be assigned"
            );
            assert!(
                solver.trail.level(lit.var()) <= backtrack_level,
                "non-asserting literal level {} exceeds backtrack level {backtrack_level}",
                solver.trail.level(lit.var())
            );
        }
    }

    #[test]
    fn test_theory_conflict_two_unassigned_literals_no_panic() {
        // Defensive: a lemma with more than one open literal is not unit, but the
        // handler must still produce a valid, non-corrupting result (an unassigned
        // asserting literal, a backtrack level drawn only from assigned literals).
        use crate::Solver;

        let mut solver = Solver::new();
        let v0 = solver.new_var(); // false @ level 2
        let v1 = solver.new_var(); // unassigned, stale level 4
        let v2 = solver.new_var(); // unassigned, stale level 3

        // Level 1 (unused), level 2: v0 false via a decision on ¬v0.
        solver.trail.new_decision_level(); // 1
        solver.trail.new_decision_level(); // 2
        solver.trail.assign_decision(Lit::neg(v0));

        // Levels 3, 4: assign v2 then v1, then backtrack both away (stale levels).
        solver.trail.new_decision_level(); // 3
        solver.trail.assign_decision(Lit::pos(v2));
        solver.trail.new_decision_level(); // 4
        solver.trail.assign_decision(Lit::pos(v1));

        solver.trail.backtrack_to(2);
        assert_eq!(solver.trail.decision_level(), 2);
        assert!(!solver.trail.is_assigned(v1));
        assert!(!solver.trail.is_assigned(v2));

        let conflict_lits = [Lit::pos(v0), Lit::pos(v1), Lit::pos(v2)];
        let (backtrack_level, learnt) = solver.analyze_theory_conflict(&conflict_lits);

        // No panic; the asserting literal is one of the unassigned vars; the
        // backtrack level is the only assigned literal's level (2), never a stale
        // level (3 or 4).
        assert!(!learnt.is_empty());
        assert!(
            !solver.trail.is_assigned(learnt[0].var()),
            "asserting literal must be unassigned"
        );
        assert_eq!(
            backtrack_level, 2,
            "backtrack level must come from the single assigned literal (level 2)"
        );
        // The full lemma is preserved (all three vars, once each).
        let vars: std::collections::BTreeSet<u32> =
            learnt.iter().map(|l| l.var().index() as u32).collect();
        assert_eq!(vars.len(), 3, "all three distinct vars must be present");
    }

    #[test]
    fn test_theory_conflict_all_false_still_uses_1uip() {
        // Regression guard: a genuine, fully-falsified theory conflict must keep
        // going through the 1-UIP path (asserting literal strictly above the
        // backtrack level), unaffected by the unassigned-literal branch.
        use crate::Solver;

        let mut solver = Solver::new();
        let v0 = solver.new_var();
        let v1 = solver.new_var();
        let v2 = solver.new_var();

        // Level 1: decide v0 = true.
        solver.trail.new_decision_level();
        solver.trail.assign_decision(Lit::pos(v0));
        // Level 2: decide v1 = true.
        solver.trail.new_decision_level();
        solver.trail.assign_decision(Lit::pos(v1));
        // Level 2: propagate v2 = true with reason (¬v1 ∨ v2).
        let r = solver.clauses.add_learned([Lit::neg(v1), Lit::pos(v2)]);
        solver.trail.assign_propagation(Lit::pos(v2), r);

        // Conflict clause (¬v0 ∨ ¬v1 ∨ ¬v2): every literal is FALSE (assigned).
        let conflict_lits = [Lit::neg(v0), Lit::neg(v1), Lit::neg(v2)];
        let (backtrack_level, learnt) = solver.analyze_theory_conflict(&conflict_lits);

        assert!(!learnt.is_empty());
        let uip_level = solver.trail.level(learnt[0].var());
        assert!(
            solver.trail.is_assigned(learnt[0].var()),
            "for an all-false conflict the 1-UIP asserting literal is assigned"
        );
        assert!(
            uip_level > backtrack_level,
            "1-UIP asserting literal level {uip_level} must be strictly above the \
             backtrack level {backtrack_level}"
        );
    }
}

#[cfg(test)]
mod stamped_lbd_equivalence {
    use super::*;

    /// The stamped hot-path LBD must agree with the reference
    /// `contains`-scan implementation on *every* input, including repeated
    /// calls (generation-counter reuse), level-0 literals, duplicate
    /// literals, and level indices at/above the table's initial size.
    #[test]
    fn stamped_lbd_matches_reference_over_randomized_calls() {
        // Deterministic LCG so the property is reproducible.
        let mut state = 0x2545F4914F6CDD1Du64;
        let mut next = move || {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            state >> 33
        };

        for case in 0..200 {
            let n_vars = 2 + (next() % 40) as usize;
            let mut trail = Trail::new(n_vars);
            // Random number of decision levels; vars assigned in order.
            let n_levels = 1 + (next() % (n_vars as u64 + 3)) as usize;
            for _ in 0..n_levels {
                trail.new_decision_level();
                let vars_here = next() % 3;
                for k in 0..vars_here {
                    let v = Var::new(((next() % n_vars as u64) as u32).min(n_vars as u32 - 1));
                    let lit = if k % 2 == 0 { Lit::pos(v) } else { Lit::neg(v) };
                    if !trail.is_assigned(v) {
                        trail.assign_decision(lit);
                    }
                }
            }
            // NOTE: `n_levels` can exceed the number of *populated* levels;
            // assigning a literal at level L makes `trail.level` return L for
            // its var. Vars never assigned report level 0 and are excluded by
            // both implementations.

            let mut level_marks: Vec<u32> = Vec::new();
            let mut mark: u32 = 0;
            for _ in 0..5 {
                // Interleave calls of varying sizes; the stamp must survive
                // reuse across calls with overlapping level sets.
                let n_lits = 1 + (next() % 24) as usize;
                let mut lits: SmallVec<[Lit; 32]> = SmallVec::new();
                for _ in 0..n_lits {
                    let v = Var::new((next() % n_vars as u64) as u32);
                    let lit = if next() % 2 == 0 {
                        Lit::pos(v)
                    } else {
                        Lit::neg(v)
                    };
                    lits.push(lit);
                    // Occasional duplicate literal (allowed in raw walks).
                    if next() % 4 == 0 {
                        lits.push(lit);
                    }
                }
                let reference = compute_lbd_from_literals(&lits, &trail);
                let stamped = compute_lbd_stamped(&mut level_marks, &mut mark, &lits, &trail);
                assert_eq!(
                    reference, stamped,
                    "case {case}: stamped LBD diverged from reference \
                     (n_vars={n_vars}, lits={n_lits})"
                );
            }
        }
    }

    /// The generation counter must be reusable after `u32` wraparound: the
    /// wrapped value is simply a fresh id, and correctness never depends on
    /// ordering.
    #[test]
    fn stamped_lbd_survives_mark_wraparound() {
        let n = 3;
        let mut trail = Trail::new(n);
        trail.new_decision_level();
        trail.assign_decision(Lit::pos(Var::new(0)));
        trail.new_decision_level();
        trail.assign_decision(Lit::pos(Var::new(1)));

        let lits = [Lit::pos(Var::new(0)), Lit::pos(Var::new(1))];
        let mut level_marks: Vec<u32> = vec![0; 2];
        let mut mark = u32::MAX;
        let first = compute_lbd_stamped(&mut level_marks, &mut mark, &lits, &trail);
        assert_eq!(first, 2);
        let second = compute_lbd_stamped(&mut level_marks, &mut mark, &lits, &trail);
        assert_eq!(second, 2, "recount after wraparound must still be 2");
    }
}
