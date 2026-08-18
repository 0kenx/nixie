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
    fn analyze_mark_antecedent(
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
            // LRAT: a level-0 (fixed) antecedent. With the level-0 flush every
            // level-0 literal is a unit with an id, so reference it directly
            // (cadical's `analyze_literal` level-0 branch). `lit` is FALSE; its
            // true form `¬lit` is the unit.
            self.seen[var.index()] = true;
            self.unit_chain
                .push(self.proof_unit_id(lit.negate().to_dimacs()));
        }
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

    pub(super) fn analyze(&mut self, conflict: ClauseId) -> (u32, SmallVec<[Lit; 16]>) {
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
                // Promote to Core if LBD ≤ 2 (GLUE clause)
                if self.clauses.get(reason_clause).is_some_and(|c| c.lbd <= 2) {
                    self.clauses.promote_to_core(reason_clause);
                }
                // Bump clause activity (MapleSAT-style)
                self.clauses
                    .bump_activity(reason_clause, self.clause_bump_increment);
            }

            let Some(clause) = self.clauses.get(reason_clause) else {
                break;
            };
            // Snapshot the literals so the shared marking helper may take
            // `&mut self` (reason clauses are short – inline SmallVec copy).
            let antecedent_lits: SmallVec<[Lit; 8]> = clause.lits.iter().copied().collect();
            for lit in antecedent_lits {
                // When resolving a *reason* clause (`p` is Some), the propagated
                // literal `p` is the one being resolved out: it is TRUE on the trail
                // and must NOT be added to the learned clause. We skip it BY VALUE
                // rather than by a fixed index, because binary-implication-graph
                // propagation (propagate.rs) records the reason without moving the
                // implied literal to index 0 – so the propagated literal may sit at
                // index 1. Skipping index 0 positionally would drop the false
                // antecedent at index 0, producing over-strong (unsound) learned
                // clauses. For the initial conflict clause `p` is None, so every
                // literal is processed.
                if p == Some(lit) {
                    continue;
                }
                self.analyze_mark_antecedent(lit, current_level, &mut counter, &mut vars_to_bump);
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
                        for &lit in &tail {
                            self.analyze_mark_antecedent(
                                lit,
                                current_level,
                                &mut counter,
                                &mut vars_to_bump,
                            );
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

        // Batch bump all collected variables at once (single heap rebuild)
        self.vsids.bump_batch(&vars_to_bump);
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
        if self.config.use_vmtf {
            // Sort by bump timestamp (cadical MSORT on `analyzed_bumped_rank`)
            // to preserve relative queue order of bumped variables.
            vars_to_bump.sort_by_key(|&v| self.vmtf.activity(v));
            for &v in &vars_to_bump {
                self.vmtf.bump(v, |v| self.trail.is_assigned(v));
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

        // Minimize learnt clause using recursive resolution (the chain-extending
        // LRAT port when LRAT is on; the plain recursive minimization otherwise).
        self.minimize_learnt_clause();

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
        let lbd = compute_lbd_from_literals(&self.learnt, &self.trail);

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

        // Apply chronological backtracking if enabled
        let backtrack_level = self.chrono_backtrack.compute_backtrack_level(
            &self.trail,
            &self.learnt,
            uip_level,
            assertion_level,
        );

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
        let mut order: SmallVec<[Lit; 16]> = self.learnt[1..].iter().copied().collect();
        order.sort_by_key(|&l| self.trail.trail_index(l.var()));

        let mut kept: SmallVec<[Lit; 16]> = SmallVec::new();
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
    fn minimize_literal_plain(&mut self, lit: Lit, depth: u32) -> bool {
        const MINIMIZE_DEPTH_LIMIT: u32 = 100;
        let var = lit.var();
        let f = self.mf_get(var);
        let level = self.trail.level(var);
        if level == 0 || (f & MF_REMOVABLE) != 0 || (f & MF_KEEP) != 0 {
            return true;
        }
        let reason = self.trail.reason(var);
        let no_reason = !matches!(reason, Reason::Propagation(_));
        // cadical compares against the conflict level (`v.level == level`),
        // not the current decision level: under chronological backtracking
        // the two differ, and treating a conflict-level literal as removable
        // resolves the UIP's own level through the clause – over-strengthening
        // it into a clause resolution does not derive (false UNSAT on
        // `circuit_48in64out…dist128_seed1`, SAT verified by CaDiCaL).
        if no_reason || (f & MF_POISON) != 0 || level == self.current_conflict_level {
            return false;
        }
        // Don Knuth's gate (cadical `!depth && l.seen.count < 2`): at the top
        // of the recursion, a literal whose level contributed only one seen
        // literal (itself) cannot be resolved out through its own level.
        if depth == 0 {
            let lv = level as usize;
            if lv < self.seen_level_count.len() && self.seen_level_count[lv] < 2 {
                return false;
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
                return false;
            }
        }
        if depth > MINIMIZE_DEPTH_LIMIT {
            return false;
        }
        let Reason::Propagation(cid) = reason else {
            return false;
        };
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
        for &other in others.iter() {
            if !self.minimize_literal_plain(other.negate(), depth + 1) {
                res = false;
                break;
            }
        }
        if res {
            self.mf_set(var, MF_REMOVABLE);
        } else {
            self.mf_set(var, MF_POISON);
        }
        // Record the var so `clear_minimize_flags` can reset its flags; a
        // leaked REMOVABLE/POISON bit across conflicts would poison later
        // decisions (same bookkeeping `minimize_literal_lrat` does).
        self.lrat_minimized.push(var.index() as i32);
        res
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
    fn clear_minimize_flags(&mut self) {
        let minimized: SmallVec<[i32; 32]> = self.lrat_minimized.drain(..).collect();
        for vi in minimized {
            let var = Var::new(vi as u32);
            self.mf_unset(var, MF_REMOVABLE | MF_POISON | MF_ADDED);
        }
        let learnt_vars: SmallVec<[Var; 16]> = self.learnt.iter().map(|l| l.var()).collect();
        for var in learnt_vars {
            self.mf_unset(var, MF_KEEP);
        }
        let analyzed: SmallVec<[i32; 32]> = self.unit_analyzed.drain(..).collect();
        for vi in analyzed {
            let var = Var::new(vi as u32);
            self.mf_unset(var, MF_SEEN);
        }
    }

    /// We use a recursive check: a literal l is redundant if its reason clause
    /// contains only literals that are either:
    /// - Already in the learnt clause (marked as seen)
    /// - At decision level 0 (always true in the learned clause context)
    /// - Themselves redundant (recursive check)
    ///
    /// This also performs clause strengthening by checking for stronger implications
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
            let mut order: SmallVec<[Lit; 16]> = self.learnt[1..].iter().copied().collect();
            order.sort_by_key(|&l| self.trail.trail_index(l.var()));

            let mut kept: SmallVec<[Lit; 16]> = SmallVec::new();
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
    ) -> (u32, SmallVec<[Lit; 16]>) {
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
                // (Snapshot: `note_seen_level` takes `&mut self` below.)
                let reason_lits: SmallVec<[Lit; 8]> = clause.lits.iter().copied().collect();
                for &lit in &reason_lits {
                    if lit == current_lit {
                        continue;
                    }
                    let reason_var = lit.var();
                    let level = self.trail.level(reason_var);

                    if !self.seen[reason_var.index()] && level > 0 {
                        self.seen[reason_var.index()] = true;
                        vars_to_bump.push(reason_var);
                        self.note_seen_level(reason_var, level);

                        if level == current_level {
                            counter += 1;
                        } else {
                            // Add the literal itself to the learned clause
                            self.learnt.push(lit);
                        }
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

        // Minimize
        self.minimize_learnt_clause();

        // Compute the real LBD from the FINAL learned clause literals (post-minimization),
        // matching the standard Glucose definition rather than using the larger
        // `vars_to_bump` proxy. For theory conflicts the learned clause shape may differ
        // from Boolean conflicts, but the distinct-decision-level count of the actual
        // learned clause is the correct glue score and never exceeds the clause length.
        let lbd = compute_lbd_from_literals(&self.learnt, &self.trail);

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
    ) -> (u32, SmallVec<[Lit; 16]>) {
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
        let seed: SmallVec<[Lit; 16]> = match self.clauses.get(conflict) {
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
