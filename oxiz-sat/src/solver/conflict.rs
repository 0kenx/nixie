//! Conflict analysis, clause minimization, and assumption handling

use super::*;
use smallvec::SmallVec;

/// Compute LBD (Literals per Block Distance / "glue" score) from a set of clause literals.
///
/// LBD = number of distinct decision levels among the literals, excluding level 0.
/// Level-0 literals are excluded because they are consequences of unit propagation at the
/// root level and are always true — they do not contribute to the "block distance" that
/// measures how spread across the search tree a learned clause is.
///
/// This is an O(n) computation with no heap allocation in the common case
/// (`SmallVec<[u32; 32]>` avoids a heap allocation for clauses up to 32 distinct decision
/// levels, which covers the overwhelming majority of real CDCL learned clauses).
///
/// This is the standard Glucose/MiniSat LBD definition applied to the **actual learned
/// (1-UIP) clause literals**, so the value it returns satisfies `lbd <= literals.len()`.
/// It is a pure function (no shared scratch state) so it can be called at sites where a
/// `&mut self` borrow of the solver is unavailable — in particular after `self.learnt`
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
        // *on the fly* — theory reason/lemma clauses in CDCL(T), or clauses
        // encountered after chronological backtracking — can be falsified at a
        // level strictly BELOW the current decision level. Running 1-UIP
        // resolution relative to `decision_level()` in that situation is
        // unsound for backtracking: the conflict clause contributes NO literal
        // at the pivot level, so the current-level counter starts at 0, the
        // trail walk underflows it, and the asserting literal ends up at a level
        // <= the computed backtrack level. Backtracking then fails to unassign
        // that variable and `learn_clause` re-assigns it in place — corrupting
        // the trail (observed as a wrong top-level UNSAT on disjunctive LIA).
        // Anchoring the analysis at the genuine conflict level restores the
        // 1-UIP invariant (asserting literal strictly above the backtrack
        // level) for both the normal and the on-the-fly-clause cases.
        let current_level = {
            let mut lvl = 0;
            if let Some(c) = self.clauses.get(conflict) {
                for &lit in &c.lits {
                    let l = self.trail.level(lit.var());
                    if l > lvl {
                        lvl = l;
                    }
                }
            }
            lvl
        };

        // A conflict whose genuine level is 0 has EVERY literal falsified under
        // unconditional (level-0) assignments — a root-level refutation, so the
        // instance is UNSAT. This can happen above decision level 0 when an
        // on-the-fly clause (a theory reason/lemma clause) is added already
        // fully falsified at the root: the watched-literal scheme only visits it
        // on the next propagation, which may run at a higher decision level.
        // There is no asserting literal to learn, so we return an empty clause
        // (backtrack level 0) — the caller treats an empty learned clause as
        // fundamental UNSAT, exactly as `analyze_theory_conflict` already does.
        // Fabricating a 1-UIP clause here instead would resolve the trail's
        // bottom literal into a spurious unit clause that contradicts a
        // level-0 fact, corrupting the trail (the earlier `decision_level()`
        // fallback did precisely this, tripping the trail-consistency assert).
        if current_level == 0 {
            self.learnt.clear();
            return (0, SmallVec::new());
        }

        // Reset seen flags
        for s in &mut self.seen {
            *s = false;
        }

        // Collect variables to bump in batch (avoids repeated heap sift-ups)
        let mut vars_to_bump: SmallVec<[Var; 32]> = SmallVec::new();

        let mut reason_clause = conflict;

        while let Some(clause) = self.clauses.get(reason_clause) {
            // Process reason clause (must exist, as it's either conflict or a propagation reason)
            let is_learned = clause.learned;

            // Record clause usage for tier promotion and bump activity (if it's a learned clause)
            if is_learned && let Some(clause_mut) = self.clauses.get_mut(reason_clause) {
                clause_mut.record_usage();
                // Promote to Core if LBD ≤ 2 (GLUE clause)
                if clause_mut.lbd <= 2 {
                    clause_mut.promote_to_core();
                }
                // Bump clause activity (MapleSAT-style)
                clause_mut.activity += self.clause_bump_increment;
            }

            let Some(clause) = self.clauses.get(reason_clause) else {
                break;
            };
            for &lit in &clause.lits {
                // When resolving a *reason* clause (`p` is Some), the propagated
                // literal `p` is the one being resolved out: it is TRUE on the trail
                // and must NOT be added to the learned clause. We skip it BY VALUE
                // rather than by a fixed index, because binary-implication-graph
                // propagation (propagate.rs) records the reason without moving the
                // implied literal to index 0 — so the propagated literal may sit at
                // index 1. Skipping index 0 positionally would drop the false
                // antecedent at index 0, producing over-strong (unsound) learned
                // clauses. For the initial conflict clause `p` is None, so every
                // literal is processed.
                if p == Some(lit) {
                    continue;
                }
                let var = lit.var();
                let level = self.trail.level(var);

                if !self.seen[var.index()] && level > 0 {
                    self.seen[var.index()] = true;
                    // Collect variable for batch bumping instead of individual bumps
                    vars_to_bump.push(var);

                    if level == current_level {
                        counter += 1;
                    } else {
                        // Add the literal itself (not negated) to the learned clause.
                        // The conflict clause has all literals FALSE. To prevent this
                        // conflict, we need at least one of these literals to become TRUE.
                        self.learnt.push(lit);
                    }
                }
            }

            // Find next literal to analyze
            let mut current_lit = Lit::from_code(0); // sentinel default
            let mut found_next = false;
            loop {
                if index == 0 {
                    // Guard against underflow: this should not happen in a
                    // well-formed conflict, but theory-conflict injection can
                    // occasionally produce a degenerate state.  Break out to
                    // avoid a usize overflow panic.
                    break;
                }
                index -= 1;
                current_lit = self.trail.assignments()[index];
                p = Some(current_lit);
                if self.seen[current_lit.var().index()] {
                    found_next = true;
                    break;
                }
            }
            if !found_next {
                break;
            }

            counter -= 1;
            if counter == 0 {
                break;
            }

            let var = current_lit.var();
            match self.trail.reason(var) {
                Reason::Propagation(c) => reason_clause = c,
                _ => break,
            }
        }

        // Batch bump all collected variables at once (single heap rebuild)
        self.vsids.bump_batch(&vars_to_bump);
        self.chb.bump_batch(&vars_to_bump);
        self.lrb.on_reason_batch(&vars_to_bump);

        // Set asserting literal (p is guaranteed to be Some at this point)
        if let Some(lit) = p {
            self.learnt[0] = lit.negate();
        }

        // Minimize learnt clause using recursive resolution
        self.minimize_learnt_clause();

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

        // Calculate assertion level (traditional backtrack level)
        let assertion_level = if self.learnt.len() == 1 {
            0
        } else {
            // Find second highest level
            let mut max_level = 0;
            let mut max_idx = 1;
            for (i, &lit) in self.learnt.iter().enumerate().skip(1) {
                let level = self.trail.level(lit.var());
                if level > max_level {
                    max_level = level;
                    max_idx = i;
                }
            }
            // Move second watch to position 1
            self.learnt.swap(1, max_idx);
            max_level
        };

        // Apply chronological backtracking if enabled
        let backtrack_level = self.chrono_backtrack.compute_backtrack_level(
            &self.trail,
            &self.learnt,
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

        (backtrack_level, self.learnt.clone())
    }

    /// Minimize the learned clause by removing redundant literals
    ///
    /// A literal can be removed if it is implied by the remaining literals.
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

        let original_len = self.learnt.len();

        // Mark all literals in the learned clause as "in clause"
        // We use analyze_stack to track literals to check
        self.analyze_stack.clear();

        // Phase 1: Basic minimization - remove redundant literals
        let mut j = 1; // Write position
        for i in 1..self.learnt.len() {
            let lit = self.learnt[i];
            if self.lit_is_redundant(lit) {
                // Skip this literal (it's redundant)
            } else {
                // Keep this literal
                self.learnt[j] = lit;
                j += 1;
            }
        }
        self.learnt.truncate(j);

        // Phase 2: Clause strengthening - check for self-subsuming resolution
        // If the clause contains both l and ~l' where l' is in a reason clause,
        // we might be able to strengthen the clause
        self.strengthen_learnt_clause();

        // Track minimization statistics
        let final_len = self.learnt.len();
        if final_len < original_len {
            self.stats.minimizations += 1;
            self.stats.literals_removed += (original_len - final_len) as u64;
        }
    }

    /// Strengthen the learned clause using on-the-fly self-subsuming resolution
    pub(super) fn strengthen_learnt_clause(&mut self) {
        if self.learnt.len() <= 2 {
            return;
        }

        // Check each literal to see if we can strengthen by resolution
        let mut j = 1;
        for i in 1..self.learnt.len() {
            let lit = self.learnt[i];
            let var = lit.var();

            // Check if this literal can be strengthened
            if let Reason::Propagation(reason_id) = self.trail.reason(var)
                && let Some(reason_clause) = self.clauses.get(reason_id)
                && reason_clause.lits.len() == 2
            {
                // Binary reason: one literal is lit, the other is the implied literal
                let other_lit = if reason_clause.lits[0] == lit.negate() {
                    reason_clause.lits[1]
                } else if reason_clause.lits[1] == lit.negate() {
                    reason_clause.lits[0]
                } else {
                    // Keep the literal
                    self.learnt[j] = lit;
                    j += 1;
                    continue;
                };

                // If other_lit is already in the learned clause at level 0,
                // we can remove lit
                if self.trail.level(other_lit.var()) == 0 && self.seen[other_lit.var().index()] {
                    // Skip this literal (strengthened)
                    continue;
                }
            }

            // Keep this literal
            self.learnt[j] = lit;
            j += 1;
        }
        self.learnt.truncate(j);
    }

    /// Check if a literal is redundant in the learned clause
    ///
    /// A literal is redundant if its reason clause only contains:
    /// - Literals marked as seen (in the learned clause)
    /// - Literals at decision level 0
    /// - Literals that are themselves redundant (recursive)
    pub(super) fn lit_is_redundant(&mut self, lit: Lit) -> bool {
        let var = lit.var();

        // Decision variables and theory propagations are not redundant
        let reason = match self.trail.reason(var) {
            Reason::Decision => return false,
            Reason::Theory => return false, // Theory propagations can't be minimized
            Reason::Propagation(c) => c,
        };

        let reason_clause = match self.clauses.get(reason) {
            Some(c) => c,
            None => return false,
        };

        // Check all literals in the reason clause
        for &reason_lit in &reason_clause.lits {
            if reason_lit == lit.negate() {
                // Skip the literal we're analyzing
                continue;
            }

            let reason_var = reason_lit.var();

            // Level 0 literals are always OK
            if self.trail.level(reason_var) == 0 {
                continue;
            }

            // If the literal is in the learned clause (seen), it's OK
            if self.seen[reason_var.index()] {
                continue;
            }

            // Otherwise, this literal prevents minimization
            // (A full recursive check would be more powerful but more expensive)
            return false;
        }

        true
    }

    /// Analyze a theory conflict (given as a list of literals that are all false)
    pub(super) fn analyze_theory_conflict(
        &mut self,
        conflict_lits: &[Lit],
    ) -> (u32, SmallVec<[Lit; 16]>) {
        self.learnt.clear();
        self.learnt.push(Lit::from_code(0)); // Placeholder

        let mut counter = 0;

        // Anchor the analysis at the genuine conflict level — the highest
        // decision level among the (all-false) theory conflict literals —
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

        // Process conflict literals
        let mut all_level_zero = true;
        for &lit in conflict_lits {
            let var = lit.var();
            let level = self.trail.level(var);

            if !self.seen[var.index()] && level > 0 {
                all_level_zero = false;
                self.seen[var.index()] = true;
                vars_to_bump.push(var);

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

        // Find UIP by walking back through trail
        let mut index = self.trail.assignments().len();
        let mut p = None;

        while counter > 0 {
            if index == 0 {
                break; // Avoid underflow — no more trail entries
            }
            index -= 1;
            if index >= self.trail.assignments().len() {
                break; // Guard against stale length
            }
            let current_lit = self.trail.assignments()[index];
            p = Some(current_lit);
            let var = current_lit.var();

            if self.seen[var.index()] {
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
                    for &lit in &clause.lits {
                        if lit == current_lit {
                            continue;
                        }
                        let reason_var = lit.var();
                        let level = self.trail.level(reason_var);

                        if !self.seen[reason_var.index()] && level > 0 {
                            self.seen[reason_var.index()] = true;
                            vars_to_bump.push(reason_var);

                            if level == current_level {
                                counter += 1;
                            } else {
                                // Add the literal itself to the learned clause
                                self.learnt.push(lit);
                            }
                        }
                    }
                }
            }
        }

        // Batch bump all collected variables
        self.vsids.bump_batch(&vars_to_bump);
        self.chb.bump_batch(&vars_to_bump);
        self.lrb.on_reason_batch(&vars_to_bump);

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

        (backtrack_level, self.learnt.clone())
    }

    /// Extract the core of assumptions responsible for a *directly conflicting*
    /// assumption — one whose required polarity is already falsified on the trail
    /// when it is about to be asserted (index `conflict_idx`).
    ///
    /// The failed assumption's variable sits on the trail with the opposite phase,
    /// implied (transitively) by earlier assumptions through unit propagation.
    /// Seeding the analysis from that variable and resolving every antecedent back
    /// to its decision (assumption) roots yields *all* contributing assumptions,
    /// not merely the failed one. The previous implementation only ever returned
    /// the single failed assumption (its `seen`-based guard was never populated
    /// for this path), so a core such as `{a, b}` for
    /// `a ∧ b ∧ (¬a ∨ ¬b)` under `[a, b]` came back as just `{b}` — an incomplete,
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
    /// and, when it found nothing, fell back to returning *every* assumption —
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

    // ---------------------------------------------------------------------------
    // Tests for compute_lbd_from_literals
    // ---------------------------------------------------------------------------

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

    // ---------------------------------------------------------------------------
    // Integration test: conflict analysis passes LBD to the external hook
    // ---------------------------------------------------------------------------

    #[test]
    fn test_conflict_analysis_passes_lbd_to_hook() {
        // Solve PHP(3,2) — the same UNSAT formula used in the external_branching tests.
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
                None // always defer — VSIDS drives the solve
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
        // (1-UIP) clause — i.e. the distinct decision-level count of `self.learnt` —
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
             {max_learnt_len} — proves LBD is computed from the learned clause, not vars_to_bump"
        );
    }

    // ---------------------------------------------------------------------------
    // Regression: conflict clause whose literals all sit BELOW the current
    // decision level (an on-the-fly / theory-lemma-style clause).
    // ---------------------------------------------------------------------------

    /// Root cause of the disjunctive-LIA wrong-UNSAT: `analyze` used to anchor
    /// its 1-UIP resolution at `trail.decision_level()`. When the conflict
    /// clause contains NO literal at that level (its highest literal is at a
    /// strictly lower level — as happens for theory reason/lemma clauses added
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
        // 1 — strictly below the current decision level 2.
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
    /// the conflict-level anchoring — the asserting literal still sits at the
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
}
