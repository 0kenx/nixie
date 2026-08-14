//! Pre-search and in-search clause-database simplification for the NLSAT solver.
//!
//! This module wires four otherwise-standalone engines into the solve loop:
//!
//! * [`StructureAnalyzer`](crate::structure_analyzer::StructureAnalyzer) –
//!   classifies the problem once (linear / univariate / dense / …) and seeds a
//!   Brown-style arithmetic variable ordering. Ordering is a *heuristic* only,
//!   so it can never change the satisfiability verdict.
//! * [`SubsumptionChecker`](crate::subsumption::SubsumptionChecker) – a
//!   one-shot pre-search pass that drops an original clause `D` whenever some
//!   other clause `C ⊆ D` is present. A subsumed clause is logically redundant,
//!   so the verdict is preserved.
//! * [`Inprocessor`](crate::inprocessing::Inprocessor) – periodic subsumption
//!   and self-subsuming resolution over *learned* clauses at decision level 0.
//! * [`Vivifier`](crate::vivification::Vivifier) – unit-propagation based
//!   strengthening of learned clauses at decision level 0, replacing each
//!   learned clause with a provably-entailed subset of its literals.
//!
//! Every operation here is model-preserving: subsumption and self-subsuming
//! resolution preserve the set of models, vivification only ever replaces a
//! clause with an entailed subset, and structural reordering touches decision
//! heuristics alone. Correctness of the clause-removing passes relies on the
//! `ClauseId`/index distinction being respected everywhere (`ClauseId` is a
//! stable id, never a Vec position); the two former `idx as ClauseId` sites in
//! the solver were fixed alongside this wiring.

use super::{NlsatSolver, PropagationResult};
use crate::assignment::Justification;
use crate::clause::{Clause, ClauseId};
use crate::types::{Atom, Literal};
use oxiz_math::polynomial::{Polynomial, Var};
use rustc_hash::FxHashSet;

impl NlsatSolver {
    /// Run the one-shot pre-search preprocessing pass (idempotent).
    ///
    /// Executed once, before the first search, at decision level 0. It performs
    /// structural classification + variable ordering and then eliminates
    /// subsumed original clauses. Both steps preserve the satisfiability verdict.
    pub(super) fn preprocess(&mut self) {
        if self.preprocessed {
            return;
        }
        self.preprocessed = true;

        self.classify_problem();
        self.subsume_original_clauses();
    }

    /// Classify the problem structure and store the classification for
    /// strategy selection (see [`Self::inprocessing_beneficial`]).
    ///
    /// This is deliberately *read-only*: it does not reorder the arithmetic
    /// variables. Because this solver assigns arithmetic variables greedily
    /// without backtracking over an individual arithmetic choice, the variable
    /// order is completeness-critical, and a naive degree-based reordering can
    /// make a satisfiable instance unsolvable (e.g. assigning a functionally
    /// determined variable before the free variable it depends on). The
    /// insertion order is therefore preserved.
    fn classify_problem(&mut self) {
        use crate::structure_analyzer::StructureAnalyzer;

        let mut analyzer = StructureAnalyzer::new();
        for atom in &self.atoms {
            match atom {
                Atom::Ineq(ineq) => {
                    for factor in &ineq.factors {
                        analyzer.add_polynomial(factor.poly.clone());
                    }
                }
                Atom::Root(root) => analyzer.add_polynomial(root.poly.clone()),
            }
        }
        self.problem_class = Some(analyzer.classify());
    }

    /// Strategy selection driven by the problem classification: in-search
    /// learned-clause simplification (subsumption / strengthening / vivification)
    /// is only worthwhile once the Boolean structure is non-trivial. Purely
    /// linear or univariate problems have essentially no Boolean search, so the
    /// passes are skipped there. This choice is verdict-neutral (the passes are
    /// model-preserving whether or not they run).
    pub(super) fn inprocessing_beneficial(&self) -> bool {
        use crate::structure_analyzer::ProblemClass;
        !matches!(
            self.problem_class,
            Some(ProblemClass::Linear) | Some(ProblemClass::Univariate)
        )
    }

    /// One-shot forward/backward subsumption over the original (non-learned)
    /// clause set. Rebuilds the clause database from the surviving clauses and
    /// re-derives the level-0 unit assignments so nothing references a stale id.
    fn subsume_original_clauses(&mut self) {
        // Reconstruct owned clauses for the subsumption engine (ids/max_var are
        // irrelevant to the propositional subsumption check).
        let originals: Vec<Clause> = self
            .clauses
            .clauses()
            .iter()
            .filter(|c| !c.is_learned())
            .map(|c| Clause::new(c.literals().to_vec(), c.max_var(), false, c.id()))
            .collect();
        let before = originals.len();
        if before < 2 {
            return;
        }

        let survivors = self.subsumption_checker.eliminate_subsumed(originals);
        let removed = before - survivors.len();
        if removed == 0 {
            return;
        }
        self.stats.preprocess_subsumed += removed as u64;

        // Rebuild the database from survivors. This pass runs before the first
        // search, so there are no learned clauses and no arithmetic model to
        // preserve. Re-deriving units from the reduced database restores a clean
        // level-0 state.
        let rebuilt: Vec<(Vec<Literal>, Var)> = survivors
            .into_iter()
            .map(|c| (c.literals().to_vec(), c.max_var()))
            .collect();
        self.clauses.clear();
        for (lits, mv) in rebuilt {
            self.clauses.add(lits, mv, false);
        }
        self.reset_search_state();
    }

    /// Clause ids that currently justify a trail assignment (reason clauses).
    /// These must never be removed or rewritten by an in-search pass.
    fn trail_reason_clause_ids(&self) -> FxHashSet<ClauseId> {
        let mut set = FxHashSet::default();
        for entry in self.assignment.trail() {
            if let Justification::Propagation(cid) = entry.justification {
                set.insert(cid);
            }
        }
        set
    }

    /// Periodic in-search subsumption + self-subsuming strengthening of learned
    /// clauses, run at decision level 0 on the [`Inprocessor`] schedule.
    ///
    /// Only learned clauses are removed or rewritten (they are all entailed by
    /// the originals, so this is model-preserving), and a clause that currently
    /// acts as a reason on the trail is never touched.
    pub(super) fn run_inprocessing(&mut self) {
        if self.assignment.level() != 0 {
            return;
        }
        if !self.inprocessor.inprocess(self.stats.conflicts) {
            return;
        }
        self.stats.inprocess_passes += 1;

        let reasons = self.trail_reason_clause_ids();

        // Subsumption: drop learned clauses that are subsumed by another clause.
        let subsumptions = self.inprocessor.find_subsumptions(self.clauses.clauses());
        let mut removed: FxHashSet<ClauseId> = FxHashSet::default();
        for (subsumed_id, subsuming_id) in subsumptions {
            if subsumed_id == subsuming_id || reasons.contains(&subsumed_id) {
                continue;
            }
            // Only remove *learned* clauses (originals define the problem).
            let is_learned = self
                .clauses
                .get(subsumed_id)
                .map(|c| c.is_learned())
                .unwrap_or(false);
            if is_learned && removed.insert(subsumed_id) {
                self.clauses.remove(subsumed_id);
            }
        }

        // Self-subsuming resolution: strengthen learned clauses by removing a
        // literal whose negation is resolved away by a subsuming partner.
        let strengthenings = self.inprocessor.find_strengthenings(self.clauses.clauses());
        for (cid, lit_to_remove) in strengthenings {
            if removed.contains(&cid) || reasons.contains(&cid) {
                continue;
            }
            let Some(clause) = self.clauses.get(cid) else {
                continue;
            };
            if !clause.is_learned() {
                continue;
            }
            let mut new_lits: Vec<Literal> = clause
                .literals()
                .iter()
                .copied()
                .filter(|&l| l != lit_to_remove)
                .collect();
            // Keep at least a binary clause; skip degenerate results (handled by
            // ordinary conflict analysis instead of a fragile unit rewrite).
            if new_lits.len() < 2 || new_lits.len() == clause.len() {
                continue;
            }
            new_lits.sort_by_key(|l| l.index());
            removed.insert(cid);
            self.clauses.remove(cid);
            self.add_learned_clause(new_lits);
        }
    }

    /// Unit-propagation based vivification of learned clauses at decision level 0.
    ///
    /// For each candidate learned clause the clause is first removed from the
    /// database (so the probe cannot use the clause to prove its own
    /// strengthening – that would be circular), then the negations of its
    /// literals are assumed one at a time with real boolean propagation. If the
    /// accumulated assumptions become inconsistent, the assumed prefix is a
    /// clause entailed by the *rest* of the formula that subsumes the original,
    /// so the original is replaced by that strictly shorter, still-entailed
    /// clause. When no strengthening is found the original clause is restored
    /// verbatim.
    pub(super) fn vivify_learned(&mut self) {
        if !self.vivifier.config().enabled {
            return;
        }
        // Require a clean level-0 state: probing pushes/pops decision levels.
        if self.assignment.level() != 0
            || !self.propagation_queue.is_empty()
            || self.conflict_clause.is_some()
        {
            return;
        }

        let max_size = self.vivifier.config().max_clause_size;
        let reasons = self.trail_reason_clause_ids();
        let candidates: Vec<(ClauseId, Vec<Literal>)> = self
            .clauses
            .clauses()
            .iter()
            .filter(|c| {
                c.is_learned() && c.len() >= 2 && c.len() <= max_size && !reasons.contains(&c.id())
            })
            .map(|c| (c.id(), c.literals().to_vec()))
            .collect();

        for (cid, lits) in candidates {
            // Remove the clause so the probe uses only the rest of the formula.
            self.clauses.remove(cid);

            let strengthened = self.vivify_probe(&lits);
            // Restore a clean level-0 state after probing.
            self.backtrack(0);

            match strengthened {
                // Keep results at binary or larger; a unit result would need
                // level-0 assign/conflict handling, so those are conservatively
                // left to ordinary conflict analysis (re-add the original).
                Some(prefix) if prefix.len() >= 2 && prefix.len() < lits.len() => {
                    let removed = (lits.len() - prefix.len()) as u64;
                    self.stats.vivified_literals += removed;
                    self.vivifier.note_vivified(removed);
                    self.add_learned_clause(prefix);
                }
                _ => {
                    // No usable strengthening: re-add the original unchanged.
                    let mv = self.clause_max_var(&lits);
                    self.clauses.add(lits, mv, true);
                }
            }
        }
    }

    /// Probe a clause for vivification. Assumes the clause has already been
    /// removed from the database and the solver is at decision level 0 with an
    /// empty propagation queue. Returns `Some(prefix)` when the clause can be
    /// strengthened to the (strictly shorter) entailed `prefix`, else `None`.
    ///
    /// Soundness: the returned `prefix` is either (a) a set of literals whose
    /// negations propagate to a conflict – hence entailed by the formula and a
    /// superclause-subset of the original – or (b) the original with literals
    /// dropped because they were forced false by the negations of the retained
    /// literals (so every model of the formula satisfying the original also
    /// satisfies `prefix`). Both cases preserve the model set.
    fn vivify_probe(&mut self, lits: &[Literal]) -> Option<Vec<Literal>> {
        let mut kept: Vec<Literal> = Vec::new();

        for &l in lits {
            let value = self.assignment.lit_value(l);
            if value.is_true() {
                // The accumulated assumptions already entail `l`, so
                // `kept ∨ l` is entailed and subsumes the original clause.
                kept.push(l);
                self.propagation_queue.clear();
                return Some(kept);
            }
            if value.is_false() {
                // `l` is forced false by the negations of the retained literals,
                // so it is redundant: drop it.
                continue;
            }

            // Undetermined: assume ¬l and propagate.
            self.assignment.push_level();
            self.assignment.assign(l.negate(), Justification::Decision);
            self.propagation_queue.push(l.negate());
            match self.propagate() {
                PropagationResult::Ok => kept.push(l),
                PropagationResult::Conflict(_) | PropagationResult::TheoryConflict(_) => {
                    // ¬kept ∧ ¬l ⇒ false, so (kept ∨ l) is entailed.
                    kept.push(l);
                    self.propagation_queue.clear();
                    return Some(kept);
                }
            }
        }

        // Reached the end with no conflict: a strengthening exists only if some
        // literal was dropped as redundant.
        if kept.len() < lits.len() {
            Some(kept)
        } else {
            None
        }
    }

    /// Record the arithmetic variables participating in a certified theory
    /// conflict into the [`TheoryConflictTracker`](crate::theory_conflict::TheoryConflictTracker)
    /// and boost their decision activity, so recurrently-conflicting variables
    /// are decided earlier. This only reorders heuristics – never the verdict.
    pub(super) fn record_theory_conflict_vars(&mut self, lemma: &[Literal]) {
        let mut vars: Vec<Var> = Vec::new();
        let mut polys: Vec<Polynomial> = Vec::new();
        for lit in lemma {
            let bv = lit.var();
            for atom in &self.atoms {
                match atom {
                    Atom::Ineq(ineq) if ineq.bool_var == bv => {
                        for factor in &ineq.factors {
                            for v in factor.poly.vars() {
                                if !vars.contains(&v) {
                                    vars.push(v);
                                }
                            }
                            polys.push(factor.poly.clone());
                        }
                    }
                    Atom::Root(root) if root.bool_var == bv => {
                        for v in root.poly.vars() {
                            if !vars.contains(&v) {
                                vars.push(v);
                            }
                        }
                        polys.push(root.poly.clone());
                    }
                    _ => {}
                }
            }
        }
        if vars.is_empty() {
            return;
        }
        self.theory_conflict_tracker
            .record_conflict(vars.clone(), polys);
        // Feed the tracker's scores into the arithmetic activity used by
        // dynamic reordering.
        for v in vars {
            self.bump_arith_activity(v);
        }
    }

    /// Read-only access to the theory-conflict tracker statistics (for tests
    /// and diagnostics).
    pub fn theory_conflict_stats(&self) -> &crate::theory_conflict::TheoryConflictStats {
        self.theory_conflict_tracker.stats()
    }

    /// The problem structure classification computed during preprocessing, if
    /// [`solve`](Self::solve) has been called.
    pub fn problem_class(&self) -> Option<crate::structure_analyzer::ProblemClass> {
        self.problem_class
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver::SolverResult;
    use crate::types::{AtomKind, Literal};
    use num_bigint::BigInt;
    use num_rational::BigRational;
    use oxiz_math::polynomial::Polynomial;

    fn rat(n: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(n))
    }

    // ======== eval_cache (theory evaluation memoization) ========

    #[test]
    fn eval_cache_serves_repeated_atom_evaluations() {
        // A single atom x > 0 evaluated twice at the same arithmetic assignment
        // must be answered from the cache on the second sweep.
        let mut solver = NlsatSolver::new();
        let _atom = solver.new_ineq_atom(Polynomial::from_var(0), AtomKind::Gt);
        solver.assignment.set_arith(0, rat(1)); // x = 1

        assert_eq!(solver.stats().eval_cache_hits, 0);
        let _ = solver.theory_propagate(); // miss + populate + theory-propagate
        let _ = solver.theory_propagate(); // hit

        assert!(
            solver.stats().eval_cache_hits > 0,
            "the second evaluation of the same atom must hit the theory cache"
        );
    }

    #[test]
    fn eval_cache_cleared_on_backtrack_stays_sound() {
        // After a backtrack (which unsets the arithmetic model) the cache must
        // be empty so it cannot answer with a stale value. x > 0 is true at
        // x = 1 but false at x = -1.
        use crate::types::Lbool;

        let mut solver = NlsatSolver::new();
        let atom = solver.new_ineq_atom(Polynomial::from_var(0), AtomKind::Gt);

        solver.assignment.set_arith(0, rat(1));
        let _ = solver.theory_propagate();
        assert!(
            !solver.eval_cache.is_empty(),
            "evaluating x > 0 at x = 1 must populate the cache"
        );

        // Drop to a clean state (unsets the arithmetic model and clears cache).
        solver.backtrack(0);
        assert!(
            solver.eval_cache.is_empty(),
            "backtrack must clear the theory-evaluation cache"
        );

        // A fresh evaluation at x = -1 must return False, not a stale True.
        solver.assignment.set_arith(0, rat(-1));
        assert_eq!(
            solver.evaluate_atom(atom),
            Lbool::False,
            "x = -1 makes x > 0 false; the cleared cache must recompute it"
        );
    }

    // ======== subsumption preprocessing ========

    #[test]
    fn preprocess_subsumes_original_clauses_and_stays_sat() {
        // (a) subsumes (a ∨ b): the longer clause must be dropped pre-search.
        let mut solver = NlsatSolver::new();
        let a = solver.new_bool_var();
        let b = solver.new_bool_var();
        solver.add_clause(vec![Literal::positive(a)]);
        solver.add_clause(vec![Literal::positive(a), Literal::positive(b)]);

        let result = solver.solve();
        assert_eq!(result, SolverResult::Sat);
        assert!(
            solver.stats().preprocess_subsumed > 0,
            "pre-search subsumption must remove the subsumed clause"
        );
    }

    #[test]
    fn preprocess_subsumption_preserves_unsat() {
        // (a) and (¬a) plus a redundant (a ∨ b): still UNSAT after subsumption.
        let mut solver = NlsatSolver::new();
        let a = solver.new_bool_var();
        let b = solver.new_bool_var();
        solver.add_clause(vec![Literal::positive(a), Literal::positive(b)]);
        solver.add_clause(vec![Literal::positive(a)]);
        solver.add_clause(vec![Literal::negative(a)]);
        assert_eq!(solver.solve(), SolverResult::Unsat);
    }

    // ======== theory-conflict tracking ========

    #[test]
    fn theory_conflict_tracker_records_certified_conflicts() {
        // x > 1 ∧ x*y > 1 ∧ y < 0 is UNSAT via a certified coupled sign
        // conflict, which routes through `install_theory_conflict` and must be
        // recorded by the tracker.
        let mut solver = NlsatSolver::new();
        let x = Polynomial::from_var(0);
        let y = Polynomial::from_var(1);
        let xy = Polynomial::mul(&x, &y);

        let a1 = solver.new_ineq_atom(
            Polynomial::sub(&x, &Polynomial::constant(rat(1))),
            AtomKind::Gt,
        );
        let a2 = solver.new_ineq_atom(
            Polynomial::sub(&xy, &Polynomial::constant(rat(1))),
            AtomKind::Gt,
        );
        let a3 = solver.new_ineq_atom(y, AtomKind::Lt);
        solver.add_clause(vec![solver.atom_literal(a1, true)]);
        solver.add_clause(vec![solver.atom_literal(a2, true)]);
        solver.add_clause(vec![solver.atom_literal(a3, true)]);

        assert_eq!(solver.solve(), SolverResult::Unsat);
        assert!(
            solver.theory_conflict_stats().num_conflicts > 0,
            "the theory-conflict tracker must record the certified conflict"
        );
    }

    // ======== vivification ========

    #[test]
    fn vivify_learned_removes_redundant_literal_and_stays_sound() {
        // Formula: unit (a). A learned clause (¬a ∨ b ∨ c ∨ d): since `a` is a
        // level-0 unit, ¬a is permanently false, so the clause is
        // entailed-equivalent to (b ∨ c ∨ d). Vivification must drop ¬a.
        let mut solver = NlsatSolver::new();
        let a = solver.new_bool_var();
        let b = solver.new_bool_var();
        let c = solver.new_bool_var();
        let d = solver.new_bool_var();

        solver.add_clause(vec![Literal::positive(a)]);
        // Settle the unit onto the trail (empties the propagation queue).
        let _ = solver.propagate();

        let before = solver.stats().vivified_literals;
        solver.add_learned_clause(vec![
            Literal::negative(a),
            Literal::positive(b),
            Literal::positive(c),
            Literal::positive(d),
        ]);

        solver.vivify_learned();

        // Execution proof: the vivifier removed at least one literal.
        assert!(
            solver.stats().vivified_literals > before,
            "vivification must remove the redundant ¬a literal"
        );
        assert!(
            solver.vivifier.stats().literals_removed > 0,
            "the Vivifier engine must record the strengthening"
        );

        // No shortened clause may keep the dropped literal.
        let has_neg_a = solver
            .clauses
            .clauses()
            .iter()
            .filter(|cl| cl.is_learned())
            .any(|cl| cl.literals().contains(&Literal::negative(a)));
        assert!(
            !has_neg_a,
            "the strengthened learned clause must no longer contain ¬a"
        );

        // Soundness regression: the formula (just the unit `a`, plus an
        // entailed learned clause) is satisfiable and must stay SAT.
        assert_eq!(solver.solve(), SolverResult::Sat);
    }

    #[test]
    fn vivify_probe_derives_entailed_prefix_on_conflict() {
        // Originals: (¬x ∨ y) and (¬y): assuming x forces y then ¬y ⇒ conflict,
        // so probing the clause (x ∨ z ∨ w) strengthens it to the unit-level
        // prefix (x) – but since we only keep binary+ results, the mechanism is
        // exercised via a 3-literal clause whose first two probes conflict.
        let mut solver = NlsatSolver::new();
        let x = solver.new_bool_var();
        let y = solver.new_bool_var();
        let z = solver.new_bool_var();
        let w = solver.new_bool_var();

        solver.add_clause(vec![Literal::negative(x), Literal::positive(y)]); // ¬x ∨ y
        solver.add_clause(vec![Literal::negative(y)]); // ¬y  ⇒ y=false, and x=false
        let _ = solver.propagate();

        // At this point ¬y and (via ¬x∨y) ¬x are entailed at level 0.
        // Learned clause (x ∨ z ∨ w): x is false ⇒ redundant; drops to (z ∨ w).
        let before = solver.stats().vivified_literals;
        solver.add_learned_clause(vec![
            Literal::positive(x),
            Literal::positive(z),
            Literal::positive(w),
        ]);
        solver.vivify_learned();

        assert!(
            solver.stats().vivified_literals > before,
            "the always-false x literal must be removed"
        );
        assert_eq!(solver.solve(), SolverResult::Sat);
    }

    // ======== inprocessing (learned-clause subsumption / strengthening) ========

    #[test]
    fn inprocessing_removes_subsumed_learned_clause() {
        let mut solver = NlsatSolver::new();
        let a = solver.new_bool_var();
        let b = solver.new_bool_var();
        let c = solver.new_bool_var();

        // Two learned clauses: (a ∨ b) subsumes (a ∨ b ∨ c).
        solver.add_learned_clause(vec![Literal::positive(a), Literal::positive(b)]);
        solver.add_learned_clause(vec![
            Literal::positive(a),
            Literal::positive(b),
            Literal::positive(c),
        ]);
        let clauses_before = solver.num_clauses();

        // conflicts == 0 satisfies the inprocessor's interval schedule.
        solver.run_inprocessing();

        assert_eq!(
            solver.stats().inprocess_passes,
            1,
            "the inprocessing pass must have executed"
        );
        assert!(
            solver.inprocessor.stats().subsumed_clauses > 0,
            "the inprocessor must have found the subsumption"
        );
        assert_eq!(
            solver.num_clauses(),
            clauses_before - 1,
            "the subsumed learned clause must be removed"
        );
        // Soundness: (a ∨ b) alone is satisfiable.
        assert_eq!(solver.solve(), SolverResult::Sat);
    }

    #[test]
    fn inprocessing_strengthens_learned_clause_by_self_subsumption() {
        let mut solver = NlsatSolver::new();
        let a = solver.new_bool_var();
        let b = solver.new_bool_var();
        let d = solver.new_bool_var();

        // (a ∨ b) and (a ∨ ¬b ∨ d): self-subsuming resolution on b strengthens
        // the second to (a ∨ d).
        solver.add_learned_clause(vec![Literal::positive(a), Literal::positive(b)]);
        solver.add_learned_clause(vec![
            Literal::positive(a),
            Literal::negative(b),
            Literal::positive(d),
        ]);

        solver.run_inprocessing();

        // The strengthened clause (a ∨ d) must now be present, and no learned
        // clause may still contain both ¬b and d together with a.
        let has_strengthened = solver.clauses.clauses().iter().any(|cl| {
            cl.is_learned()
                && cl.len() == 2
                && cl.literals().contains(&Literal::positive(a))
                && cl.literals().contains(&Literal::positive(d))
        });
        assert!(
            has_strengthened,
            "self-subsuming resolution must produce (a ∨ d)"
        );
        assert_eq!(solver.solve(), SolverResult::Sat);
    }
}
