//! Permanent clauses for definitions minted inside assertion scopes.
//!
//! A root clause is retained even when current scoped facts falsify it. Units
//! need an explicit replay journal because they otherwise live only on the
//! trail. Long clauses use the ordinary attachment/backtracking invariant,
//! with trail position breaking watch ties so pop exposes the watched literals.
//! This preserves the fork's proof, binary-graph and elimination bookkeeping.

use super::*;

impl Solver {
    /// Add a permanent clause which survives every [`Self::pop`].
    ///
    /// Intended for definitions (for example bit-blasted gates), while ordinary
    /// assertions belong in [`Self::add_clause`]. Returns false when the current
    /// root trail falsifies the clause; a conflict depending on a user scope is
    /// retracted with that scope, while the clause itself remains installed.
    pub fn add_clause_at_root(&mut self, lits: impl IntoIterator<Item = Lit>) -> bool {
        let mut clause: SmallVec<[Lit; 8]> = lits.into_iter().collect();
        for lit in &mut clause {
            *lit = self.resolve_reintroduced_literal(*lit);
            self.ensure_vars(lit.var().index() + 1);
        }
        self.void_elimination_promises(&clause);
        self.install_root_clause(clause)
    }

    /// Install a clause whose elimination obligations have already been restored.
    /// Also used by the iterative restoration worklist, avoiding native recursion.
    pub(super) fn install_root_clause(&mut self, mut clause: SmallVec<[Lit; 8]>) -> bool {
        self.mark_subsume_lits(clause.iter());
        let proof_id = self.proof_next_id();
        if let Some(proof) = &mut self.proof {
            let dimacs: SmallVec<[i32; 8]> = clause.iter().map(|l| l.to_dimacs()).collect();
            proof.add_original_clause(proof_id, false, &dimacs);
        }
        clause.sort_unstable_by_key(|l| l.code());
        clause.dedup();
        if clause.windows(2).any(|w| w[0] == w[1].negate()) {
            return true;
        }
        match clause.as_slice() {
            [] => {
                self.latch_root_contradiction();
                self.drat_emit_empty_from_seed(&[], proof_id);
                false
            }
            &[lit] => {
                self.root_units.push((lit, proof_id));
                self.backtrack_to_root();
                self.install_root_unit(lit, proof_id)
            }
            _ => self.install_root_long(clause, proof_id),
        }
    }

    fn latch_root_contradiction(&mut self) {
        self.trivially_unsat = true;
        for scope in &mut self.assertion_levels {
            scope.trivially_unsat = true;
        }
    }

    fn falsified_permanently(&self, lits: &[Lit]) -> bool {
        let end = self
            .assertion_levels
            .get(1)
            .map_or(self.trail.size(), |s| s.trail_size);
        let prefix = &self.trail.assignments()[..end.min(self.trail.size())];
        lits.iter().all(|&lit| {
            self.trail.lit_value(lit).is_false()
                && self.trail.level(lit.var()) == 0
                && prefix.contains(&lit.negate())
        })
    }

    fn install_root_unit(&mut self, lit: Lit, proof_id: i64) -> bool {
        self.proof_set_unit_id(lit.to_dimacs(), proof_id);
        match self.trail.lit_value(lit) {
            LBool::True => true,
            LBool::False => {
                if self.falsified_permanently(&[lit]) {
                    self.latch_root_contradiction();
                } else {
                    self.trivially_unsat = true;
                }
                self.drat_emit_empty_from_seed(&[lit], proof_id);
                false
            }
            LBool::Undef => {
                self.trail.assign_decision(lit);
                true
            }
        }
    }

    fn install_root_long(&mut self, mut clause: SmallVec<[Lit; 8]>, proof_id: i64) -> bool {
        // Reuse the fork's level-aware attachment rule. It may backtrack all
        // the way to root, where any implied literal survives search backtracks.
        let outcome = self.pre_check_effective_unit(&clause);
        let conflicting = matches!(outcome, PreAttachOutcome::UnconditionalConflict);
        let permanent = conflicting && self.falsified_permanently(&clause);
        let rank = |solver: &Self, lit: Lit| {
            let (class, level) = solver.watch_rank(lit);
            let position = if conflicting {
                solver
                    .trail
                    .assignments()
                    .iter()
                    .rposition(|a| a.var() == lit.var())
                    .unwrap_or(0)
            } else {
                0
            };
            (class, level, position)
        };
        for slot in 0..2 {
            let mut best = slot;
            for i in slot + 1..clause.len() {
                if rank(self, clause[i]) > rank(self, clause[best]) {
                    best = i;
                }
            }
            clause.swap(slot, best);
        }
        let id = self.clauses.add_original(clause.iter().copied());
        self.proof_set_clause_id(id, proof_id);
        match self.assertion_levels.first_mut() {
            Some(root) => root.clause_ids.push(id),
            None => panic!("SAT root assertion scope is missing"),
        }
        self.attach_watchers(id, clause[0], clause[1]);
        // Attach even a falsified clause: its falsifying facts may be popped.
        if conflicting {
            if permanent {
                self.latch_root_contradiction();
            } else {
                self.trivially_unsat = true;
            }
            self.drat_emit_empty_from_seed(&clause, proof_id);
            return false;
        }
        if let PreAttachOutcome::ForceUnitAtLevelZero(lit) = outcome {
            self.trail.assign_propagation_at(lit, id, 0);
            self.pending_parse_unit_flushes.push((lit, id));
        }
        true
    }

    pub(super) fn replay_root_units(&mut self) {
        for i in 0..self.root_units.len() {
            let (lit, proof_id) = self.root_units[i];
            self.install_root_unit(lit, proof_id);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn restored_pure_clauses_survive_the_scope_that_reintroduced_them() {
        let mut solver = Solver::new();
        solver.ensure_vars(3);
        solver.add_clause_dimacs(&[1, 2]);
        solver.add_clause_dimacs(&[1, 3]);
        solver.inprocess();
        assert!(
            solver
                .pure_literal_reconstruction
                .contains(&Lit::from_dimacs(1))
        );
        solver.push();
        solver.add_clause_dimacs(&[-1]);
        assert_eq!(solver.solve(), SolverResult::Sat);
        solver.pop();
        // Reconstruction obligations were permanently voided. Their restored
        // clauses must be permanent too, not lost along with the first -x.
        solver.add_clause_dimacs(&[-1]);
        solver.add_clause_dimacs(&[-2]);
        assert_eq!(solver.solve(), SolverResult::Unsat);
    }

    #[test]
    fn restoration_finishes_after_a_scoped_conflict() {
        let mut solver = Solver::new();
        solver.ensure_vars(3);
        // State after pure elimination at base: both clauses were retired by x.
        solver.pure_literal_reconstruction.push(Lit::from_dimacs(1));
        solver.pure_deleted_clauses.push((
            Lit::from_dimacs(1),
            vec![
                smallvec::smallvec![Lit::from_dimacs(1), Lit::from_dimacs(2)],
                smallvec::smallvec![Lit::from_dimacs(1), Lit::from_dimacs(3)],
            ],
        ));
        solver.push();
        solver.add_clause_dimacs(&[-2]);
        solver.add_clause_dimacs(&[-3]);
        // A pre-existing scoped conflict must not abort restoration halfway.
        solver.add_clause([]);
        solver.add_clause_dimacs(&[-1]);
        assert_eq!(solver.solve(), SolverResult::Unsat);
        solver.pop();
        // Check both obligations separately after removing the temporary facts.
        for other in [-2, -3] {
            solver.push();
            solver.add_clause_dimacs(&[-1]);
            solver.add_clause_dimacs(&[other]);
            assert_eq!(solver.solve(), SolverResult::Unsat);
            solver.pop();
        }
        assert_eq!(solver.solve(), SolverResult::Sat);
    }

    #[test]
    fn restoration_closure_uses_a_heap_worklist() {
        let mut solver = Solver::new();
        const N: usize = 2_000;
        solver.ensure_vars(N);
        for i in 0..N - 1 {
            let x = Lit::pos(Var::new(i as u32));
            let next = Lit::neg(Var::new(i as u32 + 1));
            solver.pure_literal_reconstruction.push(x);
            solver
                .pure_deleted_clauses
                .push((x, vec![smallvec::smallvec![x, next]]));
        }
        solver.push();
        solver.add_clause_at_root([Lit::neg(Var::new(0))]);
        solver.pop();
        solver.add_clause([Lit::pos(Var::new(N as u32 - 1))]);
        assert_eq!(solver.solve(), SolverResult::Unsat);
        assert!(solver.pure_deleted_clauses.is_empty());
    }
}
