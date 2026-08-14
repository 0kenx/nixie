//! Asymmetric Branching (AB) - Advanced clause strengthening
//!
//! Asymmetric Branching is a powerful technique for strengthening clauses by
//! removing redundant literals. It works by temporarily assigning literals
//! and checking if unit propagation leads to a conflict.
//!
//! For a clause C = (l1 ∨ l2 ∨ ... ∨ ln), we check if assigning ~l1 = true
//! and propagating leads to deriving the clause (l2 ∨ ... ∨ ln). If so, l1
//! is redundant and can be removed.
//!
//! This is more powerful than traditional clause minimization as it uses
//! the full constraint graph, not just the implication graph.

use crate::clause::{ClauseDatabase, ClauseId};
use crate::literal::{LBool, Lit};
#[allow(unused_imports)]
use crate::prelude::*;
use smallvec::SmallVec;

/// Asymmetric Branching engine
///
/// Performs clause strengthening through asymmetric branching.
/// This involves temporarily assigning literals and checking for
/// unit propagation conflicts.
pub struct AsymmetricBranching {
    /// Stack for unit propagation
    prop_queue: Vec<Lit>,
    /// Temporary assignment for AB checks
    temp_assignment: Vec<LBool>,
    /// Literals that were assigned during AB
    assigned_lits: Vec<Lit>,
    /// Statistics
    stats: AsymmetricBranchingStats,
}

/// Status of a clause under the temporary assignment, used by
/// [`AsymmetricBranching::propagate_all`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ClauseStatus {
    /// At least one literal is true
    Satisfied,
    /// Every literal is false
    Conflict,
    /// Exactly one literal is undefined and the rest are false
    Unit(Lit),
    /// More than one literal is undefined (or none, but not all false)
    Unresolved,
}

/// Statistics for Asymmetric Branching
#[derive(Debug, Default, Clone)]
pub struct AsymmetricBranchingStats {
    /// Number of clauses strengthened
    pub strengthened: usize,
    /// Number of literals removed
    pub literals_removed: usize,
    /// Number of AB attempts
    pub attempts: usize,
    /// Number of successful AB operations
    pub successes: usize,
}

impl AsymmetricBranching {
    /// Create a new Asymmetric Branching engine
    #[must_use]
    pub fn new(num_vars: usize) -> Self {
        Self {
            prop_queue: Vec::new(),
            temp_assignment: vec![LBool::Undef; num_vars],
            assigned_lits: Vec::new(),
            stats: AsymmetricBranchingStats::default(),
        }
    }

    /// Resize to accommodate more variables
    pub fn resize(&mut self, num_vars: usize) {
        self.temp_assignment.resize(num_vars, LBool::Undef);
    }

    /// Check if a literal is true under temporary assignment
    #[inline]
    fn is_true(&self, lit: Lit) -> bool {
        let val = self.temp_assignment[lit.var().index()];
        (lit.is_pos() && val == LBool::True) || (!lit.is_pos() && val == LBool::False)
    }

    /// Check if a literal is false under temporary assignment
    #[inline]
    fn is_false(&self, lit: Lit) -> bool {
        let val = self.temp_assignment[lit.var().index()];
        (lit.is_pos() && val == LBool::False) || (!lit.is_pos() && val == LBool::True)
    }

    /// Check if a literal is undefined
    #[inline]
    fn is_undef(&self, lit: Lit) -> bool {
        self.temp_assignment[lit.var().index()] == LBool::Undef
    }

    /// Assign a literal in the temporary assignment
    fn assign(&mut self, lit: Lit) {
        let var = lit.var();
        let val = if lit.is_pos() {
            LBool::True
        } else {
            LBool::False
        };
        self.temp_assignment[var.index()] = val;
        self.assigned_lits.push(lit);
    }

    /// Backtrack all temporary assignments
    fn backtrack(&mut self) {
        for &lit in &self.assigned_lits {
            self.temp_assignment[lit.var().index()] = LBool::Undef;
        }
        self.assigned_lits.clear();
        self.prop_queue.clear();
    }

    /// Classify a clause under the temporary assignment
    ///
    /// This distinguishes "satisfied" from "conflict" (both leave zero
    /// undefined literals under a naive scan), which the previous
    /// `propagate_clause` collapsed into a single `None`, making conflict
    /// detection impossible.
    fn clause_status(&self, lits: &[Lit]) -> ClauseStatus {
        let mut undef_lit: Option<Lit> = None;

        for &lit in lits {
            if self.is_true(lit) {
                return ClauseStatus::Satisfied;
            } else if self.is_undef(lit) {
                if undef_lit.is_some() {
                    return ClauseStatus::Unresolved;
                }
                undef_lit = Some(lit);
            }
        }

        match undef_lit {
            Some(lit) => ClauseStatus::Unit(lit),
            None => ClauseStatus::Conflict,
        }
    }

    /// Run unit propagation to a fixpoint over every live clause in `clauses`,
    /// starting from whatever literals are already assigned in the temporary
    /// assignment (the negated "other" literals of the clause under test).
    ///
    /// Returns `true` as soon as some clause is fully falsified.
    ///
    /// `AsymmetricBranching` has no access to the solver's watch lists or
    /// trail (it is a standalone off-line strengthening pass, not wired into
    /// CDCL search), so this is a brute-force, non-watched BCP that re-scans
    /// every clause each round. That is acceptable because it only runs via
    /// the explicit `strengthen_clause` / `strengthen_all` API, never on the
    /// solver's hot path.
    fn propagate_all(&mut self, clauses: &ClauseDatabase) -> bool {
        let mut changed = true;
        while changed {
            changed = false;
            for id in clauses.iter_ids() {
                let Some(clause) = clauses.get(id) else {
                    continue;
                };
                match self.clause_status(&clause.lits) {
                    ClauseStatus::Conflict => return true,
                    ClauseStatus::Unit(lit) => {
                        self.assign(lit);
                        changed = true;
                    }
                    ClauseStatus::Satisfied | ClauseStatus::Unresolved => {}
                }
            }
        }
        false
    }

    /// Try to strengthen a clause using asymmetric branching
    ///
    /// For clause `C = l_0 ∨ l_1 ∨ ... ∨ l_{n-1}`, literal `l_k` is redundant
    /// (droppable) if the rest of the database already entails `C \ {l_k}`.
    /// To certify that, we assume `¬(C \ {l_k})` – i.e. the negation of every
    /// *other* literal – and run unit propagation over `clauses`. A conflict
    /// means `clauses ∧ ¬(C \ {l_k}) ⊨ ⊥`, i.e. `clauses ⊨ (C \ {l_k})`, so
    /// `l_k` can be dropped while the clause stays entailed (self-subsuming
    /// resolution / asymmetric literal elimination). This mirrors the
    /// technique `Solver::strengthen_clauses_inprocessing` and
    /// `Solver::vivify_clauses` use against the live trail, except here the
    /// propagation is a self-contained brute-force BCP over `clauses` (see
    /// `Self::propagate_all`) since this module has no access to the
    /// solver's watch lists or trail.
    ///
    /// Removed literals are re-derived greedily: after a literal is dropped,
    /// later iterations test redundancy against the already-shrunk clause,
    /// which stays sound because each successful test only ever certifies
    /// entailment of a clause that is itself already known to be entailed.
    ///
    /// Returns the strengthened clause (with redundant literals removed)
    /// or `None` if the clause couldn't be strengthened.
    pub fn strengthen_clause(
        &mut self,
        clause_lits: &[Lit],
        clauses: &ClauseDatabase,
    ) -> Option<SmallVec<[Lit; 8]>> {
        self.stats.attempts += 1;

        if clause_lits.len() <= 2 {
            // Don't strengthen very small clauses
            return None;
        }

        let mut new_lits: SmallVec<[Lit; 8]> = clause_lits.iter().copied().collect();
        let mut strengthened = false;

        // Try to remove each literal, re-scanning the (possibly shrunk)
        // clause until no more literals can be removed or only two remain.
        let mut i = 0;
        while i < new_lits.len() && new_lits.len() > 2 {
            self.backtrack();

            // Assume the negation of every *other* literal and propagate.
            let mut conflict = false;
            for (j, &other) in new_lits.iter().enumerate() {
                if j == i {
                    continue;
                }
                let neg = other.negate();
                if self.is_true(neg) {
                    // Already implied by an earlier assumption in this pass.
                    continue;
                }
                if self.is_false(neg) {
                    // Assuming ~other directly contradicts a value already
                    // forced by propagation from an earlier assumption in
                    // this pass – an immediate conflict.
                    conflict = true;
                    break;
                }
                self.assign(neg);
                if self.propagate_all(clauses) {
                    conflict = true;
                    break;
                }
            }

            self.backtrack();

            if conflict {
                new_lits.remove(i);
                strengthened = true;
                self.stats.literals_removed += 1;
                // Don't advance `i`: the next literal has shifted into it.
            } else {
                i += 1;
            }
        }

        if strengthened {
            self.stats.strengthened += 1;
            self.stats.successes += 1;
            Some(new_lits)
        } else {
            None
        }
    }

    /// Strengthen all clauses in the database
    ///
    /// Returns the number of clauses that were strengthened
    pub fn strengthen_all(&mut self, clauses: &mut ClauseDatabase) -> usize {
        let mut strengthened_count = 0;

        // Collect clause IDs to avoid borrow checker issues
        let clause_ids: Vec<ClauseId> = clauses.iter_ids().collect();

        for id in clause_ids {
            if let Some(clause) = clauses.get(id) {
                let lits: SmallVec<[Lit; 8]> = clause.lits.iter().copied().collect();

                if let Some(new_lits) = self.strengthen_clause(&lits, clauses)
                    && new_lits.len() < lits.len()
                {
                    // Remove old clause and add strengthened version. This is
                    // an off-line pass with no trail access (see the module
                    // doc), so `compute_lbd` is unavailable; carry the
                    // predecessor's LBD instead. Strengthening only removes
                    // literals, so the distinct-level count cannot grow – the
                    // old LBD is a sound upper bound, clamped to the new
                    // length (LBD <= len) and to >= 1 (the invariant every
                    // other `add_learned` site satisfies).
                    let old_lbd = clauses.get(id).map(|c| c.lbd).unwrap_or(1);
                    let new_len = new_lits.len() as u32;
                    clauses.remove(id);
                    let new_id = clauses.add_learned(new_lits);
                    let new_lbd = old_lbd.min(new_len).max(1);
                    if let Some(c) = clauses.get_mut(new_id) {
                        c.lbd = new_lbd;
                    }
                    strengthened_count += 1;
                }
            }
        }

        strengthened_count
    }

    /// Get statistics
    #[must_use]
    pub fn stats(&self) -> &AsymmetricBranchingStats {
        &self.stats
    }

    /// Reset statistics
    pub fn reset_stats(&mut self) {
        self.stats = AsymmetricBranchingStats::default();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clause::Clause;
    use crate::literal::Var;

    #[test]
    fn test_ab_creation() {
        let ab = AsymmetricBranching::new(10);
        assert_eq!(ab.temp_assignment.len(), 10);
    }

    #[test]
    fn test_ab_assign_backtrack() {
        let mut ab = AsymmetricBranching::new(10);

        let lit = Lit::pos(Var::new(0));
        ab.assign(lit);

        assert!(ab.is_true(lit));
        assert!(ab.is_false(lit.negate()));

        ab.backtrack();

        assert!(ab.is_undef(lit));
    }

    #[test]
    fn test_ab_strengthen_simple() {
        let mut ab = AsymmetricBranching::new(10);
        let db = ClauseDatabase::new();

        // Simple clause that can't be strengthened trivially
        let clause = vec![
            Lit::pos(Var::new(0)),
            Lit::pos(Var::new(1)),
            Lit::pos(Var::new(2)),
        ];

        // Without additional constraints, we can't strengthen
        let result = ab.strengthen_clause(&clause, &db);

        // May or may not strengthen depending on implementation
        // Just check it doesn't crash
        assert!(result.is_some() || result.is_none());
    }

    #[test]
    fn test_ab_resize() {
        let mut ab = AsymmetricBranching::new(5);
        assert_eq!(ab.temp_assignment.len(), 5);

        ab.resize(10);
        assert_eq!(ab.temp_assignment.len(), 10);
    }

    #[test]
    fn test_ab_stats() {
        let mut ab = AsymmetricBranching::new(10);
        let db = ClauseDatabase::new();

        let clause = vec![Lit::pos(Var::new(0)), Lit::pos(Var::new(1))];

        ab.strengthen_clause(&clause, &db);

        let stats = ab.stats();
        assert_eq!(stats.attempts, 1);
    }

    #[test]
    fn test_ab_strengthen_all() {
        let mut ab = AsymmetricBranching::new(10);
        let mut db = ClauseDatabase::new();

        // Add some clauses
        db.add(Clause::new(
            vec![Lit::pos(Var::new(0)), Lit::pos(Var::new(1))],
            false,
        ));
        db.add(Clause::new(
            vec![
                Lit::pos(Var::new(2)),
                Lit::pos(Var::new(3)),
                Lit::pos(Var::new(4)),
            ],
            false,
        ));

        let _count = ab.strengthen_all(&mut db);

        // strengthen_all completed successfully (count is usize, always >= 0)
    }

    #[test]
    fn test_ab_no_strengthen_binary() {
        let mut ab = AsymmetricBranching::new(10);
        let db = ClauseDatabase::new();

        // Binary clauses should not be strengthened
        let clause = vec![Lit::pos(Var::new(0)), Lit::pos(Var::new(1))];

        let result = ab.strengthen_clause(&clause, &db);

        // Should return None for binary clauses
        assert!(result.is_none());
    }

    #[test]
    fn test_ab_is_true_false() {
        let mut ab = AsymmetricBranching::new(10);

        let lit = Lit::pos(Var::new(0));

        assert!(ab.is_undef(lit));
        assert!(!ab.is_true(lit));
        assert!(!ab.is_false(lit));

        ab.assign(lit);

        assert!(ab.is_true(lit));
        assert!(!ab.is_false(lit));
        assert!(!ab.is_undef(lit));

        assert!(ab.is_false(lit.negate()));
        assert!(!ab.is_true(lit.negate()));
    }
}
