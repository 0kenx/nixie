//! Advanced clause database maintenance and cleaning
//!
//! This module provides utilities for maintaining clause quality through:
//! - Periodic clause cleaning (duplicate removal, normalization)
//! - Advanced reduction strategies
//! - Clause tier optimization
//! - Memory compaction

use crate::clause::{ClauseDatabase, ClauseId, ClauseTier};
use crate::literal::LBool;
#[allow(unused_imports)]
use crate::prelude::*;

/// Statistics for clause maintenance operations
#[derive(Debug, Clone, Default)]
pub struct MaintenanceStats {
    /// Number of duplicates removed
    pub duplicates_removed: usize,
    /// Number of tautologies detected
    pub tautologies_removed: usize,
    /// Number of clauses strengthened
    pub clauses_strengthened: usize,
    /// Number of tier promotions
    pub tier_promotions: usize,
    /// Number of tier demotions
    pub tier_demotions: usize,
    /// Total maintenance operations
    pub operations: usize,
}

impl MaintenanceStats {
    /// Display maintenance statistics
    pub fn display(&self) {
        println!("Clause Maintenance Statistics:");
        println!("  Operations: {}", self.operations);
        println!("  Duplicates removed: {}", self.duplicates_removed);
        println!("  Tautologies removed: {}", self.tautologies_removed);
        println!("  Clauses strengthened: {}", self.clauses_strengthened);
        println!("  Tier promotions: {}", self.tier_promotions);
        println!("  Tier demotions: {}", self.tier_demotions);
    }
}

/// Clause maintenance manager
#[derive(Debug)]
pub struct ClauseMaintenance {
    /// Statistics
    stats: MaintenanceStats,
    /// Clause IDs to clean
    cleanup_queue: Vec<ClauseId>,
}

impl Default for ClauseMaintenance {
    fn default() -> Self {
        Self::new()
    }
}

impl ClauseMaintenance {
    /// Create a new clause maintenance manager
    #[must_use]
    pub fn new() -> Self {
        Self {
            stats: MaintenanceStats::default(),
            cleanup_queue: Vec::new(),
        }
    }

    /// Get statistics
    #[must_use]
    pub fn stats(&self) -> &MaintenanceStats {
        &self.stats
    }

    /// Queue a clause for cleaning
    pub fn queue_for_cleanup(&mut self, clause_id: ClauseId) {
        self.cleanup_queue.push(clause_id);
    }

    /// Perform periodic maintenance on the clause database
    ///
    /// This performs various cleaning operations:
    /// - Remove duplicate literals
    /// - Detect and remove tautologies
    /// - Normalize clause representation
    /// - Update tier assignments based on usage
    pub fn periodic_maintenance(
        &mut self,
        clauses: &mut ClauseDatabase,
        assignments: &[LBool],
    ) -> Vec<ClauseId> {
        self.stats.operations += 1;
        let mut removed_clauses = Vec::new();

        // Process cleanup queue
        let queue: Vec<_> = self.cleanup_queue.drain(..).collect();
        for clause_id in queue {
            if clauses.get(clause_id).is_none_or(|c| c.deleted) {
                continue;
            }

            let old_len = clauses.get(clause_id).map_or(0, |c| c.lits.len());

            // Normalize clause (remove duplicates, sort, check tautology)
            if clauses.normalize(clause_id) {
                // Tautology detected - remove clause
                clauses.remove(clause_id);
                removed_clauses.push(clause_id);
                self.stats.tautologies_removed += 1;
                continue;
            }

            // Track if duplicates were removed
            if clauses
                .get(clause_id)
                .is_some_and(|c| c.lits.len() < old_len)
            {
                self.stats.duplicates_removed +=
                    old_len - clauses.get(clause_id).map_or(0, |c| c.lits.len());
            }

            // Strengthen clause by removing falsified literals
            if self.strengthen_clause(clause_id, clauses, assignments) {
                self.stats.clauses_strengthened += 1;
            }

            // Optimize tier based on usage and quality
            self.optimize_tier(clause_id, clauses);
        }

        // Compact the database periodically
        clauses.compact();

        removed_clauses
    }

    /// Strengthen a clause by removing falsified literals
    ///
    /// Returns true if the clause was modified
    fn strengthen_clause(
        &self,
        clause_id: ClauseId,
        clauses: &mut ClauseDatabase,
        assignments: &[LBool],
    ) -> bool {
        let Some(v) = clauses.get(clause_id) else {
            return false;
        };
        let original_len = v.lits.len();
        let lits: Vec<crate::literal::Lit> = v
            .lits
            .iter()
            .copied()
            .filter(|lit| {
                let var_idx = lit.var().index();
                if var_idx >= assignments.len() {
                    return true; // Keep unassigned variables
                }

                let value = assignments[var_idx];

                // Keep literal if variable is undefined
                if value == LBool::Undef {
                    return true;
                }

                // A literal is falsified if:
                // - Variable is True and literal is negative
                // - Variable is False and literal is positive
                let is_falsified = (value == LBool::True && lit.is_neg())
                    || (value == LBool::False && !lit.is_neg());

                !is_falsified
            })
            .collect();
        let shrunk = lits.len() < original_len;
        if shrunk {
            clauses.shrink(clause_id, &lits);
        }
        shrunk
    }

    /// Optimize clause tier based on usage and quality metrics
    fn optimize_tier(&mut self, clause_id: ClauseId, clauses: &mut ClauseDatabase) {
        let Some(v) = clauses.get(clause_id) else {
            return;
        };
        if !v.learned {
            return;
        }

        let old_tier = v.tier;
        let (usage, lbd, activity) = (v.usage_count, v.lbd, v.activity);

        // Promotion criteria:
        // - High usage count
        // - Low LBD (high quality)
        // - Small size

        let new_tier = if old_tier == ClauseTier::Local {
            // Promote Local -> Mid if used frequently or has good LBD
            if usage >= 3 || (lbd <= 3 && usage >= 2) {
                self.stats.tier_promotions += 1;
                ClauseTier::Mid
            } else {
                ClauseTier::Local
            }
        } else if old_tier == ClauseTier::Mid {
            // Promote Mid -> Core if very high usage or excellent LBD
            if usage >= 10 || lbd <= 2 || (lbd <= 3 && usage >= 5) {
                self.stats.tier_promotions += 1;
                ClauseTier::Core
            } else {
                ClauseTier::Mid
            }
        } else {
            old_tier
        };

        // Demotion criteria:
        // - Low activity for extended period
        // - High LBD with low usage

        let final_tier = if new_tier == ClauseTier::Mid && activity < 0.1 && usage < 2 {
            self.stats.tier_demotions += 1;
            ClauseTier::Local
        } else {
            new_tier
        };

        if final_tier != old_tier {
            clauses.set_tier(clause_id, final_tier);
            // Reset usage counter on tier change.
            clauses.reset_usage(clause_id);
        }
    }

    /// Advanced clause reduction strategy
    ///
    /// Identifies clauses to delete based on multiple criteria:
    /// - Activity
    /// - LBD
    /// - Tier
    /// - Size
    /// - Age (usage count as proxy)
    ///
    /// Returns a list of clause IDs that should be deleted
    pub fn select_clauses_for_deletion(
        &self,
        clauses: &ClauseDatabase,
        target_count: usize,
    ) -> Vec<ClauseId> {
        let mut candidates: Vec<(ClauseId, f64)> = Vec::new();

        // Collect learned clauses with quality scores
        for i in 0..clauses.num_learned() {
            let clause_id = ClauseId::new(i as u32);
            if let Some(clause) = clauses.get(clause_id) {
                if clause.deleted || !clause.learned {
                    continue;
                }

                // Skip Core tier clauses (protected)
                if clause.tier == ClauseTier::Core {
                    continue;
                }

                // Compute deletion priority (higher = more likely to delete)
                // Factors:
                // - Low activity (weight: 0.4)
                // - High LBD (weight: 0.3)
                // - Large size (weight: 0.2)
                // - Tier (weight: 0.1)

                let activity_score = 1.0 - clause.activity.min(1.0);
                let lbd_score = (clause.lbd as f64 / 20.0).min(1.0);
                let size_score = ((clause.len() - 2) as f64 / 20.0).min(1.0);
                let tier_score = match clause.tier {
                    ClauseTier::Core => 0.0,  // Protected
                    ClauseTier::Mid => 0.3,   // Less likely to delete
                    ClauseTier::Local => 1.0, // Most likely to delete
                };

                let score =
                    activity_score * 0.4 + lbd_score * 0.3 + size_score * 0.2 + tier_score * 0.1;

                candidates.push((clause_id, score));
            }
        }

        // Sort by score (highest first = most deletable)
        candidates.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(core::cmp::Ordering::Equal));

        // Return top candidates up to target_count
        candidates
            .into_iter()
            .take(target_count)
            .map(|(id, _)| id)
            .collect()
    }

    /// Reset statistics
    pub fn reset_stats(&mut self) {
        self.stats = MaintenanceStats::default();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clause::Clause;
    use crate::literal::{Lit, Var};

    #[test]
    fn test_maintenance_stats() {
        let mut maintenance = ClauseMaintenance::new();
        maintenance.stats.operations = 10;
        maintenance.stats.duplicates_removed = 5;

        let stats = maintenance.stats();
        assert_eq!(stats.operations, 10);
        assert_eq!(stats.duplicates_removed, 5);
    }

    #[test]
    fn test_tier_optimization() {
        let mut maintenance = ClauseMaintenance::new();
        let mut db = ClauseDatabase::new();
        let id = db.add_learned([Lit::pos(Var::new(0)), Lit::pos(Var::new(1))]);

        db.bump_usage(id);
        db.bump_usage(id);
        db.bump_usage(id);
        db.set_lbd(id, 3);

        maintenance.optimize_tier(id, &mut db);

        // Should be promoted from Local to Mid
        assert_eq!(db.get(id).expect("clause").tier, ClauseTier::Mid);
        assert_eq!(maintenance.stats.tier_promotions, 1);
    }

    #[test]
    fn test_clause_strengthening() {
        let maintenance = ClauseMaintenance::new();
        let mut db = ClauseDatabase::new();
        let id = db.add_learned([
            Lit::pos(Var::new(0)),
            Lit::pos(Var::new(1)),
            Lit::pos(Var::new(2)),
        ]);

        let mut assignments = vec![LBool::Undef; 3];
        assignments[1] = LBool::False; // Var(1) is false

        // Lit::pos(Var(1)) should be removed since Var(1) is false
        let modified = maintenance.strengthen_clause(id, &mut db, &assignments);
        assert!(modified);
        assert_eq!(db.get(id).expect("clause").lits.len(), 2);
    }

    #[test]
    fn test_deletion_selection() {
        let mut db = ClauseDatabase::new();
        let maintenance = ClauseMaintenance::new();

        // Add some learned clauses with different properties
        let mut c1 = Clause::learned([Lit::pos(Var::new(0)), Lit::pos(Var::new(1))]);
        c1.activity = 0.1; // Low activity
        c1.lbd = 10; // High LBD
        let _id1 = db.add(c1);

        let mut c2 = Clause::learned([Lit::pos(Var::new(2)), Lit::pos(Var::new(3))]);
        c2.activity = 0.9; // High activity
        c2.lbd = 2; // Low LBD
        c2.promote_to_core(); // Protected
        let _id2 = db.add(c2);

        let to_delete = maintenance.select_clauses_for_deletion(&db, 1);

        // Should select c1 for deletion (low activity, high LBD, not protected)
        assert_eq!(to_delete.len(), 1);
    }
}
