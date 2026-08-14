//! Clause Learning for CDCL(T) Solver.
//!
//! Implements sophisticated conflict-driven clause learning including:
//! - First UIP computation
//! - Conflict clause minimization
//! - Asserting clause generation
//! - Learned clause database management
//! - Clause subsumption and strengthening

#[allow(unused_imports)]
use crate::prelude::*;
use oxiz_core::ast::{TermId, TermManager};

/// Clause learning engine for CDCL.
pub struct ClauseLearner {
    /// Implication graph
    impl_graph: ImplicationGraph,
    /// Learned clause database
    learned_db: LearnedDatabase,
    /// Clause minimization engine
    minimizer: ClauseMinimizer,
    /// Configuration
    config: ClauseLearningConfig,
    /// Statistics
    stats: ClauseLearningStats,
}

/// Implication graph for conflict analysis.
#[derive(Debug, Clone)]
pub struct ImplicationGraph {
    /// Nodes: variable → implication node
    nodes: FxHashMap<TermId, ImplicationNode>,
    /// Adjacency list: variable → predecessors
    #[allow(dead_code)]
    predecessors: FxHashMap<TermId, Vec<TermId>>,
    /// Decision levels: variable → level
    levels: FxHashMap<TermId, usize>,
    /// Current decision level
    current_level: usize,
}

/// Node in the implication graph.
#[derive(Debug, Clone)]
pub struct ImplicationNode {
    /// Variable
    pub var: TermId,
    /// Assigned value
    pub value: bool,
    /// Decision level
    pub level: usize,
    /// Reason clause (None for decisions)
    pub reason: Option<ClauseId>,
    /// Is this a decision variable?
    pub is_decision: bool,
}

/// Clause identifier.
pub type ClauseId = usize;

/// Learned clause database.
#[derive(Debug, Clone)]
pub struct LearnedDatabase {
    /// Learned clauses
    clauses: Vec<LearnedClause>,
    /// Activity scores for LRU
    activity: Vec<f64>,
    /// Clause to ID mapping
    clause_map: FxHashMap<Vec<TermId>, ClauseId>,
    /// Bump increment for activity
    bump_increment: f64,
    /// Decay factor
    decay_factor: f64,
}

/// A learned clause.
#[derive(Debug, Clone)]
pub struct LearnedClause {
    /// Literals in the clause
    pub literals: Vec<TermId>,
    /// Asserting literal (first UIP)
    pub asserting_lit: TermId,
    /// Backtrack level
    pub backtrack_level: usize,
    /// Clause activity
    pub activity: f64,
    /// Is this clause locked (in conflict analysis)?
    pub locked: bool,
    /// Glue level (LBD)
    pub lbd: usize,
}

/// Clause minimization engine.
#[derive(Debug, Clone)]
pub struct ClauseMinimizer {
    /// Seen variables during minimization
    seen: FxHashSet<TermId>,
    /// Variables to analyze
    analyze_stack: Vec<TermId>,
    /// Minimization cache
    #[allow(dead_code)]
    cache: FxHashMap<TermId, bool>,
}

/// Configuration for clause learning.
#[derive(Debug, Clone)]
pub struct ClauseLearningConfig {
    /// Enable clause minimization
    pub enable_minimization: bool,
    /// Enable recursive minimization
    pub enable_recursive_minimization: bool,
    /// Enable clause subsumption
    pub enable_subsumption: bool,
    /// Enable clause strengthening
    pub enable_strengthening: bool,
    /// Maximum clause size for learning
    pub max_learned_size: usize,
    /// LBD threshold for keeping clauses
    pub lbd_threshold: usize,
    /// Activity decay factor
    pub activity_decay: f64,
}

impl Default for ClauseLearningConfig {
    fn default() -> Self {
        Self {
            enable_minimization: true,
            enable_recursive_minimization: true,
            enable_subsumption: true,
            enable_strengthening: true,
            max_learned_size: 1000,
            lbd_threshold: 5,
            activity_decay: 0.95,
        }
    }
}

/// Clause learning statistics.
#[derive(Debug, Clone, Default)]
pub struct ClauseLearningStats {
    /// Conflicts analyzed
    pub conflicts_analyzed: usize,
    /// Clauses learned
    pub clauses_learned: usize,
    /// Literals in learned clauses (before minimization)
    pub literals_before_minimization: usize,
    /// Literals after minimization
    pub literals_after_minimization: usize,
    /// Clauses subsumed
    pub clauses_subsumed: usize,
    /// Clauses strengthened
    pub clauses_strengthened: usize,
    /// UIP computations
    pub uip_computations: usize,
    /// Clause database reductions
    pub db_reductions: usize,
}

impl ClauseLearner {
    /// Create a new clause learner.
    pub fn new(config: ClauseLearningConfig) -> Self {
        Self {
            impl_graph: ImplicationGraph::new(),
            learned_db: LearnedDatabase::new(config.activity_decay),
            minimizer: ClauseMinimizer::new(),
            config,
            stats: ClauseLearningStats::default(),
        }
    }

    /// Analyze a conflict and learn a clause.
    pub fn analyze_conflict(
        &mut self,
        conflict_clause: ClauseId,
        _tm: &TermManager,
    ) -> Result<LearnedClause, String> {
        self.stats.conflicts_analyzed += 1;

        // Build initial conflict clause
        let conflict_lits = self.get_clause_literals(conflict_clause)?;

        // Compute First UIP
        let (learned_lits, asserting_lit, backtrack_level) =
            self.compute_first_uip(&conflict_lits)?;

        self.stats.uip_computations += 1;
        self.stats.literals_before_minimization += learned_lits.len();

        // Minimize clause
        let minimized_lits = if self.config.enable_minimization {
            self.minimize_clause(&learned_lits)?
        } else {
            learned_lits
        };

        self.stats.literals_after_minimization += minimized_lits.len();

        // Compute LBD (Literal Block Distance)
        let lbd = self.compute_lbd(&minimized_lits);

        // Create learned clause
        let learned = LearnedClause {
            literals: minimized_lits,
            asserting_lit,
            backtrack_level,
            activity: 0.0,
            locked: false,
            lbd,
        };

        self.stats.clauses_learned += 1;

        // Add to database
        self.learned_db.add_clause(learned.clone());

        Ok(learned)
    }

    /// Compute First UIP (Unique Implication Point).
    fn compute_first_uip(
        &mut self,
        conflict_lits: &[TermId],
    ) -> Result<(Vec<TermId>, TermId, usize), String> {
        let current_level = self.impl_graph.current_level;

        // Initialize with conflict clause
        let mut clause = conflict_lits.to_vec();
        let mut seen = FxHashSet::default();
        let mut counter = 0;

        // Count literals at current level
        for &lit in &clause {
            if self.impl_graph.get_level(lit) == current_level {
                counter += 1;
            }
            seen.insert(lit);
        }

        // Resolve until we have exactly one literal at current level
        let mut asserting_lit = TermId::from(0);

        while counter > 1 {
            // Find a literal to resolve on
            let resolve_lit = clause
                .iter()
                .copied()
                .find(|&lit| {
                    self.impl_graph.get_level(lit) == current_level
                        && !self.impl_graph.is_decision(lit)
                })
                .ok_or("No literal to resolve on")?;

            // Get reason clause
            let reason = self
                .impl_graph
                .get_reason(resolve_lit)
                .ok_or("No reason for propagated literal")?;

            let reason_lits = self.get_clause_literals(reason)?;

            // Resolve
            clause.retain(|&lit| lit != resolve_lit);
            counter -= 1;

            for &reason_lit in &reason_lits {
                if reason_lit != resolve_lit && !seen.contains(&reason_lit) {
                    clause.push(reason_lit);
                    seen.insert(reason_lit);

                    if self.impl_graph.get_level(reason_lit) == current_level {
                        counter += 1;
                    }
                }
            }
        }

        // Find the asserting literal (the one at current level)
        for &lit in &clause {
            if self.impl_graph.get_level(lit) == current_level {
                asserting_lit = lit;
                break;
            }
        }

        // Compute backtrack level (second highest level in clause)
        let mut levels: Vec<usize> = clause
            .iter()
            .map(|&lit| self.impl_graph.get_level(lit))
            .collect();
        levels.sort_unstable();
        levels.dedup();

        let backtrack_level = if levels.len() > 1 {
            levels[levels.len() - 2]
        } else {
            0
        };

        Ok((clause, asserting_lit, backtrack_level))
    }

    /// Minimize a learned clause.
    fn minimize_clause(&mut self, clause: &[TermId]) -> Result<Vec<TermId>, String> {
        if !self.config.enable_minimization {
            return Ok(clause.to_vec());
        }

        let mut minimized = clause.to_vec();

        // Remove redundant literals
        minimized.retain(|&lit| !self.is_redundant(lit, clause));

        // Recursive minimization
        if self.config.enable_recursive_minimization {
            minimized = self.recursive_minimize(&minimized)?;
        }

        Ok(minimized)
    }

    /// Check if a literal is redundant in a clause.
    fn is_redundant(&mut self, lit: TermId, clause: &[TermId]) -> bool {
        // Check if all literals in the reason of lit are in clause
        if let Some(reason) = self.impl_graph.get_reason(lit)
            && let Ok(reason_lits) = self.get_clause_literals(reason)
        {
            return reason_lits
                .iter()
                .all(|&r_lit| r_lit == lit || clause.contains(&r_lit));
        }

        false
    }

    /// Recursive clause minimization.
    fn recursive_minimize(&mut self, clause: &[TermId]) -> Result<Vec<TermId>, String> {
        self.minimizer.seen.clear();
        self.minimizer.analyze_stack.clear();

        // Mark all clause literals as seen
        for &lit in clause {
            self.minimizer.seen.insert(lit);
        }

        let mut minimized = Vec::new();

        for &lit in clause {
            if !self.minimizer.can_remove(lit, &self.impl_graph)? {
                minimized.push(lit);
            }
        }

        Ok(minimized)
    }

    /// Compute Literal Block Distance (LBD/Glue).
    fn compute_lbd(&self, clause: &[TermId]) -> usize {
        let mut levels = FxHashSet::default();

        for &lit in clause {
            let level = self.impl_graph.get_level(lit);
            levels.insert(level);
        }

        levels.len()
    }

    /// Get literals of a clause.
    ///
    /// A [`ClauseId`] indexes [`LearnedDatabase::clauses`]. An id that is not
    /// in the database is an error, not an empty clause: callers treat an
    /// empty reason as "vacuously covered", so returning one for an unknown
    /// id would let conflict minimization delete literals it has no
    /// justification for. (This routine used to return `Ok(vec![])`
    /// unconditionally, which did exactly that for *every* id.)
    fn get_clause_literals(&self, clause_id: ClauseId) -> Result<Vec<TermId>, String> {
        self.learned_db
            .clauses
            .get(clause_id)
            .map(|clause| clause.literals.clone())
            .ok_or_else(|| format!("unknown clause id {clause_id}"))
    }

    /// Subsume redundant clauses.
    pub fn subsume_clauses(&mut self) -> Result<(), String> {
        if !self.config.enable_subsumption {
            return Ok(());
        }

        let mut to_remove = Vec::new();

        // Check each pair of clauses
        for i in 0..self.learned_db.clauses.len() {
            for j in (i + 1)..self.learned_db.clauses.len() {
                if self.learned_db.clauses[i].locked || self.learned_db.clauses[j].locked {
                    continue;
                }

                let clause_i = &self.learned_db.clauses[i].literals;
                let clause_j = &self.learned_db.clauses[j].literals;

                // Check if clause_i subsumes clause_j
                if Self::subsumes(clause_i, clause_j) {
                    to_remove.push(j);
                    self.stats.clauses_subsumed += 1;
                } else if Self::subsumes(clause_j, clause_i) {
                    to_remove.push(i);
                    self.stats.clauses_subsumed += 1;
                    break;
                }
            }
        }

        // Remove subsumed clauses
        to_remove.sort_unstable();
        to_remove.dedup();
        for &idx in to_remove.iter().rev() {
            self.learned_db.clauses.remove(idx);
            self.learned_db.activity.remove(idx);
        }

        Ok(())
    }

    /// Check if clause A subsumes clause B.
    fn subsumes(a: &[TermId], b: &[TermId]) -> bool {
        if a.len() > b.len() {
            return false;
        }

        let b_set: FxHashSet<TermId> = b.iter().copied().collect();

        a.iter().all(|lit| b_set.contains(lit))
    }

    /// Strengthen clauses by removing literals.
    pub fn strengthen_clauses(&mut self) -> Result<(), String> {
        if !self.config.enable_strengthening {
            return Ok(());
        }

        for idx in 0..self.learned_db.clauses.len() {
            if self.learned_db.clauses[idx].locked {
                continue;
            }

            // Clone the literals to avoid simultaneous borrow of self (needed because
            // can_remove_literal borrows self.impl_graph immutably while we modify the clause).
            let original_literals = self.learned_db.clauses[idx].literals.clone();
            let original_len = original_literals.len();

            let mut new_literals = Vec::with_capacity(original_len);
            for &lit in &original_literals {
                if !self.can_remove_literal(lit, &original_literals) {
                    new_literals.push(lit);
                }
            }

            if new_literals.len() < original_len {
                self.learned_db.clauses[idx].literals = new_literals;
                self.stats.clauses_strengthened += 1;
            }
        }

        Ok(())
    }

    /// Check if a literal can be removed from a clause.
    ///
    /// A literal `lit` is removable when every literal in its reason clause
    /// (other than `lit` itself) is already in `clause`.  The check is
    /// recursive: a peer literal that is not directly in `clause` may itself
    /// be removable, allowing deeper subsumption.
    ///
    /// A `visited` set guards against revisiting nodes; implication graphs in
    /// standard CDCL are acyclic, but the guard is kept for robustness.
    ///
    /// The walk is driven by an explicit heap stack rather than the native
    /// call stack. Its depth is the length of an implication chain, which is
    /// bounded only by the number of assigned literals in the problem -- i.e.
    /// fully input-controlled -- and the answer is a bare `bool` with no error
    /// channel, so a depth cap here could only ever turn "cannot remove" into
    /// a silently wrong "can remove" (or vice versa) and corrupt a learned
    /// clause. Frames are visited in exactly the order the previous recursion
    /// visited them, and the first `false` aborts the whole walk, so the
    /// `visited`-set pruning behaves identically.
    fn can_remove_literal(&self, lit: TermId, clause: &[TermId]) -> bool {
        let mut visited = FxHashSet::default();

        let mut stack: Vec<RemovalFrame> = Vec::new();
        match self.enter_removal(lit, &mut visited) {
            RemovalStep::Done(answer) => return answer,
            RemovalStep::Descend(frame) => stack.push(frame),
        }

        while let Some(mut frame) = stack.pop() {
            let mut descend: Option<RemovalFrame> = None;

            // Every literal in the reason clause (other than `frame.lit`
            // itself) must either already be present in `clause` or be
            // removable in turn.
            while frame.next < frame.reason_lits.len() {
                let other_lit = frame.reason_lits[frame.next];
                frame.next += 1;

                if other_lit == frame.lit || clause.contains(&other_lit) {
                    continue;
                }

                match self.enter_removal(other_lit, &mut visited) {
                    RemovalStep::Done(true) => continue,
                    RemovalStep::Done(false) => return false,
                    RemovalStep::Descend(child) => {
                        descend = Some(child);
                        break;
                    }
                }
            }

            if let Some(child) = descend {
                stack.push(frame);
                stack.push(child);
            }
            // Otherwise the frame's literals are exhausted: it yields `true`,
            // which the parent frame simply continues past.
        }

        true
    }

    /// Classify one node of the [`Self::can_remove_literal`] walk: either the
    /// answer for that node is immediate, or it has a reason clause whose
    /// literals must be examined.
    fn enter_removal(&self, lit: TermId, visited: &mut FxHashSet<TermId>) -> RemovalStep {
        if !visited.insert(lit) {
            // Already visited this node – avoid infinite looping.
            return RemovalStep::Done(true);
        }

        // Decision literals have no reason clause and cannot be removed.
        let Some(reason_id) = self.impl_graph.get_reason(lit) else {
            return RemovalStep::Done(false);
        };

        // Retrieve the reason clause's literals.  If the underlying clause
        // database is not yet wired up, `get_clause_literals` returns an empty
        // vec, which makes the (vacuous) per-literal check below succeed –
        // harmless because no real literal will be removed from an empty
        // reason clause.
        let Ok(reason_lits) = self.get_clause_literals(reason_id) else {
            return RemovalStep::Done(false);
        };

        RemovalStep::Descend(RemovalFrame {
            lit,
            reason_lits,
            next: 0,
        })
    }

    /// Reduce clause database.
    pub fn reduce_database(&mut self) -> Result<(), String> {
        self.stats.db_reductions += 1;

        // Remove low-activity clauses
        self.learned_db.reduce();

        Ok(())
    }

    /// Bump clause activity.
    pub fn bump_clause(&mut self, clause_id: ClauseId) {
        self.learned_db.bump_activity(clause_id);
    }

    /// Get statistics.
    pub fn stats(&self) -> &ClauseLearningStats {
        &self.stats
    }
}

/// One suspended node of the [`ClauseLearner::can_remove_literal`] walk.
///
/// Owning the reason literals plus the index of the next one to examine is
/// what lets the walk be resumed after descending into a child, i.e. what
/// replaces the native call frame.
struct RemovalFrame {
    /// The literal whose reason clause this frame is scanning.
    lit: TermId,
    /// Literals of that reason clause.
    reason_lits: Vec<TermId>,
    /// Index of the next literal in `reason_lits` to examine.
    next: usize,
}

/// Result of classifying one node of the literal-removal walk.
enum RemovalStep {
    /// The node's answer is already known; no descent needed.
    Done(bool),
    /// The node has a reason clause that must be scanned.
    Descend(RemovalFrame),
}

impl ImplicationGraph {
    /// Create a new implication graph.
    pub fn new() -> Self {
        Self {
            nodes: FxHashMap::default(),
            predecessors: FxHashMap::default(),
            levels: FxHashMap::default(),
            current_level: 0,
        }
    }

    /// Add a node to the graph.
    pub fn add_node(
        &mut self,
        var: TermId,
        value: bool,
        level: usize,
        reason: Option<ClauseId>,
        is_decision: bool,
    ) {
        self.nodes.insert(
            var,
            ImplicationNode {
                var,
                value,
                level,
                reason,
                is_decision,
            },
        );

        self.levels.insert(var, level);
    }

    /// Get decision level of a variable.
    pub fn get_level(&self, var: TermId) -> usize {
        self.levels.get(&var).copied().unwrap_or(0)
    }

    /// Check if a variable is a decision.
    pub fn is_decision(&self, var: TermId) -> bool {
        self.nodes.get(&var).is_some_and(|n| n.is_decision)
    }

    /// Get reason clause for a variable.
    pub fn get_reason(&self, var: TermId) -> Option<ClauseId> {
        self.nodes.get(&var).and_then(|n| n.reason)
    }

    /// Set current decision level.
    pub fn set_level(&mut self, level: usize) {
        self.current_level = level;
    }
}

impl LearnedDatabase {
    /// Create a new learned database.
    pub fn new(decay_factor: f64) -> Self {
        Self {
            clauses: Vec::new(),
            activity: Vec::new(),
            clause_map: FxHashMap::default(),
            bump_increment: 1.0,
            decay_factor,
        }
    }

    /// Add a clause to the database.
    pub fn add_clause(&mut self, clause: LearnedClause) {
        let clause_id = self.clauses.len();

        self.clause_map.insert(clause.literals.clone(), clause_id);
        self.activity.push(clause.activity);
        self.clauses.push(clause);
    }

    /// Bump clause activity.
    pub fn bump_activity(&mut self, clause_id: ClauseId) {
        if clause_id < self.activity.len() {
            self.activity[clause_id] += self.bump_increment;

            // Rescale if needed
            if self.activity[clause_id] > 1e20 {
                for act in &mut self.activity {
                    *act *= 1e-20;
                }
                self.bump_increment *= 1e-20;
            }
        }
    }

    /// Decay all activities.
    pub fn decay(&mut self) {
        self.bump_increment /= self.decay_factor;
    }

    /// Reduce database by removing low-activity clauses.
    pub fn reduce(&mut self) {
        let mut sorted_indices: Vec<usize> = (0..self.clauses.len()).collect();

        // Sort by activity (descending)
        sorted_indices.sort_by(|&a, &b| {
            self.activity[b]
                .partial_cmp(&self.activity[a])
                .unwrap_or(core::cmp::Ordering::Equal)
        });

        // Keep top 50%
        let keep_count = self.clauses.len() / 2;

        let mut to_keep = FxHashSet::default();
        for &idx in sorted_indices.iter().take(keep_count) {
            to_keep.insert(idx);
        }

        // Also keep locked clauses
        for (idx, clause) in self.clauses.iter().enumerate() {
            if clause.locked {
                to_keep.insert(idx);
            }
        }

        // Rebuild database
        let mut new_clauses = Vec::new();
        let mut new_activity = Vec::new();

        for (idx, clause) in self.clauses.iter().enumerate() {
            if to_keep.contains(&idx) {
                new_clauses.push(clause.clone());
                new_activity.push(self.activity[idx]);
            }
        }

        self.clauses = new_clauses;
        self.activity = new_activity;
        self.clause_map.clear();

        // Rebuild map
        for (idx, clause) in self.clauses.iter().enumerate() {
            self.clause_map.insert(clause.literals.clone(), idx);
        }
    }
}

impl ClauseMinimizer {
    /// Create a new clause minimizer.
    pub fn new() -> Self {
        Self {
            seen: FxHashSet::default(),
            analyze_stack: Vec::new(),
            cache: FxHashMap::default(),
        }
    }

    /// Check if a literal can be removed.
    fn can_remove(&mut self, _lit: TermId, _graph: &ImplicationGraph) -> Result<bool, String> {
        // Simplified: would do recursive analysis
        Ok(false)
    }
}

impl Default for ClauseLearner {
    fn default() -> Self {
        Self::new(ClauseLearningConfig::default())
    }
}

impl Default for ImplicationGraph {
    fn default() -> Self {
        Self::new()
    }
}

impl Default for ClauseMinimizer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_clause_learner() {
        let learner = ClauseLearner::default();
        assert_eq!(learner.stats.conflicts_analyzed, 0);
    }

    #[test]
    fn test_implication_graph() {
        let mut graph = ImplicationGraph::new();

        let var = TermId::from(1);
        graph.add_node(var, true, 1, None, true);

        assert_eq!(graph.get_level(var), 1);
        assert!(graph.is_decision(var));
    }

    #[test]
    fn test_learned_database() {
        let mut db = LearnedDatabase::new(0.95);

        let clause = LearnedClause {
            literals: vec![TermId::from(1), TermId::from(2)],
            asserting_lit: TermId::from(1),
            backtrack_level: 0,
            activity: 0.0,
            locked: false,
            lbd: 2,
        };

        db.add_clause(clause);
        assert_eq!(db.clauses.len(), 1);
    }

    #[test]
    fn test_subsumption() {
        let a = vec![TermId::from(1), TermId::from(2)];
        let b = vec![TermId::from(1), TermId::from(2), TermId::from(3)];

        assert!(ClauseLearner::subsumes(&a, &b));
        assert!(!ClauseLearner::subsumes(&b, &a));
    }

    #[test]
    fn test_lbd_computation() {
        let learner = ClauseLearner::default();

        let clause = vec![TermId::from(1), TermId::from(2), TermId::from(3)];
        let lbd = learner.compute_lbd(&clause);

        // LBD depends on decision levels, which are 0 by default
        assert_eq!(lbd, 1);
    }

    /// Build a chain of implications `lit_i` <- clause `[lit_i, lit_{i+1}]`,
    /// so removing `lit_0` requires walking the whole chain. The walk used to
    /// be recursive and overflowed on a chain the size of a real trail.
    fn build_implication_chain(learner: &mut ClauseLearner, chain: u32) {
        for var in 0..=chain {
            let literals = if var == chain {
                vec![TermId::from(var)]
            } else {
                vec![TermId::from(var), TermId::from(var + 1)]
            };
            let clause_id = learner.learned_db.clauses.len();
            learner.learned_db.add_clause(LearnedClause {
                literals,
                asserting_lit: TermId::from(var),
                backtrack_level: 0,
                activity: 0.0,
                locked: false,
                lbd: 1,
            });
            learner
                .impl_graph
                .add_node(TermId::from(var), true, 0, Some(clause_id), false);
        }
    }

    #[test]
    fn can_remove_literal_survives_a_long_implication_chain_on_a_small_stack() {
        // Stack and chain length scale together (1 MiB/100k -> 128 KiB/12.5k):
        // the ~10 B-per-frame threshold is the pin, so never raise one alone.
        const CHAIN: u32 = 12_500;

        let handle = std::thread::Builder::new()
            .stack_size(1 << 17)
            .spawn(|| {
                let mut learner = ClauseLearner::default();
                build_implication_chain(&mut learner, CHAIN);
                learner.can_remove_literal(TermId::from(0), &[])
            })
            .expect("spawning the worker thread should succeed");

        assert!(handle.join().expect("the walk must not overflow"));
    }

    /// Semantic pin: a decision literal has no reason clause and can never be
    /// removed.
    #[test]
    fn can_remove_literal_keeps_a_decision_literal() {
        let mut learner = ClauseLearner::default();
        learner
            .impl_graph
            .add_node(TermId::from(1), true, 0, None, true);

        assert!(!learner.can_remove_literal(TermId::from(1), &[]));
    }

    /// Semantic pin: a literal whose reason clause is covered by the clause
    /// being strengthened is removable.
    #[test]
    fn can_remove_literal_accepts_a_covered_reason() {
        let mut learner = ClauseLearner::default();
        learner.learned_db.add_clause(LearnedClause {
            literals: vec![TermId::from(1), TermId::from(2)],
            asserting_lit: TermId::from(1),
            backtrack_level: 0,
            activity: 0.0,
            locked: false,
            lbd: 1,
        });
        learner
            .impl_graph
            .add_node(TermId::from(1), true, 0, Some(0), false);

        assert!(learner.can_remove_literal(TermId::from(1), &[TermId::from(2)]));
    }

    /// A clause id that is not in the database is an error, not an empty
    /// clause: an empty reason reads as "vacuously covered" and would delete
    /// the literal.
    #[test]
    fn unknown_clause_id_is_an_error_not_an_empty_clause() {
        let mut learner = ClauseLearner::default();
        learner
            .impl_graph
            .add_node(TermId::from(1), true, 0, Some(42), false);

        assert!(learner.get_clause_literals(42).is_err());
        assert!(!learner.can_remove_literal(TermId::from(1), &[]));
    }
}
