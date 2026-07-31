//! Theory Conflict Resolution for Combination.
//!
//! This module handles conflicts that arise from theory combination:
//! - Multi-theory conflict analysis
//! - Minimal explanation generation
//! - Conflict minimization
//! - Theory blame assignment
//! - Conflict-driven clause learning (CDCL) for theory combination
//!
//! ## Theory Conflicts
//!
//! In theory combination, conflicts can arise from:
//! - A single theory detecting inconsistency
//! - Incompatible propagations from multiple theories
//! - Violation of shared term constraints
//!
//! ## Conflict Analysis
//!
//! When a conflict occurs, we perform analysis to:
//! - Identify the root cause
//! - Generate a minimal explanation
//! - Learn conflict clauses to prevent similar conflicts
//! - Determine the backtrack level
//!
//! ## References
//!
//! - Silva & Sakallah (1996): "GRASP: A Search Algorithm for Propositional Satisfiability"
//! - Nieuwenhuis, Oliveras, Tinelli (2006): "Solving SAT and SAT Modulo Theories"
//! - Z3's `smt/theory_combination.cpp`, `smt/smt_conflict.cpp`

/// Term identifier.
#[allow(unused_imports)]
use crate::prelude::*;
/// Term identifier for conflict resolution.
pub type TermId = u32;

/// Theory identifier.
pub type TheoryId = u32;

/// Decision level.
pub type DecisionLevel = u32;

/// Literal (term with polarity).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Literal {
    /// Term.
    pub term: TermId,
    /// Polarity.
    pub polarity: bool,
}

impl Literal {
    /// Create positive literal.
    pub fn positive(term: TermId) -> Self {
        Self {
            term,
            polarity: true,
        }
    }

    /// Create negative literal.
    pub fn negative(term: TermId) -> Self {
        Self {
            term,
            polarity: false,
        }
    }

    /// Negate literal.
    pub fn negate(self) -> Self {
        Self {
            term: self.term,
            polarity: !self.polarity,
        }
    }
}

/// Equality between terms.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Equality {
    /// Left-hand side.
    pub lhs: TermId,
    /// Right-hand side.
    pub rhs: TermId,
}

impl Equality {
    /// Create new equality.
    pub fn new(lhs: TermId, rhs: TermId) -> Self {
        if lhs <= rhs {
            Self { lhs, rhs }
        } else {
            Self { lhs: rhs, rhs: lhs }
        }
    }
}

/// Explanation for a propagation or conflict.
#[derive(Debug, Clone)]
pub enum Explanation {
    /// Given as input.
    Given,

    /// Theory propagation.
    TheoryPropagation {
        /// Source theory.
        theory: TheoryId,
        /// Antecedent literals.
        antecedents: Vec<Literal>,
    },

    /// Equality propagation.
    EqualityPropagation {
        /// Equalities used.
        equalities: Vec<Equality>,
        /// Supporting literals.
        support: Vec<Literal>,
    },

    /// Transitivity.
    Transitivity {
        /// Chain of equalities.
        chain: Vec<Equality>,
    },

    /// Congruence.
    Congruence {
        /// Function applications.
        function: TermId,
        /// Argument equalities.
        arg_equalities: Vec<Equality>,
    },
}

/// Theory conflict.
#[derive(Debug, Clone)]
pub struct TheoryConflict {
    /// Theory that detected the conflict.
    pub theory: TheoryId,

    /// Conflicting literals.
    pub literals: Vec<Literal>,

    /// Explanation for the conflict.
    pub explanation: Explanation,

    /// Decision level where conflict occurred.
    pub level: DecisionLevel,
}

/// Conflict clause learned from analysis.
#[derive(Debug, Clone)]
pub struct ConflictClause {
    /// Literals in the clause.
    pub literals: Vec<Literal>,

    /// UIP (unique implication point) literal.
    pub uip: Option<Literal>,

    /// Backtrack level.
    pub backtrack_level: DecisionLevel,

    /// Theories involved.
    pub theories: FxHashSet<TheoryId>,

    /// Activity score (for clause deletion).
    pub activity: f64,
}

/// Conflict analysis result.
#[derive(Debug, Clone)]
pub struct ConflictAnalysis {
    /// Learned clause.
    pub clause: ConflictClause,

    /// Minimal explanation.
    pub explanation: Explanation,

    /// Theories responsible.
    pub blamed_theories: FxHashSet<TheoryId>,
}

/// Configuration for conflict resolution.
#[derive(Debug, Clone)]
pub struct ConflictResolutionConfig {
    /// Enable conflict minimization.
    pub enable_minimization: bool,

    /// Enable UIP-based learning.
    pub enable_uip: bool,

    /// Minimization algorithm.
    pub minimization_algorithm: MinimizationAlgorithm,

    /// Maximum resolution steps.
    pub max_resolution_steps: usize,

    /// Enable theory blame tracking.
    pub track_theory_blame: bool,

    /// Enable conflict clause learning.
    pub enable_learning: bool,
}

impl Default for ConflictResolutionConfig {
    fn default() -> Self {
        Self {
            enable_minimization: true,
            enable_uip: true,
            minimization_algorithm: MinimizationAlgorithm::Recursive,
            max_resolution_steps: 1000,
            track_theory_blame: true,
            enable_learning: true,
        }
    }
}

/// Minimization algorithm for conflict clauses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MinimizationAlgorithm {
    /// No minimization.
    None,
    /// Simple minimization (remove redundant literals).
    Simple,
    /// Recursive minimization.
    Recursive,
    /// Binary resolution minimization.
    BinaryResolution,
}

/// Statistics for conflict resolution.
#[derive(Debug, Clone, Default)]
pub struct ConflictResolutionStats {
    /// Total conflicts analyzed.
    pub conflicts_analyzed: u64,
    /// Clauses learned.
    pub clauses_learned: u64,
    /// Literals minimized away.
    pub literals_minimized: u64,
    /// UIP conflicts.
    pub uip_conflicts: u64,
    /// Resolution steps performed.
    pub resolution_steps: u64,
    /// Theory blames assigned.
    pub theory_blames: u64,
}

/// Conflict resolution engine.
pub struct ConflictResolver {
    /// Configuration.
    config: ConflictResolutionConfig,

    /// Statistics.
    stats: ConflictResolutionStats,

    /// Assignment trail.
    trail: Vec<(Literal, DecisionLevel, Explanation)>,

    /// Literal to trail position.
    literal_position: FxHashMap<Literal, usize>,

    /// Decision level boundaries in trail.
    level_boundaries: FxHashMap<DecisionLevel, usize>,

    /// Current decision level.
    current_level: DecisionLevel,

    /// Learned clauses.
    learned_clauses: Vec<ConflictClause>,

    /// Theory blame counters.
    theory_blame: FxHashMap<TheoryId, u64>,

    /// Boolean atom representing each equality premise.
    ///
    /// [`Explanation::Transitivity`], [`Explanation::Congruence`] and
    /// [`Explanation::EqualityPropagation`] carry their premises as
    /// [`Equality`] values, but a reason is a list of [`Literal`]s, and a
    /// literal names a *term*.  The embedder therefore tells the resolver
    /// which term is the atom `lhs = rhs` (see
    /// [`Self::register_equality_atom`]); without that mapping an equality
    /// premise cannot be named in a learned clause at all, and
    /// [`Self::get_reason`] says so with an error rather than dropping the
    /// premise.
    equality_atoms: FxHashMap<Equality, TermId>,
}

/// One suspended node of the [`ConflictResolver::is_redundant`] walk.
struct RedundancyFrame {
    /// The literal whose reason is being scanned.
    literal: Literal,
    /// The literals of that reason.
    reason: Vec<Literal>,
    /// Index of the next reason literal to examine.
    next: usize,
}

/// Result of classifying one node of the redundancy walk.
enum RedundancyStep {
    /// The answer for this node is already known.
    Done(bool),
    /// The node has a reason that must be scanned.
    Descend(RedundancyFrame),
}

impl ConflictResolver {
    /// Create new conflict resolver.
    pub fn new() -> Self {
        Self::with_config(ConflictResolutionConfig::default())
    }

    /// Create with configuration.
    pub fn with_config(config: ConflictResolutionConfig) -> Self {
        let mut level_boundaries = FxHashMap::default();
        // Initialize level 0 boundary at position 0
        level_boundaries.insert(0, 0);

        Self {
            config,
            stats: ConflictResolutionStats::default(),
            trail: Vec::new(),
            literal_position: FxHashMap::default(),
            level_boundaries,
            current_level: 0,
            learned_clauses: Vec::new(),
            theory_blame: FxHashMap::default(),
            equality_atoms: FxHashMap::default(),
        }
    }

    /// Record the boolean atom that represents the equality `equality`.
    ///
    /// Equality-carrying explanations ([`Explanation::Transitivity`],
    /// [`Explanation::Congruence`], [`Explanation::EqualityPropagation`]) can
    /// only contribute reason *literals* for equalities registered here.  The
    /// mapping is a naming table, not trail state: it survives
    /// [`Self::backtrack`] and is discarded only by [`Self::clear`].
    pub fn register_equality_atom(&mut self, equality: Equality, atom: TermId) {
        self.equality_atoms.insert(equality, atom);
    }

    /// The boolean atom registered for `equality`, if any.
    #[must_use]
    pub fn equality_atom(&self, equality: Equality) -> Option<TermId> {
        self.equality_atoms.get(&equality).copied()
    }

    /// Get statistics.
    pub fn stats(&self) -> &ConflictResolutionStats {
        &self.stats
    }

    /// Add assignment to trail.
    pub fn add_assignment(
        &mut self,
        literal: Literal,
        level: DecisionLevel,
        explanation: Explanation,
    ) {
        let position = self.trail.len();
        self.trail.push((literal, level, explanation));
        self.literal_position.insert(literal, position);

        self.level_boundaries.entry(level).or_insert(position);
    }

    /// Push decision level.
    pub fn push_decision_level(&mut self) {
        self.current_level += 1;
    }

    /// Backtrack to decision level.
    pub fn backtrack(&mut self, level: DecisionLevel) -> Result<(), String> {
        if level > self.current_level {
            return Err("Cannot backtrack to future level".to_string());
        }

        // Find position to backtrack to
        let backtrack_pos = self
            .level_boundaries
            .get(&level)
            .copied()
            .unwrap_or(self.trail.len());

        // Remove assignments above this level
        self.trail.truncate(backtrack_pos);

        // Rebuild literal position map
        self.literal_position.clear();
        for (i, &(literal, _, _)) in self.trail.iter().enumerate() {
            self.literal_position.insert(literal, i);
        }

        // Remove level boundaries above this level
        self.level_boundaries.retain(|&l, _| l <= level);

        self.current_level = level;
        Ok(())
    }

    /// Analyze a theory conflict.
    pub fn analyze_conflict(
        &mut self,
        conflict: TheoryConflict,
    ) -> Result<ConflictAnalysis, String> {
        self.stats.conflicts_analyzed += 1;

        if self.config.track_theory_blame {
            *self.theory_blame.entry(conflict.theory).or_insert(0) += 1;
            self.stats.theory_blames += 1;
        }

        // Extract conflict literals
        let mut conflict_literals = conflict.literals.clone();

        // Perform resolution to find UIP if enabled
        if self.config.enable_uip {
            conflict_literals = self.find_uip(&conflict_literals, conflict.level)?;
            self.stats.uip_conflicts += 1;
        }

        // Minimize conflict clause
        if self.config.enable_minimization {
            let before_size = conflict_literals.len();
            conflict_literals = self.minimize_conflict(&conflict_literals)?;
            let after_size = conflict_literals.len();
            self.stats.literals_minimized += (before_size - after_size) as u64;
        }

        // Determine backtrack level
        let backtrack_level = self.compute_backtrack_level(&conflict_literals, conflict.level)?;

        // Build learned clause
        let clause = ConflictClause {
            literals: conflict_literals.clone(),
            uip: self.find_uip_literal(&conflict_literals),
            backtrack_level,
            theories: {
                let mut theories = FxHashSet::default();
                theories.insert(conflict.theory);
                theories
            },
            activity: 1.0,
        };

        // Learn clause if enabled
        if self.config.enable_learning {
            self.learned_clauses.push(clause.clone());
            self.stats.clauses_learned += 1;
        }

        Ok(ConflictAnalysis {
            clause,
            explanation: conflict.explanation,
            blamed_theories: {
                let mut theories = FxHashSet::default();
                theories.insert(conflict.theory);
                theories
            },
        })
    }

    /// Find UIP (Unique Implication Point) using resolution.
    fn find_uip(
        &mut self,
        literals: &[Literal],
        level: DecisionLevel,
    ) -> Result<Vec<Literal>, String> {
        let mut current_clause: FxHashSet<Literal> = literals.iter().copied().collect();
        let mut seen = FxHashSet::default();
        let mut counter = 0;

        // Count literals at current level
        for &lit in &current_clause {
            if self.get_decision_level(lit) == Some(level) {
                counter += 1;
            }
        }

        // Resolution loop
        for _ in 0..self.config.max_resolution_steps {
            self.stats.resolution_steps += 1;

            if counter <= 1 {
                break; // Found UIP
            }

            // Find next literal to resolve.  Running out of candidates is not
            // a failure: `current_clause` is a resolvent of the conflict and
            // its reasons at every step, so it is implied by the constraint
            // set whether or not a UIP was reached.  Stopping here yields a
            // sound (if weaker) learned clause; the alternative -- resolving
            // on a literal that has no reason -- would delete it from the
            // clause and is exactly what makes a learned clause unsound.
            let Ok(resolve_lit) = self.find_resolution_literal(&current_clause, level, &seen)
            else {
                break;
            };
            seen.insert(resolve_lit);

            // Get reason for this literal.  A literal with no reason (a
            // decision, or one whose explanation names an unnameable premise)
            // cannot be resolved away: keep it in the clause and look for
            // another candidate.  `seen` grows every iteration, so the search
            // still terminates.
            let Ok(reason) = self.get_reason(resolve_lit) else {
                continue;
            };

            // Perform resolution
            current_clause.remove(&resolve_lit);
            counter -= 1;

            for &lit in &reason {
                if !current_clause.contains(&lit) {
                    current_clause.insert(lit);
                    if self.get_decision_level(lit) == Some(level) {
                        counter += 1;
                    }
                }
            }
        }

        Ok(current_clause.into_iter().collect())
    }

    /// Find literal for resolution.
    fn find_resolution_literal(
        &self,
        clause: &FxHashSet<Literal>,
        level: DecisionLevel,
        seen: &FxHashSet<Literal>,
    ) -> Result<Literal, String> {
        // Find last assigned literal at current level that hasn't been seen
        for &(literal, lit_level, _) in self.trail.iter().rev() {
            if lit_level == level && clause.contains(&literal) && !seen.contains(&literal) {
                return Ok(literal);
            }
        }

        Err("No resolution literal found".to_string())
    }

    /// Get decision level for a literal.
    fn get_decision_level(&self, literal: Literal) -> Option<DecisionLevel> {
        self.literal_position
            .get(&literal)
            .and_then(|&pos| self.trail.get(pos))
            .map(|(_, level, _)| *level)
    }

    /// Get reason (explanation) for a literal: the premises that imply it,
    /// as literals.
    ///
    /// An *empty* reason is not a neutral answer here — it states that the
    /// literal is entailed unconditionally, which makes it resolvable away in
    /// [`Self::find_uip`] and vacuously redundant in [`Self::is_redundant`],
    /// i.e. deletable from a learned clause.  Deleting a literal that is in
    /// fact conditional turns the learned clause into a non-implied one, so
    /// every kind below either produces its real premises or fails; no kind
    /// falls through to `Ok(Vec::new())`, and the match is exhaustive so a
    /// future kind cannot inherit such a fallthrough by default.
    ///
    /// Per kind:
    ///
    /// * [`Explanation::TheoryPropagation`] and
    ///   [`Explanation::EqualityPropagation`] carry literal premises
    ///   directly (`antecedents` / `support`); `EqualityPropagation`
    ///   additionally carries `equalities`, which are premises just as much
    ///   as `support` is and are now included instead of discarded.
    /// * [`Explanation::Transitivity`] and [`Explanation::Congruence`] carry
    ///   their premises as [`Equality`] values — the chain links and the
    ///   argument equalities respectively.  They are named through
    ///   [`Self::register_equality_atom`]; an unregistered equality is an
    ///   error, never a dropped premise.  (The congruence head `function` is
    ///   the term the rule concludes about, not a premise.)  An *empty*
    ///   chain or argument list is a degenerate explanation that proves
    ///   nothing, and is likewise an error rather than a licence to delete
    ///   the literal.
    /// * [`Explanation::Given`] is an input assertion. At level 0 that is
    ///   genuinely unconditional — the standard CDCL rule that level-0
    ///   assignments may be removed from a learned clause — so its reason is
    ///   the empty premise set, stated deliberately and only there.  Above
    ///   level 0 the same explanation marks a *decision*: it has no premises
    ///   to resolve on and must stay in the clause, so it is an error.
    ///
    /// The equality premises are iterated flatly: unlike
    /// [`crate::combination::equality_propagation::Explanation`], this
    /// explanation type is not self-nesting, so there is no sub-explanation
    /// tree to walk and no stack to keep.
    ///
    /// # Errors
    ///
    /// Returns `Err` when the literal has no reason to resolve on: it is not
    /// on the trail, it is a decision, or its explanation names a premise
    /// that cannot be expressed as a literal.  Every caller must treat that
    /// as "this literal stays" — never as "this literal is free".
    fn get_reason(&self, literal: Literal) -> Result<Vec<Literal>, String> {
        let position = *self
            .literal_position
            .get(&literal)
            .ok_or("Literal not in trail")?;

        let (_, level, explanation) = self
            .trail
            .get(position)
            .ok_or("Trail position out of range")?;

        match explanation {
            Explanation::TheoryPropagation { antecedents, .. } => Ok(antecedents.clone()),
            Explanation::EqualityPropagation {
                equalities,
                support,
            } => {
                let mut reason = support.clone();
                reason.extend(self.equality_reason_literals(equalities, "equality propagation")?);
                Ok(reason)
            }
            Explanation::Transitivity { chain } => {
                if chain.is_empty() {
                    return Err(
                        "Transitivity explanation has an empty chain: it proves nothing"
                            .to_string(),
                    );
                }
                self.equality_reason_literals(chain, "transitivity")
            }
            Explanation::Congruence { arg_equalities, .. } => {
                if arg_equalities.is_empty() {
                    return Err(
                        "Congruence explanation has no argument equalities: it proves nothing"
                            .to_string(),
                    );
                }
                self.equality_reason_literals(arg_equalities, "congruence")
            }
            // Input assertion: unconditional at level 0, a decision above it.
            Explanation::Given => {
                if *level == 0 {
                    Ok(Vec::new())
                } else {
                    Err(format!(
                        "Literal on term {} is a decision at level {level}: it has no reason",
                        literal.term
                    ))
                }
            }
        }
    }

    /// The reason literals naming a list of equality premises.
    ///
    /// `kind` names the explanation for the error message.  An equality with
    /// no registered atom fails the whole reason: reporting the premises that
    /// *could* be named would understate the reason and license deleting a
    /// literal that is not implied by them alone.
    ///
    /// The premise "`lhs = rhs` holds" is the positive literal on the
    /// equality's atom, matching the polarity convention of the `support` and
    /// `antecedents` lists it joins: reasons record premises as asserted.
    fn equality_reason_literals(
        &self,
        equalities: &[Equality],
        kind: &str,
    ) -> Result<Vec<Literal>, String> {
        let mut literals = Vec::with_capacity(equalities.len());
        for &equality in equalities {
            let atom = self.equality_atom(equality).ok_or_else(|| {
                format!(
                    "{kind} explanation uses the equality {} = {}, which has no registered atom",
                    equality.lhs, equality.rhs
                )
            })?;
            literals.push(Literal::positive(atom));
        }
        Ok(literals)
    }

    /// Minimize conflict clause.
    fn minimize_conflict(&self, literals: &[Literal]) -> Result<Vec<Literal>, String> {
        match self.config.minimization_algorithm {
            MinimizationAlgorithm::None => Ok(literals.to_vec()),
            MinimizationAlgorithm::Simple => self.minimize_simple(literals),
            MinimizationAlgorithm::Recursive => self.minimize_recursive(literals),
            MinimizationAlgorithm::BinaryResolution => self.minimize_binary_resolution(literals),
        }
    }

    /// Simple minimization (remove obviously redundant literals).
    fn minimize_simple(&self, literals: &[Literal]) -> Result<Vec<Literal>, String> {
        // Remove duplicates and keep only necessary literals
        let mut minimal = Vec::new();
        let mut seen = FxHashSet::default();

        for &lit in literals {
            if !seen.contains(&lit) {
                seen.insert(lit);
                minimal.push(lit);
            }
        }

        Ok(minimal)
    }

    /// Recursive minimization.
    fn minimize_recursive(&self, literals: &[Literal]) -> Result<Vec<Literal>, String> {
        let mut minimal = Vec::new();
        let mut redundant = FxHashSet::default();

        for &lit in literals {
            if self.is_redundant(lit, literals, &mut redundant)? {
                continue;
            }
            minimal.push(lit);
        }

        Ok(minimal)
    }

    /// Check if a literal is redundant.
    ///
    /// A literal is redundant with respect to `clause` when every literal of
    /// its reason is either already in `clause` or redundant in turn.
    ///
    /// The walk runs on an explicit heap stack: its depth is the length of an
    /// implication chain, bounded only by the size of the trail, and dropping
    /// a literal that is *not* redundant weakens a learned clause into an
    /// unsound one, so there is no depth at which giving up quietly would be
    /// acceptable.
    ///
    /// Two corrections to the recursive version, both in the
    /// "keep the literal" (conservative) direction:
    ///
    /// * a literal whose reason cannot be retrieved -- a decision, or one that
    ///   is not on the trail at all -- is no longer treated as having an empty
    ///   reason and therefore as vacuously redundant. `get_reason`'s error was
    ///   discarded by `.ok().unwrap_or_default()`, so such literals were
    ///   silently deleted from the learned clause;
    /// * a cycle among reasons no longer recurses forever. Implication graphs
    ///   are acyclic in a well-formed trail, but the explanations here are
    ///   supplied by theory solvers, so a literal already being examined is
    ///   reported as not redundant instead.
    fn is_redundant(
        &self,
        literal: Literal,
        clause: &[Literal],
        redundant: &mut FxHashSet<Literal>,
    ) -> Result<bool, String> {
        let mut in_progress: FxHashSet<Literal> = FxHashSet::default();

        let mut stack: Vec<RedundancyFrame> = Vec::new();
        match self.enter_redundancy(literal, redundant, &mut in_progress) {
            RedundancyStep::Done(answer) => return Ok(answer),
            RedundancyStep::Descend(frame) => stack.push(frame),
        }

        while let Some(mut frame) = stack.pop() {
            let mut descend: Option<RedundancyFrame> = None;

            while frame.next < frame.reason.len() {
                let reason_lit = frame.reason[frame.next];
                frame.next += 1;

                if clause.contains(&reason_lit) || redundant.contains(&reason_lit) {
                    continue;
                }

                match self.enter_redundancy(reason_lit, redundant, &mut in_progress) {
                    RedundancyStep::Done(true) => continue,
                    RedundancyStep::Done(false) => return Ok(false),
                    RedundancyStep::Descend(child) => {
                        descend = Some(child);
                        break;
                    }
                }
            }

            match descend {
                Some(child) => {
                    stack.push(frame);
                    stack.push(child);
                }
                // Every literal of this reason is covered: the node is
                // redundant.
                None => {
                    redundant.insert(frame.literal);
                }
            }
        }

        Ok(true)
    }

    /// Classify one node of the [`Self::is_redundant`] walk.
    fn enter_redundancy(
        &self,
        literal: Literal,
        redundant: &FxHashSet<Literal>,
        in_progress: &mut FxHashSet<Literal>,
    ) -> RedundancyStep {
        if redundant.contains(&literal) {
            return RedundancyStep::Done(true);
        }
        if !in_progress.insert(literal) {
            // Already on the current path: refuse to claim redundancy.
            return RedundancyStep::Done(false);
        }

        match self.get_reason(literal) {
            Ok(reason) => RedundancyStep::Descend(RedundancyFrame {
                literal,
                reason,
                next: 0,
            }),
            // No reason on the trail: this literal cannot be resolved away.
            Err(_) => RedundancyStep::Done(false),
        }
    }

    /// Binary resolution minimization.
    fn minimize_binary_resolution(&self, literals: &[Literal]) -> Result<Vec<Literal>, String> {
        // Simplified: same as simple for now
        self.minimize_simple(literals)
    }

    /// Compute backtrack level.
    fn compute_backtrack_level(
        &self,
        literals: &[Literal],
        _conflict_level: DecisionLevel,
    ) -> Result<DecisionLevel, String> {
        // Find second-highest decision level in the clause
        let mut levels: Vec<DecisionLevel> = literals
            .iter()
            .filter_map(|&lit| self.get_decision_level(lit))
            .collect();

        levels.sort_unstable();
        levels.dedup();

        if levels.len() >= 2 {
            Ok(levels[levels.len() - 2])
        } else if !levels.is_empty() {
            Ok(levels[0].saturating_sub(1))
        } else {
            Ok(0)
        }
    }

    /// Find UIP literal in clause.
    fn find_uip_literal(&self, literals: &[Literal]) -> Option<Literal> {
        // Find literal at highest decision level
        literals
            .iter()
            .max_by_key(|&&lit| self.get_decision_level(lit).unwrap_or(0))
            .copied()
    }

    /// Get learned clauses.
    pub fn learned_clauses(&self) -> &[ConflictClause] {
        &self.learned_clauses
    }

    /// Get theory blame statistics.
    pub fn theory_blame(&self) -> &FxHashMap<TheoryId, u64> {
        &self.theory_blame
    }

    /// Clear all state.
    pub fn clear(&mut self) {
        self.trail.clear();
        self.literal_position.clear();
        self.level_boundaries.clear();
        self.current_level = 0;
        self.learned_clauses.clear();
        self.theory_blame.clear();
        self.equality_atoms.clear();
    }

    /// Reset statistics.
    pub fn reset_stats(&mut self) {
        self.stats = ConflictResolutionStats::default();
    }
}

impl Default for ConflictResolver {
    fn default() -> Self {
        Self::new()
    }
}

/// Explanation generator for theory conflicts.
pub struct ExplanationGenerator {
    /// Explanation cache.
    cache: FxHashMap<Literal, Explanation>,
}

impl ExplanationGenerator {
    /// Create new explanation generator.
    pub fn new() -> Self {
        Self {
            cache: FxHashMap::default(),
        }
    }

    /// Add explanation for a literal.
    pub fn add_explanation(&mut self, literal: Literal, explanation: Explanation) {
        self.cache.insert(literal, explanation);
    }

    /// Get explanation for a literal.
    pub fn get_explanation(&self, literal: Literal) -> Option<&Explanation> {
        self.cache.get(&literal)
    }

    /// Build explanation chain.
    pub fn build_chain(&self, literals: &[Literal]) -> Explanation {
        let mut antecedents = Vec::new();

        for &lit in literals {
            if let Some(explanation) = self.cache.get(&lit)
                && let Explanation::TheoryPropagation {
                    antecedents: ants, ..
                } = explanation
            {
                antecedents.extend_from_slice(ants);
            }
        }

        Explanation::TheoryPropagation {
            theory: 0,
            antecedents,
        }
    }

    /// Clear cache.
    pub fn clear(&mut self) {
        self.cache.clear();
    }
}

impl Default for ExplanationGenerator {
    fn default() -> Self {
        Self::new()
    }
}

/// Multi-theory conflict analyzer.
pub struct MultiTheoryConflictAnalyzer {
    /// Individual theory resolvers.
    resolvers: FxHashMap<TheoryId, ConflictResolver>,

    /// Combined conflict statistics.
    combined_stats: ConflictResolutionStats,
}

impl MultiTheoryConflictAnalyzer {
    /// Create new multi-theory analyzer.
    pub fn new() -> Self {
        Self {
            resolvers: FxHashMap::default(),
            combined_stats: ConflictResolutionStats::default(),
        }
    }

    /// Register theory.
    pub fn register_theory(&mut self, theory: TheoryId, config: ConflictResolutionConfig) {
        self.resolvers
            .insert(theory, ConflictResolver::with_config(config));
    }

    /// Analyze conflict from a theory.
    pub fn analyze(&mut self, conflict: TheoryConflict) -> Result<ConflictAnalysis, String> {
        let resolver = self
            .resolvers
            .get_mut(&conflict.theory)
            .ok_or("Theory not registered")?;

        let analysis = resolver.analyze_conflict(conflict)?;

        // Update combined stats
        self.combined_stats.conflicts_analyzed += 1;

        Ok(analysis)
    }

    /// Get combined statistics.
    pub fn combined_stats(&self) -> &ConflictResolutionStats {
        &self.combined_stats
    }

    /// Get resolver for a theory.
    pub fn get_resolver(&self, theory: TheoryId) -> Option<&ConflictResolver> {
        self.resolvers.get(&theory)
    }

    /// Clear all resolvers.
    pub fn clear(&mut self) {
        for resolver in self.resolvers.values_mut() {
            resolver.clear();
        }
        self.combined_stats = ConflictResolutionStats::default();
    }
}

impl Default for MultiTheoryConflictAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_literal_creation() {
        let lit = Literal::positive(1);
        assert_eq!(lit.term, 1);
        assert!(lit.polarity);
    }

    #[test]
    fn test_literal_negation() {
        let lit = Literal::positive(1);
        let neg = lit.negate();
        assert!(!neg.polarity);
    }

    #[test]
    fn test_resolver_creation() {
        let resolver = ConflictResolver::new();
        assert_eq!(resolver.stats().conflicts_analyzed, 0);
    }

    #[test]
    fn test_add_assignment() {
        let mut resolver = ConflictResolver::new();
        let lit = Literal::positive(1);

        resolver.add_assignment(lit, 0, Explanation::Given);
        assert_eq!(resolver.trail.len(), 1);
    }

    #[test]
    fn test_decision_level() {
        let mut resolver = ConflictResolver::new();

        resolver.push_decision_level();
        assert_eq!(resolver.current_level, 1);
    }

    #[test]
    fn test_backtrack() {
        let mut resolver = ConflictResolver::new();

        resolver.push_decision_level();
        resolver.add_assignment(Literal::positive(1), 1, Explanation::Given);

        resolver.backtrack(0).expect("Backtrack failed");
        assert_eq!(resolver.trail.len(), 0);
    }

    #[test]
    fn test_conflict_analysis() {
        let mut resolver = ConflictResolver::new();

        let conflict = TheoryConflict {
            theory: 0,
            literals: vec![Literal::positive(1), Literal::negative(2)],
            explanation: Explanation::Given,
            level: 0,
        };

        let analysis = resolver.analyze_conflict(conflict);
        assert!(analysis.is_ok());
    }

    #[test]
    fn test_explanation_generator() {
        let mut generator = ExplanationGenerator::new();
        let lit = Literal::positive(1);

        generator.add_explanation(lit, Explanation::Given);
        assert!(generator.get_explanation(lit).is_some());
    }

    #[test]
    fn test_multi_theory_analyzer() {
        let mut analyzer = MultiTheoryConflictAnalyzer::new();
        analyzer.register_theory(0, ConflictResolutionConfig::default());

        let conflict = TheoryConflict {
            theory: 0,
            literals: vec![Literal::positive(1)],
            explanation: Explanation::Given,
            level: 0,
        };

        let result = analyzer.analyze(conflict);
        assert!(result.is_ok());
    }

    #[test]
    fn test_simple_minimization() {
        let resolver = ConflictResolver::new();

        let literals = vec![
            Literal::positive(1),
            Literal::positive(2),
            Literal::positive(1), // Duplicate
        ];

        let minimized = resolver
            .minimize_simple(&literals)
            .expect("Minimization failed");
        assert_eq!(minimized.len(), 2);
    }

    #[test]
    fn test_backtrack_level_computation() {
        let mut resolver = ConflictResolver::new();

        resolver.add_assignment(Literal::positive(1), 0, Explanation::Given);
        resolver.push_decision_level();
        resolver.add_assignment(Literal::positive(2), 1, Explanation::Given);
        resolver.push_decision_level();
        resolver.add_assignment(Literal::positive(3), 2, Explanation::Given);

        let literals = vec![
            Literal::positive(1),
            Literal::positive(2),
            Literal::positive(3),
        ];

        let level = resolver.compute_backtrack_level(&literals, 2);
        assert!(level.is_ok());
    }

    /// A reason chain as long as the trail used to be walked recursively.
    /// Returning at all is the assertion.
    #[test]
    fn is_redundant_survives_a_long_reason_chain_on_a_small_stack() {
        // Stack and chain length scale together (1 MiB/100k -> 128 KiB/12.5k):
        // the ~10 B-per-frame threshold is the pin, so never raise one alone.
        let handle = std::thread::Builder::new()
            .stack_size(1 << 17)
            .spawn(|| {
                let mut resolver = ConflictResolver::new();
                const CHAIN: TermId = 12_500;

                for term in 0..CHAIN {
                    resolver.add_assignment(
                        Literal::positive(term),
                        0,
                        Explanation::TheoryPropagation {
                            theory: 0,
                            antecedents: vec![Literal::positive(term + 1)],
                        },
                    );
                }
                // The end of the chain has an explanation with no antecedents.
                resolver.add_assignment(Literal::positive(CHAIN), 0, Explanation::Given);

                let mut redundant = FxHashSet::default();
                resolver.is_redundant(Literal::positive(0), &[], &mut redundant)
            })
            .expect("spawning the worker thread should succeed");

        let verdict = handle
            .join()
            .expect("the walk must not overflow")
            .expect("the walk must not error");
        assert!(verdict);
    }

    /// A literal that is not on the trail has no reason, so it cannot be
    /// resolved away. It used to be reported redundant -- and therefore
    /// deleted from the learned clause -- because `get_reason`'s error was
    /// turned into an empty reason.
    #[test]
    fn is_redundant_keeps_a_literal_with_no_reason() {
        let resolver = ConflictResolver::new();
        let mut redundant = FxHashSet::default();

        let verdict = resolver
            .is_redundant(Literal::positive(7), &[], &mut redundant)
            .expect("querying an unknown literal is not an error");
        assert!(!verdict, "a literal absent from the trail is not redundant");
        assert!(redundant.is_empty());
    }

    /// Mutually justifying literals used to recurse until the stack ran out.
    #[test]
    fn is_redundant_terminates_on_a_reason_cycle() {
        let mut resolver = ConflictResolver::new();
        resolver.add_assignment(
            Literal::positive(1),
            0,
            Explanation::TheoryPropagation {
                theory: 0,
                antecedents: vec![Literal::positive(2)],
            },
        );
        resolver.add_assignment(
            Literal::positive(2),
            0,
            Explanation::TheoryPropagation {
                theory: 0,
                antecedents: vec![Literal::positive(1)],
            },
        );

        let mut redundant = FxHashSet::default();
        let verdict = resolver
            .is_redundant(Literal::positive(1), &[], &mut redundant)
            .expect("a cycle is not an error");
        assert!(!verdict, "a literal on a reason cycle is not redundant");
    }

    /// Semantic pin: a literal whose reason is entirely inside the clause is
    /// redundant, and gets recorded for later queries.
    #[test]
    fn is_redundant_accepts_a_reason_covered_by_the_clause() {
        let mut resolver = ConflictResolver::new();
        resolver.add_assignment(
            Literal::positive(1),
            0,
            Explanation::TheoryPropagation {
                theory: 0,
                antecedents: vec![Literal::positive(2), Literal::positive(3)],
            },
        );

        let clause = [Literal::positive(2), Literal::positive(3)];
        let mut redundant = FxHashSet::default();
        assert!(
            resolver
                .is_redundant(Literal::positive(1), &clause, &mut redundant)
                .expect("covered reason is not an error")
        );
        assert!(redundant.contains(&Literal::positive(1)));
    }

    // ===== get_reason: one pin per explanation kind =====================
    //
    // Every kind used to fall through to `Ok(Vec::new())` unless it was a
    // theory or equality propagation. An empty reason means "entailed
    // unconditionally", which licenses deleting the literal from a learned
    // clause -- so the fallthrough silently produced clauses the constraint
    // set does not imply.

    /// A theory propagation's reason is its antecedents, verbatim.
    #[test]
    fn get_reason_theory_propagation_returns_its_antecedents() {
        let mut resolver = ConflictResolver::new();
        resolver.add_assignment(
            Literal::positive(1),
            0,
            Explanation::TheoryPropagation {
                theory: 3,
                antecedents: vec![Literal::positive(2), Literal::negative(3)],
            },
        );

        let reason = resolver
            .get_reason(Literal::positive(1))
            .expect("a theory propagation has a reason");
        assert_eq!(reason, vec![Literal::positive(2), Literal::negative(3)]);
    }

    /// An equality propagation's reason is its support *and* its equalities;
    /// the equalities used to be discarded.
    #[test]
    fn get_reason_equality_propagation_includes_its_equalities() {
        let mut resolver = ConflictResolver::new();
        let equality = Equality::new(10, 11);
        resolver.register_equality_atom(equality, 42);
        resolver.add_assignment(
            Literal::positive(1),
            0,
            Explanation::EqualityPropagation {
                equalities: vec![equality],
                support: vec![Literal::negative(5)],
            },
        );

        let reason = resolver
            .get_reason(Literal::positive(1))
            .expect("an equality propagation has a reason");
        assert_eq!(reason, vec![Literal::negative(5), Literal::positive(42)]);
    }

    /// A transitivity explanation's reason is its chain links.
    #[test]
    fn get_reason_transitivity_returns_its_chain() {
        let mut resolver = ConflictResolver::new();
        let first = Equality::new(1, 2);
        let second = Equality::new(2, 3);
        resolver.register_equality_atom(first, 100);
        resolver.register_equality_atom(second, 101);
        resolver.add_assignment(
            Literal::positive(7),
            0,
            Explanation::Transitivity {
                chain: vec![first, second],
            },
        );

        let reason = resolver
            .get_reason(Literal::positive(7))
            .expect("a transitivity chain is a reason");
        assert_eq!(reason, vec![Literal::positive(100), Literal::positive(101)]);
    }

    /// A congruence explanation's reason is its argument equalities (the
    /// head `function` is what it concludes about, not a premise).
    #[test]
    fn get_reason_congruence_returns_its_argument_equalities() {
        let mut resolver = ConflictResolver::new();
        let arg = Equality::new(4, 5);
        resolver.register_equality_atom(arg, 200);
        resolver.add_assignment(
            Literal::positive(8),
            0,
            Explanation::Congruence {
                function: 99,
                arg_equalities: vec![arg],
            },
        );

        let reason = resolver
            .get_reason(Literal::positive(8))
            .expect("an argument equality is a reason");
        assert_eq!(reason, vec![Literal::positive(200)]);
    }

    /// An equality with no registered atom cannot be named in a clause; the
    /// whole reason fails rather than reporting the premises that can be
    /// named (which would understate it).
    #[test]
    fn get_reason_rejects_an_equality_with_no_registered_atom() {
        let mut resolver = ConflictResolver::new();
        let known = Equality::new(1, 2);
        resolver.register_equality_atom(known, 100);
        resolver.add_assignment(
            Literal::positive(7),
            0,
            Explanation::Transitivity {
                chain: vec![known, Equality::new(2, 3)],
            },
        );

        assert!(resolver.get_reason(Literal::positive(7)).is_err());
    }

    /// Degenerate equality explanations prove nothing, and must not be read
    /// as "no premises needed".
    #[test]
    fn get_reason_rejects_degenerate_equality_explanations() {
        let mut resolver = ConflictResolver::new();
        resolver.add_assignment(
            Literal::positive(1),
            0,
            Explanation::Transitivity { chain: Vec::new() },
        );
        resolver.add_assignment(
            Literal::positive(2),
            0,
            Explanation::Congruence {
                function: 9,
                arg_equalities: Vec::new(),
            },
        );

        assert!(resolver.get_reason(Literal::positive(1)).is_err());
        assert!(resolver.get_reason(Literal::positive(2)).is_err());
    }

    /// A level-0 `Given` is an input assertion: unconditionally entailed, so
    /// an empty premise set is the correct answer -- the one place this
    /// function may return one.
    #[test]
    fn get_reason_given_at_level_zero_has_no_premises() {
        let mut resolver = ConflictResolver::new();
        resolver.add_assignment(Literal::positive(1), 0, Explanation::Given);

        let reason = resolver
            .get_reason(Literal::positive(1))
            .expect("a level-0 input assertion is unconditional");
        assert!(reason.is_empty());
    }

    /// The same explanation above level 0 marks a *decision*: it has no
    /// premises to resolve on and must not be deleted from a clause.
    #[test]
    fn get_reason_given_above_level_zero_is_a_decision_error() {
        let mut resolver = ConflictResolver::new();
        resolver.push_decision_level();
        resolver.add_assignment(Literal::positive(1), 1, Explanation::Given);

        assert!(resolver.get_reason(Literal::positive(1)).is_err());
    }

    /// Soundness end to end: a conflict between two decisions used to
    /// resolve both away and learn the *empty* clause -- an unconditional
    /// claim of unsatisfiability. Both decisions must survive.
    #[test]
    fn analyze_conflict_never_resolves_a_decision_away() {
        let mut resolver = ConflictResolver::new();
        resolver.push_decision_level();
        resolver.add_assignment(Literal::positive(1), 1, Explanation::Given);
        resolver.add_assignment(Literal::positive(2), 1, Explanation::Given);

        let analysis = resolver
            .analyze_conflict(TheoryConflict {
                theory: 0,
                literals: vec![Literal::positive(1), Literal::positive(2)],
                explanation: Explanation::Given,
                level: 1,
            })
            .expect("analysis succeeds");

        let learned: FxHashSet<Literal> = analysis.clause.literals.iter().copied().collect();
        assert!(
            learned.contains(&Literal::positive(1)) && learned.contains(&Literal::positive(2)),
            "decisions have no reason and cannot be resolved away: {:?}",
            analysis.clause.literals
        );
    }

    /// A literal justified by a decision is not redundant either.
    #[test]
    fn is_redundant_keeps_a_literal_justified_by_a_decision() {
        let mut resolver = ConflictResolver::new();
        resolver.push_decision_level();
        resolver.add_assignment(Literal::positive(1), 1, Explanation::Given);
        resolver.add_assignment(
            Literal::positive(2),
            1,
            Explanation::TheoryPropagation {
                theory: 0,
                antecedents: vec![Literal::positive(1)],
            },
        );

        let mut redundant = FxHashSet::default();
        let verdict = resolver
            .is_redundant(Literal::positive(2), &[], &mut redundant)
            .expect("a decision-backed reason is not an error");
        assert!(!verdict);
    }

    /// The equality-atom table is a naming table, not trail state: it must
    /// survive backtracking, or a reason that was expressible before a
    /// backjump would become an error after it.
    #[test]
    fn equality_atoms_survive_backtracking() {
        let mut resolver = ConflictResolver::new();
        let equality = Equality::new(1, 2);
        resolver.register_equality_atom(equality, 55);
        resolver.push_decision_level();
        resolver.add_assignment(Literal::positive(9), 1, Explanation::Given);

        resolver.backtrack(0).expect("backtrack to level 0");
        assert_eq!(resolver.equality_atom(equality), Some(55));

        resolver.clear();
        assert_eq!(resolver.equality_atom(equality), None);
    }
}
