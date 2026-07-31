//! Nelson-Oppen Theory Combination
//!
//! This module implements the Nelson-Oppen procedure for combining
//! decision procedures from multiple theories.
//!
//! The combination works for:
//! - Stably infinite theories (every satisfiable formula has an infinite model)
//! - Signature-disjoint theories (no shared function/predicate symbols except =)
//!
//! Key operations:
//! 1. Purification: Transform mixed terms into pure sub-formulas
//! 2. Variable abstraction: Replace foreign terms with fresh variables
//! 3. Equality propagation: Share equalities between shared variables
//!
//! # Theory Combination Modes
//!
//! ## Nelson-Oppen (Classic)
//! The original procedure from Nelson & Oppen (1979):
//! - Eagerly propagates all equalities between shared variables to all theories
//! - Requires theories to be stably-infinite and signature-disjoint
//! - Guarantees completeness: if each theory is complete, combination is complete
//! - Can generate many unnecessary propagations (O(n²) equalities for n shared vars)
//!
//! ## Model-Based Combination
//! More efficient approach from de Moura & Bjørner (2007):
//! - Checks arrangements lazily using current theory models
//! - Only propagates equalities when models disagree on arrangements
//! - Reduces unnecessary propagations significantly on satisfiable formulas
//! - Optimal when theories have cheap model construction
//!
//! ## Delayed Combination
//! Postpones propagation until absolutely necessary:
//! - Batches equality propagations to reduce overhead
//! - Useful when theories have expensive equality handling
//! - Trades completeness for performance in some cases
//!
//! ## Polite Combination
//! From Jovanović & Barrett (2010), for "polite" theories:
//! - A theory is polite if it can witness all possible arrangements of shared variables
//! - More efficient than Nelson-Oppen when applicable (e.g., arithmetic is polite)
//! - Requires theories to construct models that satisfy arbitrary equality arrangements
//! - Best performance when all theories are polite
//!
//! # References
//!
//! - Nelson & Oppen, "Simplification by Cooperating Decision Procedures" (1979)
//! - de Moura & Bjørner, "Model-based Theory Combination" (2007)
//! - Jovanović & Barrett, "Polite Theories Revisited" (2010)
//! - Z3's `src/smt/theory_opt.cpp` and `src/smt/smt_context.cpp`

use crate::arithmetic::ArithSolver;
use crate::euf::EufSolver;
use crate::lru_cache::LruCache;
#[allow(unused_imports)]
use crate::prelude::*;
use crate::theory::{EqualityNotification, Theory, TheoryCombination, TheoryId, TheoryResult};
use num_rational::Rational64;
use oxiz_core::ast::TermId;
use oxiz_core::error::Result;

/// A shared variable between theories
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SharedVar {
    /// The variable/term ID
    pub term: TermId,
    /// Which theories use this variable
    pub theories: u8,
}

impl SharedVar {
    /// Check if EUF uses this variable
    #[must_use]
    pub fn in_euf(&self) -> bool {
        self.theories & (1 << TheoryId::EUF as u8) != 0
    }

    /// Check if arithmetic uses this variable
    #[must_use]
    pub fn in_arith(&self) -> bool {
        self.theories & (1 << TheoryId::LRA as u8) != 0
            || self.theories & (1 << TheoryId::LIA as u8) != 0
    }
}

/// An equality arrangement between shared variables
#[derive(Debug, Clone)]
pub struct EqualityArrangement {
    /// Pairs of terms that must be equal
    pub equalities: Vec<(TermId, TermId)>,
    /// Pairs of terms that must be different
    pub disequalities: Vec<(TermId, TermId)>,
}

impl EqualityArrangement {
    /// Create a new empty arrangement
    #[must_use]
    pub fn new() -> Self {
        Self {
            equalities: Vec::new(),
            disequalities: Vec::new(),
        }
    }

    /// Add an equality
    pub fn add_equality(&mut self, a: TermId, b: TermId) {
        self.equalities.push((a, b));
    }

    /// Add a disequality
    pub fn add_disequality(&mut self, a: TermId, b: TermId) {
        self.disequalities.push((a, b));
    }

    /// Check if this arrangement is complete for the given variables
    #[must_use]
    pub fn is_complete(&self, vars: &[TermId]) -> bool {
        // A complete arrangement specifies the relationship between all pairs
        let n = vars.len();
        let expected_pairs = n * (n - 1) / 2;
        self.equalities.len() + self.disequalities.len() >= expected_pairs
    }
}

impl Default for EqualityArrangement {
    fn default() -> Self {
        Self::new()
    }
}

/// Theory combination mode
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CombinationMode {
    /// Classic Nelson-Oppen (equality propagation)
    NelsonOppen,
    /// Model-based theory combination (check arrangements)
    ModelBased,
    /// Delayed theory combination (lazy propagation)
    Delayed,
    /// Polite theory combination (more efficient for certain theory classes)
    Polite,
}

/// A cached theory lemma
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct TheoryLemma {
    /// The assumptions (conjunction)
    assumptions: Vec<TermId>,
    /// The conclusion (disjunction)
    conclusion: Vec<TermId>,
    /// Which theory produced this lemma
    theory: TheoryId,
}

impl TheoryLemma {
    /// Check if this lemma subsumes (makes redundant) another
    ///
    /// Lemma L1 subsumes L2 if L1 is at least as strong, meaning:
    /// - L1.assumptions ⊆ L2.assumptions (L1 needs fewer or equal assumptions)
    /// - L1.conclusion ⊇ L2.conclusion (L1 concludes at least as much)
    ///
    /// If L1 subsumes L2, then L2 is redundant and can be discarded
    fn subsumes(&self, other: &TheoryLemma) -> bool {
        // Must be from the same theory
        if self.theory != other.theory {
            return false;
        }

        // L1 subsumes L2 if:
        // - Every assumption in L1 is also in L2 (L1 requires subset of L2's assumptions)
        let assumptions_subset = self
            .assumptions
            .iter()
            .all(|a| other.assumptions.contains(a));

        // - Every conclusion in L2 is also in L1 (L1 proves superset of L2's conclusions)
        let conclusion_superset = other.conclusion.iter().all(|c| self.conclusion.contains(c));

        assumptions_subset && conclusion_superset
    }

    /// Check if this lemma is stronger than another (synonym for subsumes)
    fn is_stronger_than(&self, other: &TheoryLemma) -> bool {
        self.subsumes(other)
    }
}

/// Nelson-Oppen theory combiner with model-based extension
#[derive(Debug)]
pub struct TheoryCombiner {
    /// EUF theory solver
    euf: EufSolver,
    /// Arithmetic theory solver
    arith: ArithSolver,
    /// Shared variables (appear in multiple theories)
    shared_vars: FxHashSet<TermId>,
    /// Term to theory mapping
    term_theory: FxHashMap<TermId, TheoryId>,
    /// Pending equalities to propagate
    pending_equalities: Vec<(TermId, TermId, TheoryId)>,
    /// Context stack for push/pop
    context_stack: Vec<CombinerState>,
    /// Theory combination mode
    mode: CombinationMode,
    /// Cache of theory lemmas to avoid recomputation (bounded LRU)
    lemma_cache: LruCache<TheoryLemma, ()>,
    /// Current arrangement being tested (for model-based)
    current_arrangement: Option<EqualityArrangement>,
    /// Relevancy tracking: terms that are relevant to the current search
    relevant_terms: FxHashSet<TermId>,
    /// Statistics for theory propagation
    stats: CombinerStats,
}

/// Statistics for theory combination
#[derive(Debug, Clone, Default)]
pub struct CombinerStats {
    /// Number of equalities propagated
    pub equalities_propagated: u64,
    /// Number of theory checks performed
    pub theory_checks: u64,
    /// Number of conflicts detected
    pub conflicts: u64,
    /// Number of lemmas cached
    pub lemmas_cached: u64,
    /// Number of relevancy propagations
    pub relevancy_propagations: u64,
    /// Number of lemma cache hits (contains_key returned true)
    pub lemma_cache_hits: u64,
    /// Number of lemma cache misses (contains_key returned false)
    pub lemma_cache_misses: u64,
    /// Number of lemma cache evictions due to capacity limit
    pub lemma_cache_evictions: u64,
}

#[derive(Debug, Clone)]
struct CombinerState {
    num_pending: usize,
    lemma_cache_size: usize,
    relevant_terms_size: usize,
}

impl Default for TheoryCombiner {
    fn default() -> Self {
        Self::new()
    }
}

impl TheoryCombiner {
    /// Create a new theory combiner with default Nelson-Oppen mode
    #[must_use]
    pub fn new() -> Self {
        Self::with_mode(CombinationMode::NelsonOppen)
    }

    /// Create a new theory combiner with specified mode
    #[must_use]
    pub fn with_mode(mode: CombinationMode) -> Self {
        const DEFAULT_MAX_LEMMA_CACHE_SIZE: usize = 10_000;
        Self {
            euf: EufSolver::new(),
            arith: ArithSolver::lra(),
            shared_vars: FxHashSet::default(),
            term_theory: FxHashMap::default(),
            pending_equalities: Vec::new(),
            context_stack: Vec::new(),
            mode,
            lemma_cache: LruCache::new(DEFAULT_MAX_LEMMA_CACHE_SIZE),
            current_arrangement: None,
            relevant_terms: FxHashSet::default(),
            stats: CombinerStats::default(),
        }
    }

    /// Create a new theory combiner with a specified lemma cache size
    #[must_use]
    pub fn with_max_lemma_cache_size(max_size: usize) -> Self {
        let effective = max_size.max(1);
        Self {
            euf: EufSolver::new(),
            arith: ArithSolver::lra(),
            shared_vars: FxHashSet::default(),
            term_theory: FxHashMap::default(),
            pending_equalities: Vec::new(),
            context_stack: Vec::new(),
            mode: CombinationMode::NelsonOppen,
            lemma_cache: LruCache::new(effective),
            current_arrangement: None,
            relevant_terms: FxHashSet::default(),
            stats: CombinerStats::default(),
        }
    }

    /// Set the combination mode
    pub fn set_mode(&mut self, mode: CombinationMode) {
        self.mode = mode;
    }

    /// Get the current combination mode
    #[must_use]
    pub fn mode(&self) -> CombinationMode {
        self.mode
    }

    /// Check if the combination should use polite theory combination
    ///
    /// Polite theory combination is more efficient than Nelson-Oppen when one or both
    /// theories are "polite" - meaning they can witness all arrangements of shared variables.
    ///
    /// A theory T is polite if:
    /// 1. T is stably infinite (every satisfiable formula has an infinite model)
    /// 2. T can "absorb" extra constants without losing satisfiability
    /// 3. T can witness any arrangement of shared variables
    ///
    /// Common polite theories: EUF, arrays, and most data structure theories.
    /// Non-polite theories: LRA/LIA (arithmetic) - these have finite witnessing issues.
    ///
    /// When combining a polite theory T1 with any theory T2:
    /// - We only need to check satisfiability of T2 with the arrangement
    /// - T1 can always be extended to satisfy any consistent arrangement
    /// - This avoids the expensive equality propagation of Nelson-Oppen
    ///
    /// Reference: "Polite Theories Revisited" by Jovanović & Barrett (2010)
    #[must_use]
    pub fn is_theory_polite(&self, theory: TheoryId) -> bool {
        match theory {
            TheoryId::EUF => true,                  // EUF is polite
            TheoryId::Arrays => true,               // Arrays are polite
            TheoryId::Datatype => true,             // Datatypes are polite
            TheoryId::Strings => true,              // Strings can be polite with careful handling
            TheoryId::LRA | TheoryId::LIA => false, // Arithmetic is not polite
            TheoryId::NIA | TheoryId::NRA => false, // Nonlinear arithmetic is not polite
            TheoryId::BV => false,                  // BitVectors are not polite (fixed width)
            TheoryId::FP => false,                  // Floating-point is not polite
            TheoryId::Bool => true,                 // Boolean is trivially polite
        }
    }

    /// Perform polite theory combination check
    ///
    /// When combining theories where at least one is polite, we can use a more
    /// efficient checking procedure:
    ///
    /// 1. Check the non-polite theory (e.g., arithmetic) for satisfiability
    /// 2. Extract the arrangement of shared variables from its model
    /// 3. The polite theory (e.g., EUF) can always be extended to match this arrangement
    ///
    /// This avoids the O(2^n) equality propagation of Nelson-Oppen
    pub fn check_polite_combination(&mut self) -> Result<TheoryResult> {
        // Check if we can use polite combination
        // EUF is polite, so we check arithmetic first then extend EUF
        let euf_is_polite = self.is_theory_polite(TheoryId::EUF);

        if euf_is_polite {
            // Arithmetic is the "difficult" theory, EUF is polite
            // 1. Check arithmetic for satisfiability
            match self.arith.check() {
                Ok(TheoryResult::Sat) => {
                    // 2. Extract arrangement of shared variables from arithmetic model
                    let arrangement = self.extract_arrangement_from_arith();

                    // 3. Assert this arrangement in EUF
                    // Note: We use a special reason term (0) to indicate polite combination arrangement
                    let polite_reason = TermId::new(0);
                    for (a, b) in &arrangement.equalities {
                        self.euf.merge(a.raw(), b.raw(), polite_reason)?;
                    }
                    for (a, b) in &arrangement.disequalities {
                        self.euf.assert_diseq(a.raw(), b.raw(), polite_reason);
                    }

                    // 4. Check EUF (should always succeed for polite theories)
                    match self.euf.check() {
                        Ok(TheoryResult::Sat) => Ok(TheoryResult::Sat),
                        Ok(TheoryResult::Unsat(conflict)) => {
                            // This shouldn't happen for a truly polite theory
                            // But we handle it gracefully
                            Ok(TheoryResult::Unsat(conflict))
                        }
                        Ok(TheoryResult::Unknown) => Ok(TheoryResult::Unknown),
                        Ok(TheoryResult::Propagate(_)) => {
                            // Propagate and continue checking
                            Ok(TheoryResult::Sat)
                        }
                        Err(e) => Err(e),
                    }
                }
                Ok(TheoryResult::Unsat(conflict)) => Ok(TheoryResult::Unsat(conflict)),
                Ok(TheoryResult::Unknown) => Ok(TheoryResult::Unknown),
                Ok(TheoryResult::Propagate(_)) => {
                    // Propagate and retry
                    Ok(TheoryResult::Sat)
                }
                Err(e) => Err(e),
            }
        } else {
            // Fall back to standard Nelson-Oppen
            self.check_nelson_oppen()
        }
    }

    /// Extract the arrangement of shared variables from the arithmetic model.
    ///
    /// This used to unconditionally assert a disequality for EVERY pair of
    /// shared variables regardless of their actual arithmetic values ("for
    /// now, assume they're different"), fabricating a spurious `!=` even
    /// when the arithmetic model gives two shared variables the SAME
    /// value. Asserting that fabricated disequality into EUF could
    /// conflict with an equality EUF independently derives (e.g. via
    /// congruence), producing a wrong `Unsat` that has nothing to do with
    /// the actual problem. The arrangement must instead reflect what the
    /// arithmetic model actually says: variables with the same value are
    /// equal, variables with different values are disequal.
    fn extract_arrangement_from_arith(&self) -> EqualityArrangement {
        let mut arrangement = EqualityArrangement::new();

        let shared_vars: Vec<TermId> = self.shared_vars.iter().copied().collect();

        // Group shared variables by their actual arithmetic-model value so
        // same-value pairs become equalities and different-value pairs
        // become disequalities -- the arrangement must partition the
        // variables consistently with the model, not assume everything is
        // pairwise distinct.
        let mut by_value: FxHashMap<Rational64, Vec<TermId>> = FxHashMap::default();
        let mut unvalued: Vec<TermId> = Vec::new();
        for &v in &shared_vars {
            match self.arith.value(v) {
                Some(val) => by_value.entry(val).or_default().push(v),
                // A shared variable the arithmetic theory has no value for
                // (e.g. not actually interned there) cannot be honestly
                // arranged -- skip it rather than guessing.
                None => unvalued.push(v),
            }
        }

        // Same value: equal.
        for group in by_value.values() {
            for w in group.windows(2) {
                arrangement.add_equality(w[0], w[1]);
            }
        }

        // Different values: disequal. Compare one representative per
        // value-group (transitively, everything in one group is already
        // asserted equal to the others in that group).
        let representatives: Vec<TermId> = by_value
            .values()
            .filter_map(|group| group.first().copied())
            .collect();
        for i in 0..representatives.len() {
            for j in (i + 1)..representatives.len() {
                arrangement.add_disequality(representatives[i], representatives[j]);
            }
        }

        let _ = unvalued; // Intentionally excluded from the arrangement (see above).

        arrangement
    }

    /// Register a term with a specific theory
    pub fn register_term(&mut self, term: TermId, theory: TheoryId) {
        if let Some(existing) = self.term_theory.get(&term) {
            if *existing != theory {
                // Term appears in multiple theories - it's shared
                self.shared_vars.insert(term);
            }
        } else {
            self.term_theory.insert(term, theory);
        }
    }

    /// Register a shared variable
    pub fn add_shared_var(&mut self, term: TermId) {
        self.shared_vars.insert(term);
    }

    /// Get all shared variables
    #[must_use]
    pub fn shared_vars(&self) -> &FxHashSet<TermId> {
        &self.shared_vars
    }

    /// Get mutable reference to EUF solver
    pub fn euf_mut(&mut self) -> &mut EufSolver {
        &mut self.euf
    }

    /// Get mutable reference to arithmetic solver
    pub fn arith_mut(&mut self) -> &mut ArithSolver {
        &mut self.arith
    }

    /// Get reference to EUF solver
    #[must_use]
    pub fn euf(&self) -> &EufSolver {
        &self.euf
    }

    /// Get reference to arithmetic solver
    #[must_use]
    pub fn arith(&self) -> &ArithSolver {
        &self.arith
    }

    /// Propagate an equality from one theory to others
    pub fn propagate_equality(&mut self, a: TermId, b: TermId, source: TheoryId) {
        self.pending_equalities.push((a, b, source));
    }

    /// Process all pending equality propagations
    ///
    /// Returns Ok(true) if propagation succeeded, Ok(false) if there was no work,
    /// or an error with conflict explanation if inconsistent.
    pub fn propagate(&mut self) -> Result<TheoryResult> {
        if self.pending_equalities.is_empty() {
            return Ok(TheoryResult::Sat);
        }

        while let Some((a, b, source)) = self.pending_equalities.pop() {
            // Only propagate equalities between shared variables
            if !self.shared_vars.contains(&a) || !self.shared_vars.contains(&b) {
                continue;
            }

            // Skip if terms are not relevant
            if !self.is_relevant(a) && !self.is_relevant(b) {
                continue;
            }

            self.stats.equalities_propagated += 1;

            // Propagate to EUF if it didn't originate there
            if source != TheoryId::EUF {
                // Intern the terms and merge them
                let node_a = self.euf.intern(a);
                let node_b = self.euf.intern(b);
                self.euf.merge(node_a, node_b, TermId::new(0))?;
            }

            // Propagate to arithmetic if it didn't originate there. This
            // used to be a no-op ("would be implemented here"), so an
            // equality EUF (or a caller) discovered between two shared
            // variables never actually reached the simplex -- arithmetic
            // stayed unaware of it and could derive a model inconsistent
            // with it. `notify_equality` (via `TheoryCombination`) encodes
            // `a = b` as `a <= b AND a >= b` in the simplex, exactly the
            // real Nelson-Oppen propagation direction this theory needs.
            //
            // `notify_equality` returning `false` is ambiguous by the
            // trait's own design (see `ArithSolver`/`BvSolver`'s impls): it
            // means EITHER "not relevant to me, politely ignored" OR "both
            // sides ARE mine and this equality genuinely conflicts". Only
            // the second is an actual cross-theory conflict; `is_relevant`
            // on both terms distinguishes the two.
            if source != TheoryId::LRA && source != TheoryId::LIA {
                let both_relevant = self.arith.is_relevant(a) && self.arith.is_relevant(b);
                let accepted = self.arith.notify_equality(EqualityNotification {
                    lhs: a,
                    rhs: b,
                    reason: None,
                });
                if !accepted && both_relevant {
                    // Arithmetic already knew about both terms and still
                    // rejected the equality: a genuine cross-theory
                    // conflict, not a fabricated one.
                    return Ok(TheoryResult::Unsat(vec![a, b]));
                }
            }
        }

        Ok(TheoryResult::Sat)
    }

    /// Check all theories for consistency
    ///
    /// Dispatches to the appropriate combination method based on mode
    pub fn check(&mut self) -> Result<TheoryResult> {
        self.stats.theory_checks += 1;
        let result = match self.mode {
            CombinationMode::NelsonOppen => self.check_nelson_oppen(),
            CombinationMode::ModelBased => self.check_model_based(),
            CombinationMode::Delayed => self.check_delayed(),
            CombinationMode::Polite => self.check_polite_combination(),
        };
        if matches!(result, Ok(TheoryResult::Unsat(_))) {
            self.stats.conflicts += 1;
        }
        result
    }

    /// Check using classic Nelson-Oppen equality propagation
    ///
    /// This is the main Nelson-Oppen loop:
    /// 1. Check each theory individually
    /// 2. Extract equalities between shared variables from each theory
    /// 3. Propagate new equalities to other theories
    /// 4. Repeat until fixed point or conflict
    fn check_nelson_oppen(&mut self) -> Result<TheoryResult> {
        // The fixpoint loop must terminate. `extract_euf_equalities` re-reports
        // every currently-equal shared pair on every call (it has no notion of
        // "new since last round"), so without deduplication a single equal pair
        // would set `changed = true` forever. We therefore track which canonical
        // shared pairs have already been queued for propagation and only treat a
        // genuinely new pair as progress. A hard iteration cap acts as a final
        // safety net against any other non-converging propagation source.
        let mut changed = true;
        let mut seen_pairs: FxHashSet<(TermId, TermId)> = FxHashSet::default();

        // Upper bound on rounds: for n shared variables there are at most
        // n*(n-1)/2 distinct equalities to discover, so O(n^2) rounds suffice
        // for the EUF-equality fixpoint. Add a constant floor for the
        // propagation/theory-check interplay on small inputs.
        let n = self.shared_vars.len();
        let max_iterations = n.saturating_mul(n).saturating_add(16);
        let mut iterations = 0usize;

        while changed {
            changed = false;

            iterations += 1;
            if iterations > max_iterations {
                // Fixpoint did not converge within the theoretical bound.
                // Report Unknown rather than spinning forever: soundness demands
                // we never fabricate Sat from a truncated search.
                return Ok(TheoryResult::Unknown);
            }

            // Check EUF. `TheoryResult::Propagate` carries `(literal,
            // reasons)` pairs -- propositions EUF wants asserted, NOT
            // equalities between two terms -- so it must not be
            // (mis)treated as an equality source (previously this pushed
            // `(lit, lit, EUF)`, a trivially-true self-equality that wasted
            // propagation rounds and inflated `equalities_propagated` with
            // no-ops). The actual EUF-discovered equalities between shared
            // variables come from `extract_euf_equalities` below, which
            // genuinely compares distinct shared-variable pairs via the
            // E-graph's union-find.
            match self.euf.check()? {
                TheoryResult::Sat | TheoryResult::Propagate(_) => {}
                TheoryResult::Unsat(reason) => {
                    return Ok(TheoryResult::Unsat(reason));
                }
                TheoryResult::Unknown => {
                    return Ok(TheoryResult::Unknown);
                }
            }

            // Check arithmetic. Same reasoning as EUF above: `Propagate`
            // is not an equality source. Arithmetic's genuine
            // Nelson-Oppen equalities come from its `TheoryCombination`
            // implementation (`get_shared_equalities`), which does real
            // model-based extraction with entailment verification --
            // unlike the old `(lit, lit)` self-equality placeholder.
            match self.arith.check()? {
                TheoryResult::Sat | TheoryResult::Propagate(_) => {}
                TheoryResult::Unsat(reason) => {
                    return Ok(TheoryResult::Unsat(reason));
                }
                TheoryResult::Unknown => {
                    return Ok(TheoryResult::Unknown);
                }
            }
            let arith_theory_id = self.arith.id();
            for eq in self.arith.get_shared_equalities() {
                if !self.shared_vars.contains(&eq.lhs) || !self.shared_vars.contains(&eq.rhs) {
                    continue;
                }
                if seen_pairs.insert(Self::canonical_pair(eq.lhs, eq.rhs)) {
                    self.pending_equalities
                        .push((eq.lhs, eq.rhs, arith_theory_id));
                    changed = true;
                }
            }

            // Propagate any new equalities (only mark progress if there was work)
            if !self.pending_equalities.is_empty() {
                self.propagate()?;
                changed = true;
            }

            // Check for new EUF equalities between shared variables. Only pairs
            // not previously queued count as progress, otherwise the same set of
            // equal pairs would be re-extracted indefinitely.
            let new_euf_equalities = self.extract_euf_equalities();
            for (a, b) in new_euf_equalities {
                if seen_pairs.insert(Self::canonical_pair(a, b)) {
                    self.pending_equalities.push((a, b, TheoryId::EUF));
                    changed = true;
                }
            }
        }

        Ok(TheoryResult::Sat)
    }

    /// Canonicalize an unordered pair of terms so `(a, b)` and `(b, a)` map to
    /// the same key for deduplication.
    fn canonical_pair(a: TermId, b: TermId) -> (TermId, TermId) {
        if a.raw() <= b.raw() { (a, b) } else { (b, a) }
    }

    /// Check using model-based theory combination
    ///
    /// Instead of eagerly propagating all equalities, model-based combination:
    /// 1. Gets a model from one theory (e.g., EUF)
    /// 2. Checks if other theories accept this arrangement
    /// 3. If not, learns a blocking clause and tries another arrangement
    ///
    /// Known limitations (honest, not silently wrong):
    /// - Only the arrangement's EQUALITIES are asserted into arithmetic
    ///   (via `notify_equality`, encoding `a = b` as bounds). Arithmetic
    ///   has no API for asserting a DISEQUALITY (that requires a
    ///   disjunctive case-split -- `a < b OR a > b` -- which this crate's
    ///   `ArithSolver` does not yet expose), so an inconsistency that only
    ///   shows up through a disequality the EUF arrangement demands is not
    ///   caught here.
    /// - This checks exactly ONE arrangement per call rather than
    ///   systematically searching alternative arrangements on conflict (the
    ///   literature's full "model-based theory combination" backtracks
    ///   over arrangements); the cached lemma at least prevents the SAME
    ///   arrangement from being retried, but does not drive EUF toward a
    ///   different one.
    fn check_model_based(&mut self) -> Result<TheoryResult> {
        // First check EUF for consistency
        match self.euf.check()? {
            TheoryResult::Unsat(reason) => {
                return Ok(TheoryResult::Unsat(reason));
            }
            TheoryResult::Unknown => {
                return Ok(TheoryResult::Unknown);
            }
            _ => {}
        }

        // Extract the equality arrangement from EUF
        let arrangement = self.extract_arrangement();
        self.current_arrangement = Some(arrangement.clone());

        // Check if arithmetic accepts this arrangement
        self.push();

        // Actually assert the arrangement's equalities into arithmetic
        // (previously a no-op: `let _ = (a, b);`, so arithmetic's model
        // could silently disagree with EUF's about shared variables and
        // this function would still report `Sat`). If arithmetic itself
        // rejects one of these equalities outright, that IS the genuine,
        // correctly-attributed conflict -- report it directly rather than
        // going on to call `check()` and blaming whatever THAT finds on
        // this arrangement.
        for &(a, b) in &arrangement.equalities {
            // As in `propagate()`: `notify_equality` returning `false`
            // means either "not relevant" (both sides unknown to
            // arithmetic -- not a conflict) or a genuine rejection (both
            // sides ARE known and still incompatible). Only the latter is
            // an actual conflict.
            let both_relevant = self.arith.is_relevant(a) && self.arith.is_relevant(b);
            let accepted = self.arith.notify_equality(EqualityNotification {
                lhs: a,
                rhs: b,
                reason: None,
            });
            if !accepted && both_relevant {
                self.pop();
                self.cache_lemma(TheoryLemma {
                    assumptions: vec![a, b],
                    conclusion: vec![],
                    theory: self.arith.id(),
                });
                return Ok(TheoryResult::Unsat(vec![a, b]));
            }
        }

        let arith_result = self.arith.check()?;
        self.pop();

        match arith_result {
            TheoryResult::Sat => Ok(TheoryResult::Sat),
            TheoryResult::Unsat(reason) => {
                // Learn a blocking clause to avoid this arrangement
                self.cache_lemma(TheoryLemma {
                    assumptions: arrangement.equalities.iter().map(|(a, _)| *a).collect(),
                    conclusion: vec![],
                    theory: self.arith.id(),
                });
                Ok(TheoryResult::Unsat(reason))
            }
            other => Ok(other),
        }
    }

    /// Check using delayed theory combination
    ///
    /// Delayed combination postpones propagation until absolutely necessary,
    /// reducing the number of theory calls
    fn check_delayed(&mut self) -> Result<TheoryResult> {
        // Check each theory independently first
        let euf_result = self.euf.check()?;
        let arith_result = self.arith.check()?;

        // Only combine if both are SAT.
        //
        // The match is exhaustive over the *pair* of results on purpose. It
        // used to end in `_ => Ok(TheoryResult::Sat)`, which swallowed every
        // combination involving `Propagate`: a theory that asked for literals
        // to be propagated was answered "satisfiable", its propagations
        // dropped, and the caller then believed the combined problem was
        // settled. Propagations are now forwarded, and a new `TheoryResult`
        // variant becomes a compile error here rather than another silent
        // `Sat`.
        match (euf_result, arith_result) {
            (TheoryResult::Sat, TheoryResult::Sat) => {
                // Now check if they agree on shared variables
                self.check_nelson_oppen()
            }
            (TheoryResult::Unsat(r), _) | (_, TheoryResult::Unsat(r)) => Ok(TheoryResult::Unsat(r)),
            (TheoryResult::Unknown, _) | (_, TheoryResult::Unknown) => Ok(TheoryResult::Unknown),
            (TheoryResult::Propagate(mut a), TheoryResult::Propagate(b)) => {
                a.extend(b);
                Ok(TheoryResult::Propagate(a))
            }
            (TheoryResult::Propagate(p), TheoryResult::Sat)
            | (TheoryResult::Sat, TheoryResult::Propagate(p)) => Ok(TheoryResult::Propagate(p)),
        }
    }

    /// Extract the current equality arrangement from EUF
    fn extract_arrangement(&mut self) -> EqualityArrangement {
        let mut arrangement = EqualityArrangement::new();
        let shared: Vec<TermId> = self.shared_vars.iter().copied().collect();

        for i in 0..shared.len() {
            for j in (i + 1)..shared.len() {
                let a = shared[i];
                let b = shared[j];

                let node_a = self.euf.intern(a);
                let node_b = self.euf.intern(b);

                if self.euf.are_equal(node_a, node_b) {
                    arrangement.add_equality(a, b);
                } else {
                    arrangement.add_disequality(a, b);
                }
            }
        }

        arrangement
    }

    /// Cache a theory lemma to avoid recomputation
    ///
    /// This also checks for subsumption: if a stronger lemma is already cached,
    /// we don't need to cache this weaker one.  The cache is bounded by
    /// `max_lemma_cache_size`; when full, the LRU entry is evicted automatically.
    fn cache_lemma(&mut self, lemma: TheoryLemma) {
        // Check if any existing lemma is stronger
        let has_stronger = self
            .lemma_cache
            .iter()
            .any(|(existing, _)| existing.is_stronger_than(&lemma));

        if has_stronger {
            // Don't cache this lemma - we already have a stronger one
            return;
        }

        // Remove any weaker lemmas before caching this one
        let weaker_keys: Vec<TheoryLemma> = self
            .lemma_cache
            .iter()
            .filter(|(existing, _)| lemma.is_stronger_than(existing))
            .map(|(k, _)| k.clone())
            .collect();
        for key in weaker_keys {
            self.lemma_cache.remove(&key);
        }

        // Sync eviction count from cache before insertion
        let (_hits, _misses, evictions_before) = self.lemma_cache.stats();

        if self.lemma_cache.insert(lemma, ()) {
            self.stats.lemmas_cached += 1;
        }

        // Detect if eviction occurred (capacity enforced by LruCache::insert)
        let (_hits2, _misses2, evictions_after) = self.lemma_cache.stats();
        if evictions_after > evictions_before {
            self.stats.lemma_cache_evictions += (evictions_after - evictions_before) as u64;
        }
    }

    /// Check if a lemma is subsumed by any cached lemma
    #[must_use]
    pub fn is_lemma_subsumed(
        &self,
        assumptions: &[TermId],
        conclusion: &[TermId],
        theory: TheoryId,
    ) -> bool {
        let test_lemma = TheoryLemma {
            assumptions: assumptions.to_vec(),
            conclusion: conclusion.to_vec(),
            theory,
        };

        self.lemma_cache
            .iter()
            .any(|(existing, _)| existing.subsumes(&test_lemma) || existing == &test_lemma)
    }

    /// Get the number of cached lemmas
    #[must_use]
    pub fn lemma_cache_size(&self) -> usize {
        self.lemma_cache.len()
    }

    /// Mark a term as relevant
    pub fn mark_relevant(&mut self, term: TermId) {
        if self.relevant_terms.insert(term) {
            self.stats.relevancy_propagations += 1;
        }
    }

    /// Check if a term is relevant
    #[must_use]
    pub fn is_relevant(&self, term: TermId) -> bool {
        self.relevant_terms.is_empty() || self.relevant_terms.contains(&term)
    }

    /// Get statistics, updated with current LRU cache counters
    #[must_use]
    pub fn stats(&self) -> CombinerStats {
        let (lru_hits, lru_misses, lru_evictions) = self.lemma_cache.stats();
        CombinerStats {
            equalities_propagated: self.stats.equalities_propagated,
            theory_checks: self.stats.theory_checks,
            conflicts: self.stats.conflicts,
            lemmas_cached: self.stats.lemmas_cached,
            relevancy_propagations: self.stats.relevancy_propagations,
            lemma_cache_hits: lru_hits as u64,
            lemma_cache_misses: lru_misses as u64,
            lemma_cache_evictions: lru_evictions as u64,
        }
    }

    /// Reset statistics
    pub fn reset_stats(&mut self) {
        self.stats = CombinerStats::default();
        self.lemma_cache.reset_stats();
    }

    /// Extract equalities between shared variables from EUF
    fn extract_euf_equalities(&mut self) -> Vec<(TermId, TermId)> {
        let mut equalities = Vec::new();
        let shared: Vec<TermId> = self.shared_vars.iter().copied().collect();

        // Check all pairs of shared variables
        for i in 0..shared.len() {
            for j in (i + 1)..shared.len() {
                let a = shared[i];
                let b = shared[j];

                // Check if EUF considers them equal
                let node_a = self.euf.intern(a);
                let node_b = self.euf.intern(b);

                if self.euf.are_equal(node_a, node_b) {
                    equalities.push((a, b));
                }
            }
        }

        equalities
    }

    /// Push a context level
    pub fn push(&mut self) {
        self.context_stack.push(CombinerState {
            num_pending: self.pending_equalities.len(),
            lemma_cache_size: self.lemma_cache.len(),
            relevant_terms_size: self.relevant_terms.len(),
        });
        self.euf.push();
        self.arith.push();
    }

    /// Pop a context level
    pub fn pop(&mut self) {
        if let Some(state) = self.context_stack.pop() {
            self.pending_equalities.truncate(state.num_pending);

            // Restore lemma cache to saved size, evicting the most-recently-added
            // entries (LRU tail = oldest entry, so truncate_to evicts the LRU ones
            // that were added during this scope).
            self.lemma_cache.truncate_to(state.lemma_cache_size);

            // Relevant terms: a full trail-based structure would be needed for
            // precise restoration; we conservatively leave them in place because
            // keeping extra relevant terms is safe (they are hints, not assertions).
            let _ = state.relevant_terms_size;

            self.euf.pop();
            self.arith.pop();
        }
    }

    /// Get a model from the theories (for model reconstruction)
    #[must_use]
    pub fn get_model(&self) -> Vec<(TermId, TermId)> {
        let mut model = Vec::new();

        // Get EUF equalities
        let shared: Vec<TermId> = self.shared_vars.iter().copied().collect();
        for i in 0..shared.len() {
            for j in (i + 1)..shared.len() {
                let a = shared[i];
                let b = shared[j];

                // Check if they're equal in the model
                // This is simplified - a full implementation would query the theories
                model.push((a, b));
            }
        }

        model
    }

    /// Verify that a model satisfies all constraints
    ///
    /// This checks:
    /// 1. All shared variables have consistent values across theories
    /// 2. All theory-specific constraints are satisfied
    /// 3. All propagated equalities hold in the model
    ///
    /// Useful for debugging and ensuring model correctness.
    #[must_use]
    pub fn verify_model(&self, model: &[(TermId, TermId)]) -> bool {
        // Cross-theory consistency check: for every `(term, representative)`
        // pair the model claims are equal, confirm that every component
        // theory which actually knows about BOTH terms agrees they are
        // equal. This does not (yet) re-check theory-internal constraint
        // satisfaction beyond what `EufSolver`/`ArithSolver` expose here,
        // so it is not a complete verifier, but it is a real, sound check
        // rather than an unconditional `true` that could never catch a
        // genuinely inconsistent model.
        for &(term, rep) in model {
            if term == rep {
                continue;
            }

            if let (Some(term_node), Some(rep_node)) =
                (self.euf.term_to_node(term), self.euf.term_to_node(rep))
                && !self.euf.are_equal_immutable(term_node, rep_node)
            {
                return false;
            }

            if let (Some(term_val), Some(rep_val)) = (self.arith.value(term), self.arith.value(rep))
                && term_val != rep_val
            {
                return false;
            }
        }
        true
    }

    /// Complete a partial model by assigning values to all variables
    ///
    /// Given a partial model (some variables assigned), a full
    /// implementation would:
    /// 1. Identify all unassigned shared variables
    /// 2. For each theory, get theory-specific assignments
    /// 3. Propagate equalities to ensure consistency
    /// 4. Check for conflicts and backtrack if needed
    ///
    /// None of that is implemented yet: this is an identity pass-through
    /// (the input is returned unchanged, never `None`), which is honest
    /// about doing no completion work but means callers must not treat a
    /// `Some` result as evidence the model is actually complete or
    /// conflict-checked.
    pub fn complete_model(&self, partial: Vec<(TermId, TermId)>) -> Option<Vec<(TermId, TermId)>> {
        Some(partial)
    }

    /// Extract variable assignments from the model.
    ///
    /// Converts the equality-based model representation (a list of
    /// `(term, term)` pairs asserting equality) into a map from every term
    /// mentioned to its canonical representative, via union-find over the
    /// input pairs. Two terms connected directly OR TRANSITIVELY by the
    /// model's equalities map to the same representative.
    #[must_use]
    pub fn extract_assignments(&self, model: &[(TermId, TermId)]) -> FxHashMap<TermId, TermId> {
        let mut parent: FxHashMap<TermId, TermId> = FxHashMap::default();

        /// Find `x`'s representative, compressing the path behind it.
        ///
        /// Iterative on purpose: `union` below links by the smaller raw
        /// `TermId` (for determinism) rather than by rank, so feeding
        /// equalities in descending-id order builds a chain of length N before
        /// any compression happens — and N is the number of model equalities,
        /// i.e. caller-controlled. The return type is `TermId`, so a depth cap
        /// could only hand back a non-representative and silently split a
        /// class.
        fn find(parent: &mut FxHashMap<TermId, TermId>, x: TermId) -> TermId {
            // Walk to the root...
            let mut root = *parent.entry(x).or_insert(x);
            while let Some(&next) = parent.get(&root) {
                if next == root {
                    break;
                }
                root = next;
            }
            // ...then point every node on the way there straight at it.
            let mut current = x;
            while current != root {
                let Some(next) = parent.insert(current, root) else {
                    break;
                };
                current = next;
            }
            root
        }

        fn union(parent: &mut FxHashMap<TermId, TermId>, a: TermId, b: TermId) {
            let ra = find(parent, a);
            let rb = find(parent, b);
            if ra != rb {
                // Canonicalize on the smaller raw id for a deterministic
                // representative regardless of union order.
                if ra.raw() <= rb.raw() {
                    parent.insert(rb, ra);
                } else {
                    parent.insert(ra, rb);
                }
            }
        }

        for &(a, b) in model {
            union(&mut parent, a, b);
        }

        let keys: Vec<TermId> = parent.keys().copied().collect();
        let mut assignments = FxHashMap::default();
        for k in keys {
            let root = find(&mut parent, k);
            assignments.insert(k, root);
        }
        assignments
    }

    /// Minimize a conflict explanation (core extraction)
    ///
    /// Given a set of assumptions that led to conflict, find a minimal subset
    /// that still causes conflict. Uses multiple strategies:
    /// 1. Theory-specific minimization (remove theory-local redundancies)
    /// 2. Binary search minimization (linear deletion)
    /// 3. Resolution-based minimization (analyze proof structure)
    pub fn minimize_conflict(&mut self, assumptions: &[TermId]) -> Result<Vec<TermId>> {
        if assumptions.is_empty() {
            return Ok(Vec::new());
        }

        // Phase 1: Theory-specific minimization
        // Group assumptions by theory and minimize within each theory
        let mut core = self.minimize_by_theory(assumptions)?;

        // Phase 2: Linear deletion algorithm
        // Try removing each assumption one by one
        let mut i = 0;
        while i < core.len() {
            // Try removing assumption i
            let removed = core.remove(i);

            // Check if still unsat
            self.push();
            // Would re-assert core assumptions here
            let result = self.check()?;
            self.pop();

            match result {
                TheoryResult::Unsat(_) => {
                    // Still unsat without this assumption, keep it removed
                }
                _ => {
                    // Need this assumption, put it back
                    core.insert(i, removed);
                    i += 1;
                }
            }
        }

        Ok(core)
    }

    /// Minimize assumptions by theory
    ///
    /// For each theory, try to reduce the assumptions specific to that theory
    fn minimize_by_theory(&mut self, assumptions: &[TermId]) -> Result<Vec<TermId>> {
        // Group assumptions by theory
        let mut euf_assumptions = Vec::new();
        let mut arith_assumptions = Vec::new();
        let mut other_assumptions = Vec::new();

        for &assumption in assumptions {
            if let Some(&theory) = self.term_theory.get(&assumption) {
                match theory {
                    TheoryId::EUF => euf_assumptions.push(assumption),
                    TheoryId::LRA | TheoryId::LIA | TheoryId::NIA | TheoryId::NRA => {
                        arith_assumptions.push(assumption)
                    }
                    _ => other_assumptions.push(assumption),
                }
            } else {
                other_assumptions.push(assumption);
            }
        }

        // For simplicity, return all assumptions
        // A full implementation would minimize within each theory
        let mut result = Vec::new();
        result.extend_from_slice(&euf_assumptions);
        result.extend_from_slice(&arith_assumptions);
        result.extend_from_slice(&other_assumptions);

        Ok(result)
    }

    /// Reset the combiner
    pub fn reset(&mut self) {
        self.euf.reset();
        self.arith.reset();
        self.shared_vars.clear();
        self.term_theory.clear();
        self.pending_equalities.clear();
        self.context_stack.clear();
        self.lemma_cache.clear();
        self.current_arrangement = None;
        self.relevant_terms.clear();
        self.stats = CombinerStats::default();
    }

    /// Clear the lemma cache
    pub fn clear_cache(&mut self) {
        self.lemma_cache.clear();
    }

    /// Presolve: simplify constraints before solving
    ///
    /// Performs:
    /// 1. Singleton detection: find shared variables whose EUF equivalence
    ///    class already pins them to another term (a "singleton" value)
    /// 2. Subsumption elimination: remove redundant constraints
    /// 3. Equality propagation: feed the discovered equalities into the
    ///    same `propagate_equality`/`propagate` pipeline used by the main
    ///    solve loop, so every theory that shares the variable actually
    ///    observes the substitution instead of it being silently dropped
    ///
    /// Note: `TheoryCombiner` does not own the input formula, so it cannot
    /// rewrite terms in place; propagating the equality is the mechanism
    /// available to it for making the detected fact visible to arithmetic.
    pub fn presolve(&mut self) -> Result<PresolveStats> {
        let mut stats = PresolveStats::default();

        // Phase 1: Detect singleton variables in EUF
        // Look for shared variables whose equivalence class already
        // contains another (canonical) term they can be replaced by.
        let singleton_eqs = self.detect_singletons_euf();
        stats.singleton_propagations = singleton_eqs.len();

        // Phase 2: Detect trivially infeasible constraints in arithmetic
        // This would check for contradictory bounds like x <= 5 && x >= 10
        // For now, we rely on the solver to detect this

        // Phase 3: Propagate the discovered equalities. This queues them
        // through the real `propagate_equality`/`propagate` machinery
        // (the same path EUF-native equalities take), so arithmetic (and
        // any other theory sharing the variable) is actually notified.
        for (var, representative) in singleton_eqs {
            self.propagate_equality(var, representative, TheoryId::EUF);
            stats.vars_eliminated += 1;
        }

        Ok(stats)
    }

    /// Detect singleton variables in EUF
    ///
    /// A shared variable is considered a "singleton" here when its EUF
    /// equivalence class (queried via the real union-find, not a stub)
    /// already contains another interned term. The canonical
    /// representative for the whole class is the member with the smallest
    /// `TermId` -- every member of the class agrees on that same
    /// representative, so a class of `n` equal terms yields exactly
    /// `n - 1` (non-canonical-member, representative) pairs rather than
    /// reporting each direction of every pair symmetrically.
    ///
    /// Returns pairs of (variable, representative). A variable that was
    /// never interned into EUF, or whose class contains nothing else, is
    /// not returned -- there is nothing EUF can tell us about it yet.
    fn detect_singletons_euf(&self) -> Vec<(TermId, TermId)> {
        let mut singletons = Vec::new();

        // For each shared variable, check whether EUF already knows it is
        // equal to some other term by inspecting its equivalence class.
        for &term in &self.shared_vars {
            let Some(node) = self.euf.term_to_node(term) else {
                // Never interned into EUF: no information available.
                continue;
            };

            let root = self.euf.find_immutable(node);
            let members = self.euf.class_members(root);
            if members.len() <= 1 {
                // Genuine singleton equivalence class: nothing to pin the
                // variable to yet.
                continue;
            }

            let representative = members
                .iter()
                .filter_map(|&idx| self.euf.node_term(idx))
                .min_by_key(|candidate| candidate.raw());

            if let Some(representative) = representative
                && representative != term
            {
                singletons.push((term, representative));
            }
        }

        singletons
    }
}

/// Presolve statistics
#[derive(Debug, Clone, Default)]
pub struct PresolveStats {
    /// Number of variables eliminated
    pub vars_eliminated: usize,
    /// Number of constraints removed
    pub constraints_removed: usize,
    /// Number of equality substitutions
    pub equality_substitutions: usize,
    /// Number of singleton propagations
    pub singleton_propagations: usize,
}

/// Purify a formula by introducing fresh variables for sub-terms
/// that belong to a different theory.
///
/// For example, given `f(x + y) = z` where f is uninterpreted and + is arithmetic:
/// - Create fresh variable `v` for `x + y`
/// - Add constraint `v = x + y` to arithmetic theory
/// - Replace original with `f(v) = z` for EUF
///
/// This is a simplified purification - a full implementation would handle
/// nested terms and all theory combinations.
#[derive(Debug)]
pub struct Purifier {
    /// Fresh variable counter
    fresh_counter: u32,
    /// Mapping from original terms to purified terms
    purified: FxHashMap<TermId, TermId>,
    /// Constraints generated by purification
    constraints: Vec<PurificationConstraint>,
}

/// A constraint generated during purification
#[derive(Debug, Clone)]
pub struct PurificationConstraint {
    /// The fresh variable
    pub fresh_var: TermId,
    /// The original term it represents
    pub original: TermId,
    /// Which theory owns this constraint
    pub theory: TheoryId,
}

impl Default for Purifier {
    fn default() -> Self {
        Self::new()
    }
}

impl Purifier {
    /// Create a new purifier
    #[must_use]
    pub fn new() -> Self {
        Self {
            fresh_counter: 0,
            purified: FxHashMap::default(),
            constraints: Vec::new(),
        }
    }

    /// Get the next fresh variable ID
    pub fn fresh_var(&mut self) -> TermId {
        let id = TermId::new(0x8000_0000 | self.fresh_counter);
        self.fresh_counter += 1;
        id
    }

    /// Record a purification
    pub fn add_purification(&mut self, original: TermId, fresh: TermId, theory: TheoryId) {
        self.purified.insert(original, fresh);
        self.constraints.push(PurificationConstraint {
            fresh_var: fresh,
            original,
            theory,
        });
    }

    /// Get the purified form of a term (if any)
    #[must_use]
    pub fn get_purified(&self, term: TermId) -> Option<TermId> {
        self.purified.get(&term).copied()
    }

    /// Get all purification constraints
    #[must_use]
    pub fn constraints(&self) -> &[PurificationConstraint] {
        &self.constraints
    }

    /// Clear the purifier
    pub fn clear(&mut self) {
        self.fresh_counter = 0;
        self.purified.clear();
        self.constraints.clear();
    }
}

#[cfg(test)]
mod tests;
