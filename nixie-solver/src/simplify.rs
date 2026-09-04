//! Formula simplification and preprocessing
//!
//! This module provides simplification passes that run before the main solver
//! to reduce problem size and improve solving performance.

// Allow these clippy lints for simplification code patterns
#![allow(clippy::map_entry)] // contains_key + insert pattern used for clarity
#![allow(clippy::only_used_in_recursion)] // recursive simplification intentional
#![allow(clippy::for_kv_map)] // iterating map keys with values pattern

#[allow(unused_imports)]
use crate::prelude::*;
use nixie_core::ast::{TermId, TermKind, TermManager};

/// Simplification statistics
#[derive(Debug, Clone, Default)]
pub struct SimplifyStats {
    /// Number of constant propagations performed
    pub const_propagations: usize,
    /// Number of terms eliminated
    pub terms_eliminated: usize,
    /// Number of trivial equations detected
    pub trivial_equalities: usize,
    /// Number of contradictions found
    pub contradictions_found: usize,
    /// Number of nested operations flattened
    pub operations_flattened: usize,
    /// Number of duplicate literals eliminated
    pub duplicates_eliminated: usize,
    /// Number of tautologies detected
    pub tautologies_detected: usize,
}

/// Context-aware formula simplifier
///
/// Performs simplification passes including:
/// - Constant propagation
/// - Boolean simplification
/// - Trivial equality elimination
/// - Contradiction detection
#[derive(Debug)]
pub struct Simplifier {
    /// Cache of simplified terms
    cache: FxHashMap<TermId, TermId>,
    /// Statistics
    stats: SimplifyStats,
}

impl Simplifier {
    /// Create a new simplifier
    #[must_use]
    pub fn new() -> Self {
        Self {
            cache: FxHashMap::default(),
            stats: SimplifyStats::default(),
        }
    }

    /// Get simplification statistics
    #[must_use]
    #[allow(dead_code)]
    pub fn stats(&self) -> &SimplifyStats {
        &self.stats
    }

    /// Reset the simplifier state
    #[allow(dead_code)]
    pub fn reset(&mut self) {
        self.cache.clear();
        self.stats = SimplifyStats::default();
    }

    /// Simplify a term
    ///
    /// Returns a simplified version of the term, or the original if no simplification applies
    ///
    /// # Traversal
    ///
    /// The walk is an explicit heap stack, not recursion: nesting depth is
    /// caller-controlled (an assertion is whatever the SMT-LIB input built),
    /// and the return type is a bare `TermId` with no error channel, so a
    /// depth cap could only ever return a *differently simplified* term --
    /// silently wrong output rather than a reported failure.
    ///
    /// A node is only handed to [`Self::simplify_impl`] once every term that
    /// rule application will look up is already in `self.cache`, so
    /// `simplify_impl` performs one node's worth of rewriting and never
    /// descends. See [`Self::push_missing_dependencies`] for what "every term
    /// it will look up" means -- notably it includes the arguments of a
    /// conjunct that itself simplified to a conjunction, which the flattening
    /// rules simplify in turn.
    ///
    /// One deliberate difference from the previous recursive version: a
    /// subterm that a short-circuiting rule would have skipped (the `y` in
    /// `(and false y)`) is now simplified anyway, so the diagnostic counters
    /// in [`SimplifyStats`] can be higher than before. The *terms* produced
    /// are unchanged -- caching a correct simplification of an unused subterm
    /// cannot change any other node's result.
    pub fn simplify(&mut self, term: TermId, manager: &mut TermManager) -> TermId {
        // Check cache first
        if let Some(&simplified) = self.cache.get(&term) {
            return simplified;
        }

        let mut stack: Vec<TermId> = vec![term];
        while let Some(&top) = stack.last() {
            if self.cache.contains_key(&top) {
                stack.pop();
                continue;
            }

            if self.push_missing_dependencies(&mut stack, top, manager) > 0 {
                // Revisit `top` once its dependencies are cached.
                continue;
            }

            let result = self.simplify_impl(top, manager);
            self.cache.insert(top, result);
            stack.pop();
        }

        self.cache.get(&term).copied().unwrap_or(term)
    }

    /// Push every term [`Self::simplify_impl`] will need for `term` that is
    /// not simplified yet, returning how many were pushed.
    ///
    /// Two rounds are possible. The first pushes the direct children the rule
    /// set looks at. Once those are cached, a conjunction (disjunction) whose
    /// argument simplified to a conjunction (disjunction) additionally needs
    /// that nested argument list, because the flattening rule simplifies those
    /// nested arguments too; they are pushed on the second visit. Both rounds
    /// only ever push terms that are proper subterms of an already-simplified
    /// term, so the walk cannot cycle.
    fn push_missing_dependencies(
        &self,
        stack: &mut Vec<TermId>,
        term: TermId,
        manager: &TermManager,
    ) -> usize {
        let Some(t) = manager.get(term) else {
            return 0;
        };

        /// Push `child` unless it is already simplified; count the push.
        fn push_if_missing(
            cache: &FxHashMap<TermId, TermId>,
            stack: &mut Vec<TermId>,
            child: TermId,
            pushed: &mut usize,
        ) {
            if !cache.contains_key(&child) {
                stack.push(child);
                *pushed += 1;
            }
        }

        let cache = &self.cache;
        let mut pushed = 0;

        match &t.kind {
            TermKind::Not(arg) => push_if_missing(cache, stack, *arg, &mut pushed),
            TermKind::Implies(lhs, rhs) | TermKind::Eq(lhs, rhs) => {
                push_if_missing(cache, stack, *rhs, &mut pushed);
                push_if_missing(cache, stack, *lhs, &mut pushed);
            }
            TermKind::Ite(cond, then_br, else_br) => {
                push_if_missing(cache, stack, *else_br, &mut pushed);
                push_if_missing(cache, stack, *then_br, &mut pushed);
                push_if_missing(cache, stack, *cond, &mut pushed);
            }
            TermKind::And(args) | TermKind::Or(args) => {
                for &arg in args.iter().rev() {
                    push_if_missing(cache, stack, arg, &mut pushed);
                }
                if pushed > 0 {
                    // The nested arguments below depend on these results.
                    return pushed;
                }

                let flattens_and = matches!(t.kind, TermKind::And(_));
                for &arg in args.iter().rev() {
                    let Some(&simplified) = cache.get(&arg) else {
                        continue;
                    };
                    let Some(simplified_term) = manager.get(simplified) else {
                        continue;
                    };
                    let nested = match (&simplified_term.kind, flattens_and) {
                        (TermKind::And(nested), true) | (TermKind::Or(nested), false) => nested,
                        _ => continue,
                    };
                    for &nested_arg in nested.iter().rev() {
                        push_if_missing(cache, stack, nested_arg, &mut pushed);
                    }
                }
            }
            // Every other kind is returned unchanged by `simplify_impl`.
            _ => {}
        }

        pushed
    }

    /// Apply the rewrite rules for a single node.
    ///
    /// Every `self.simplify(..)` call below is a cache hit by construction:
    /// [`Self::simplify`] only calls this once the node's dependencies are
    /// simplified. (If one were somehow missing, the call would start its own
    /// -- still iterative -- solve rather than misbehave.)
    fn simplify_impl(&mut self, term: TermId, manager: &mut TermManager) -> TermId {
        let Some(t) = manager.get(term).cloned() else {
            return term;
        };

        match &t.kind {
            // Boolean simplifications
            TermKind::True | TermKind::False => term,

            TermKind::Not(arg) => {
                let arg_simplified = self.simplify(*arg, manager);

                // not(true) => false
                if let Some(arg_term) = manager.get(arg_simplified) {
                    if matches!(arg_term.kind, TermKind::True) {
                        self.stats.const_propagations += 1;
                        return manager.mk_false();
                    }
                    // not(false) => true
                    if matches!(arg_term.kind, TermKind::False) {
                        self.stats.const_propagations += 1;
                        return manager.mk_true();
                    }
                    // not(not(x)) => x
                    if let TermKind::Not(inner) = arg_term.kind {
                        self.stats.terms_eliminated += 1;
                        return inner;
                    }
                }

                if arg_simplified == *arg {
                    term
                } else {
                    manager.mk_not(arg_simplified)
                }
            }

            TermKind::And(args) => {
                let mut simplified_args = Vec::new();
                let mut seen = FxHashMap::default();

                for &arg in args.iter() {
                    let simplified = self.simplify(arg, manager);

                    // and(..., false, ...) => false
                    if let Some(arg_term) = manager.get(simplified) {
                        if matches!(arg_term.kind, TermKind::False) {
                            self.stats.const_propagations += 1;
                            return manager.mk_false();
                        }
                        // Skip true literals
                        if matches!(arg_term.kind, TermKind::True) {
                            self.stats.terms_eliminated += 1;
                            continue;
                        }

                        // Flatten nested ANDs: and(and(a, b), c) => and(a, b, c)
                        if let TermKind::And(nested_args) = &arg_term.kind {
                            self.stats.operations_flattened += 1;
                            let nested_args_cloned = nested_args.clone();
                            for &nested_arg in &nested_args_cloned {
                                let nested_simplified = self.simplify(nested_arg, manager);
                                if !seen.contains_key(&nested_simplified) {
                                    seen.insert(nested_simplified, ());
                                    simplified_args.push(nested_simplified);
                                } else {
                                    self.stats.duplicates_eliminated += 1;
                                }
                            }
                            continue;
                        }
                    }

                    // Check for contradictions: and(x, not(x)) => false.
                    // Membership is checked through `seen`, which mirrors
                    // `simplified_args` exactly (both are updated together
                    // below and in the nested-flatten branch) – a linear
                    // `Vec::contains` here made wide `and` nodes quadratic
                    // (a single 250 kB `tacas07/BBB-32` assert spent >25 s
                    // in these scans before the check went to the hash set).
                    if let Some(arg_term) = manager.get(simplified)
                        && let TermKind::Not(inner) = arg_term.kind
                        && seen.contains_key(&inner)
                    {
                        self.stats.contradictions_found += 1;
                        return manager.mk_false();
                    }
                    // Check if we already have not(arg) in the list.
                    let neg = manager.mk_not(simplified);
                    if seen.contains_key(&neg) {
                        self.stats.contradictions_found += 1;
                        return manager.mk_false();
                    }

                    // Eliminate duplicates
                    if !seen.contains_key(&simplified) {
                        seen.insert(simplified, ());
                        simplified_args.push(simplified);
                    } else {
                        self.stats.duplicates_eliminated += 1;
                    }
                }

                match simplified_args.len() {
                    0 => {
                        self.stats.const_propagations += 1;
                        manager.mk_true()
                    }
                    1 => {
                        self.stats.terms_eliminated += 1;
                        simplified_args[0]
                    }
                    _ => manager.mk_and(simplified_args),
                }
            }

            TermKind::Or(args) => {
                let mut simplified_args = Vec::new();
                let mut seen = FxHashMap::default();

                for &arg in args.iter() {
                    let simplified = self.simplify(arg, manager);

                    // or(..., true, ...) => true
                    if let Some(arg_term) = manager.get(simplified) {
                        if matches!(arg_term.kind, TermKind::True) {
                            self.stats.const_propagations += 1;
                            return manager.mk_true();
                        }
                        // Skip false literals
                        if matches!(arg_term.kind, TermKind::False) {
                            self.stats.terms_eliminated += 1;
                            continue;
                        }

                        // Flatten nested ORs: or(or(a, b), c) => or(a, b, c)
                        if let TermKind::Or(nested_args) = &arg_term.kind {
                            self.stats.operations_flattened += 1;
                            let nested_args_cloned = nested_args.clone();
                            for &nested_arg in &nested_args_cloned {
                                let nested_simplified = self.simplify(nested_arg, manager);
                                if !seen.contains_key(&nested_simplified) {
                                    seen.insert(nested_simplified, ());
                                    simplified_args.push(nested_simplified);
                                } else {
                                    self.stats.duplicates_eliminated += 1;
                                }
                            }
                            continue;
                        }
                    }

                    // Check for tautologies: or(x, not(x)) => true
                    // (`seen` mirrors `simplified_args`; see the And arm's
                    // note on why membership must not scan the Vec).
                    if let Some(arg_term) = manager.get(simplified)
                        && let TermKind::Not(inner) = arg_term.kind
                        && seen.contains_key(&inner)
                    {
                        self.stats.tautologies_detected += 1;
                        return manager.mk_true();
                    }
                    // Check if we already have not(arg) in the list.
                    let neg = manager.mk_not(simplified);
                    if seen.contains_key(&neg) {
                        self.stats.tautologies_detected += 1;
                        return manager.mk_true();
                    }

                    // Eliminate duplicates
                    if !seen.contains_key(&simplified) {
                        seen.insert(simplified, ());
                        simplified_args.push(simplified);
                    } else {
                        self.stats.duplicates_eliminated += 1;
                    }
                }

                match simplified_args.len() {
                    0 => {
                        self.stats.const_propagations += 1;
                        manager.mk_false()
                    }
                    1 => {
                        self.stats.terms_eliminated += 1;
                        simplified_args[0]
                    }
                    _ => manager.mk_or(simplified_args),
                }
            }

            TermKind::Implies(lhs, rhs) => {
                let lhs_simplified = self.simplify(*lhs, manager);
                let rhs_simplified = self.simplify(*rhs, manager);

                // false => x  =  true
                if let Some(lhs_term) = manager.get(lhs_simplified)
                    && matches!(lhs_term.kind, TermKind::False)
                {
                    self.stats.const_propagations += 1;
                    return manager.mk_true();
                }

                // true => x  =  x
                if let Some(lhs_term) = manager.get(lhs_simplified)
                    && matches!(lhs_term.kind, TermKind::True)
                {
                    self.stats.terms_eliminated += 1;
                    return rhs_simplified;
                }

                // x => true  =  true
                if let Some(rhs_term) = manager.get(rhs_simplified)
                    && matches!(rhs_term.kind, TermKind::True)
                {
                    self.stats.const_propagations += 1;
                    return manager.mk_true();
                }

                // x => false  =  not(x)
                if let Some(rhs_term) = manager.get(rhs_simplified)
                    && matches!(rhs_term.kind, TermKind::False)
                {
                    self.stats.terms_eliminated += 1;
                    return manager.mk_not(lhs_simplified);
                }

                if lhs_simplified == *lhs && rhs_simplified == *rhs {
                    term
                } else {
                    manager.mk_implies(lhs_simplified, rhs_simplified)
                }
            }

            TermKind::Ite(cond, then_br, else_br) => {
                let cond_simplified = self.simplify(*cond, manager);
                let then_simplified = self.simplify(*then_br, manager);
                let else_simplified = self.simplify(*else_br, manager);

                // ite(true, x, y) => x
                if let Some(cond_term) = manager.get(cond_simplified)
                    && matches!(cond_term.kind, TermKind::True)
                {
                    self.stats.const_propagations += 1;
                    return then_simplified;
                }

                // ite(false, x, y) => y
                if let Some(cond_term) = manager.get(cond_simplified)
                    && matches!(cond_term.kind, TermKind::False)
                {
                    self.stats.const_propagations += 1;
                    return else_simplified;
                }

                // ite(c, x, x) => x
                if then_simplified == else_simplified {
                    self.stats.terms_eliminated += 1;
                    return then_simplified;
                }

                if cond_simplified == *cond
                    && then_simplified == *then_br
                    && else_simplified == *else_br
                {
                    term
                } else {
                    manager.mk_ite(cond_simplified, then_simplified, else_simplified)
                }
            }

            TermKind::Eq(lhs, rhs) => {
                let lhs_simplified = self.simplify(*lhs, manager);
                let rhs_simplified = self.simplify(*rhs, manager);

                // x = x  =>  true
                if lhs_simplified == rhs_simplified {
                    self.stats.trivial_equalities += 1;
                    return manager.mk_true();
                }

                // Check for constant simplifications
                if let (Some(lhs_term), Some(rhs_term)) =
                    (manager.get(lhs_simplified), manager.get(rhs_simplified))
                {
                    // Handle datatype constructor equalities:
                    // C1(args) = C2(args') => false (different constructors)
                    // C(args) = C(args') => args = args' (same constructor)
                    if let (
                        TermKind::DtConstructor {
                            constructor: lhs_con,
                            args: lhs_args,
                        },
                        TermKind::DtConstructor {
                            constructor: rhs_con,
                            args: rhs_args,
                        },
                    ) = (&lhs_term.kind, &rhs_term.kind)
                    {
                        if lhs_con != rhs_con {
                            // Different constructors cannot be equal
                            self.stats.contradictions_found += 1;
                            return manager.mk_false();
                        } else if lhs_args.is_empty() && rhs_args.is_empty() {
                            // Same nullary constructor
                            self.stats.trivial_equalities += 1;
                            return manager.mk_true();
                        } else if lhs_args.len() == rhs_args.len() {
                            // Same constructor: decompose to field equalities
                            self.stats.terms_eliminated += 1;
                            let lhs_args = lhs_args.clone();
                            let rhs_args = rhs_args.clone();
                            let equalities: Vec<_> = lhs_args
                                .iter()
                                .zip(rhs_args.iter())
                                .map(|(&a, &b)| manager.mk_eq(a, b))
                                .collect();
                            return manager.mk_and(equalities);
                        }
                    }

                    // Handle boolean equalities with constants:
                    // x = true  => x
                    // x = false => NOT x
                    // true = x  => x
                    // false = x => NOT x
                    if lhs_term.sort == manager.sorts.bool_sort {
                        match (&lhs_term.kind, &rhs_term.kind) {
                            // Contradictory constants
                            (TermKind::True, TermKind::False)
                            | (TermKind::False, TermKind::True) => {
                                self.stats.contradictions_found += 1;
                                return manager.mk_false();
                            }
                            // Same constants
                            (TermKind::True, TermKind::True)
                            | (TermKind::False, TermKind::False) => {
                                self.stats.trivial_equalities += 1;
                                return manager.mk_true();
                            }
                            // x = true => x
                            (_, TermKind::True) => {
                                self.stats.terms_eliminated += 1;
                                return lhs_simplified;
                            }
                            // x = false => NOT x
                            (_, TermKind::False) => {
                                self.stats.terms_eliminated += 1;
                                return manager.mk_not(lhs_simplified);
                            }
                            // true = x => x
                            (TermKind::True, _) => {
                                self.stats.terms_eliminated += 1;
                                return rhs_simplified;
                            }
                            // false = x => NOT x
                            (TermKind::False, _) => {
                                self.stats.terms_eliminated += 1;
                                return manager.mk_not(rhs_simplified);
                            }
                            _ => {}
                        }
                    }
                }

                if lhs_simplified == *lhs && rhs_simplified == *rhs {
                    term
                } else {
                    manager.mk_eq(lhs_simplified, rhs_simplified)
                }
            }

            // For other term kinds, just return the original
            _ => term,
        }
    }

    /// Simplify multiple assertions
    ///
    /// Returns simplified versions of all assertions and a flag indicating
    /// if a contradiction was found
    #[allow(dead_code)]
    pub fn simplify_assertions(
        &mut self,
        assertions: &[TermId],
        manager: &mut TermManager,
    ) -> (Vec<TermId>, bool) {
        let mut simplified = Vec::new();
        let mut found_false = false;

        // Track constructor constraints for each variable
        // If a variable is constrained to multiple different constructors, it's UNSAT
        let mut var_constructors: FxHashMap<TermId, nixie_core::interner::Spur> =
            FxHashMap::default();

        for &assertion in assertions {
            let simp = self.simplify(assertion, manager);

            // Check if we found false
            if let Some(term) = manager.get(simp) {
                if matches!(term.kind, TermKind::False) {
                    found_false = true;
                }
                // Skip true assertions (they don't constrain anything)
                if matches!(term.kind, TermKind::True) {
                    continue;
                }

                // Check for datatype constructor mutual exclusivity
                // If we see (= var Constructor), track it
                if let TermKind::Eq(lhs, rhs) = &term.kind {
                    let (var, cons) = self.extract_var_constructor(*lhs, *rhs, manager);
                    if let Some((var_term, constructor)) = var.zip(cons) {
                        if let Some(&existing_con) = var_constructors.get(&var_term) {
                            if existing_con != constructor {
                                // Variable constrained to two different constructors - UNSAT
                                self.stats.contradictions_found += 1;
                                found_false = true;
                            }
                        } else {
                            var_constructors.insert(var_term, constructor);
                        }
                    }
                }
            }

            simplified.push(simp);
        }

        (simplified, found_false)
    }

    /// Extract (variable, constructor) pair from an equality if one side is a variable
    /// and the other is a DtConstructor
    fn extract_var_constructor(
        &self,
        lhs: TermId,
        rhs: TermId,
        manager: &TermManager,
    ) -> (Option<TermId>, Option<nixie_core::interner::Spur>) {
        let lhs_term = manager.get(lhs);
        let rhs_term = manager.get(rhs);

        match (lhs_term, rhs_term) {
            (Some(lt), Some(rt)) => {
                // lhs is var, rhs is constructor
                if matches!(lt.kind, TermKind::Var(_)) {
                    if let TermKind::DtConstructor { constructor, .. } = &rt.kind {
                        return (Some(lhs), Some(*constructor));
                    }
                }
                // rhs is var, lhs is constructor
                if matches!(rt.kind, TermKind::Var(_)) {
                    if let TermKind::DtConstructor { constructor, .. } = &lt.kind {
                        return (Some(rhs), Some(*constructor));
                    }
                }
                (None, None)
            }
            _ => (None, None),
        }
    }

    /// Apply unit propagation at preprocessing level
    /// Returns simplified assertions after propagating unit clauses
    #[allow(dead_code)]
    pub fn unit_propagation(
        &mut self,
        assertions: &[TermId],
        manager: &mut TermManager,
    ) -> Vec<TermId> {
        let mut units = FxHashMap::default(); // Map from term to its assigned value (true/false)
        let mut result = Vec::new();

        // First pass: collect unit clauses (single literals)
        for &assertion in assertions {
            if let Some(term) = manager.get(assertion) {
                match &term.kind {
                    TermKind::True | TermKind::False => {
                        // Already handled by simplification
                        result.push(assertion);
                    }
                    TermKind::Not(inner) => {
                        // Unit clause: not(x)
                        units.insert(*inner, false);
                        result.push(assertion);
                    }
                    _ => {
                        // Check if it's a variable (also a unit clause)
                        if matches!(term.kind, TermKind::Var(_)) {
                            units.insert(assertion, true);
                        }
                        result.push(assertion);
                    }
                }
            } else {
                result.push(assertion);
            }
        }

        // If we found unit clauses, propagate them
        if !units.is_empty() {
            self.stats.const_propagations += units.len();
            result = result
                .into_iter()
                .map(|term| self.substitute_units(term, &units, manager))
                .collect();
        }

        result
    }

    /// Substitute unit assignments in a term.
    ///
    /// Iterative post-order rebuild. Depth is caller-controlled (the nesting
    /// of the asserted formula) and the result is a bare `TermId`, so this
    /// walk must not be depth-capped: a cap would return a partially
    /// substituted formula while the caller believes every unit was
    /// propagated.
    ///
    /// A memo keyed on `TermId` makes a shared sub-DAG cost one visit instead
    /// of one visit per path. The memo is sound here because the result
    /// depends only on the subterm and on `units`, which is fixed for the
    /// whole call -- none of the handled kinds binds a variable.
    fn substitute_units(
        &mut self,
        term: TermId,
        units: &FxHashMap<TermId, bool>,
        manager: &mut TermManager,
    ) -> TermId {
        /// A node whose children are being substituted.
        enum Frame {
            /// Rebuild `not`.
            Not,
            /// Rebuild an `and` over `arity` children.
            And(usize),
            /// Rebuild an `or` over `arity` children.
            Or(usize),
        }

        let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
        // (term, pending frame). `None` means the term is a leaf for this walk.
        let mut steps: Vec<(TermId, Option<Frame>)> = vec![(term, None)];
        let mut values: Vec<TermId> = Vec::new();

        while let Some((current, frame)) = steps.pop() {
            let Some(frame) = frame else {
                // Expansion step.
                if let Some(&done) = memo.get(&current) {
                    values.push(done);
                    continue;
                }

                // Check if this term has a unit assignment
                if let Some(&value) = units.get(&current) {
                    let replacement = if value {
                        manager.mk_true()
                    } else {
                        manager.mk_false()
                    };
                    memo.insert(current, replacement);
                    values.push(replacement);
                    continue;
                }

                let Some(t) = manager.get(current).cloned() else {
                    memo.insert(current, current);
                    values.push(current);
                    continue;
                };

                match &t.kind {
                    TermKind::Not(arg) => {
                        steps.push((current, Some(Frame::Not)));
                        steps.push((*arg, None));
                    }
                    TermKind::And(args) => {
                        steps.push((current, Some(Frame::And(args.len()))));
                        for &arg in args.iter().rev() {
                            steps.push((arg, None));
                        }
                    }
                    TermKind::Or(args) => {
                        steps.push((current, Some(Frame::Or(args.len()))));
                        for &arg in args.iter().rev() {
                            steps.push((arg, None));
                        }
                    }
                    _ => {
                        memo.insert(current, current);
                        values.push(current);
                    }
                }
                continue;
            };

            // Rebuild step: the children's results are on top of `values`.
            let arity = match frame {
                Frame::Not => 1,
                Frame::And(n) | Frame::Or(n) => n,
            };
            let start = values.len().saturating_sub(arity);
            let new_args: Vec<TermId> = values.split_off(start);

            let original_args = Self::substitution_children(current, manager);
            let changed = new_args.len() != original_args.len()
                || new_args
                    .iter()
                    .zip(original_args.iter())
                    .any(|(new, old)| new != old);

            let rebuilt = if !changed {
                current
            } else {
                match frame {
                    Frame::Not => match new_args.first() {
                        Some(&arg) => manager.mk_not(arg),
                        // Unreachable: a `Not` frame always has one child.
                        None => current,
                    },
                    Frame::And(_) => manager.mk_and(new_args),
                    Frame::Or(_) => manager.mk_or(new_args),
                }
            };

            memo.insert(current, rebuilt);
            values.push(rebuilt);
        }

        values.pop().unwrap_or(term)
    }

    /// The children [`Self::substitute_units`] descends into, for the kinds it
    /// rebuilds.
    fn substitution_children(term: TermId, manager: &TermManager) -> Vec<TermId> {
        let Some(t) = manager.get(term) else {
            return Vec::new();
        };
        match &t.kind {
            TermKind::Not(arg) => vec![*arg],
            TermKind::And(args) | TermKind::Or(args) => args.to_vec(),
            _ => Vec::new(),
        }
    }

    /// Detect pure literals (literals that appear only in one polarity)
    /// Returns a map from pure literals to their polarity (true = positive, false = negative)
    #[allow(dead_code)]
    pub fn detect_pure_literals(
        &self,
        assertions: &[TermId],
        manager: &TermManager,
    ) -> FxHashMap<TermId, bool> {
        let mut positive = FxHashMap::default();
        let mut negative = FxHashMap::default();

        // Collect all literal occurrences
        for &assertion in assertions {
            self.collect_literals(assertion, true, &mut positive, &mut negative, manager);
        }

        // Find pure literals (appear only in one polarity)
        let mut pure_literals = FxHashMap::default();
        for (&lit, _) in &positive {
            if !negative.contains_key(&lit) {
                pure_literals.insert(lit, true);
            }
        }
        for (&lit, _) in &negative {
            if !positive.contains_key(&lit) {
                pure_literals.insert(lit, false);
            }
        }

        pure_literals
    }

    /// Collect literal occurrences with their polarities.
    ///
    /// Iterative: the walk returns `()`, so there is no channel through which
    /// a depth cap could report that it gave up -- a capped walk would just
    /// miss occurrences, and a literal wrongly classified as pure is assigned
    /// a fixed polarity, which is unsound.
    ///
    /// The `(term, polarity)` pairs already expanded are remembered, so a
    /// shared sub-DAG (or an ITE, whose condition is walked in both
    /// polarities) is expanded once per polarity instead of once per path.
    /// That is exactly semantics-preserving: the visit does nothing but insert
    /// into `positive`/`negative`, which is idempotent.
    fn collect_literals(
        &self,
        term: TermId,
        polarity: bool,
        positive: &mut FxHashMap<TermId, ()>,
        negative: &mut FxHashMap<TermId, ()>,
        manager: &TermManager,
    ) {
        let mut seen: FxHashSet<(TermId, bool)> = FxHashSet::default();
        let mut stack: Vec<(TermId, bool)> = vec![(term, polarity)];

        while let Some((current, polarity)) = stack.pop() {
            if !seen.insert((current, polarity)) {
                continue;
            }

            let Some(t) = manager.get(current) else {
                continue;
            };

            match &t.kind {
                TermKind::Var(_) => {
                    if polarity {
                        positive.insert(current, ());
                    } else {
                        negative.insert(current, ());
                    }
                }
                TermKind::Not(arg) => stack.push((*arg, !polarity)),
                TermKind::And(args) | TermKind::Or(args) => {
                    for &arg in args.iter().rev() {
                        stack.push((arg, polarity));
                    }
                }
                TermKind::Implies(lhs, rhs) => {
                    stack.push((*rhs, polarity));
                    stack.push((*lhs, !polarity));
                }
                TermKind::Ite(cond, then_br, else_br) => {
                    // For ITE, both branches can be reached
                    stack.push((*else_br, polarity));
                    stack.push((*then_br, polarity));
                    stack.push((*cond, false));
                    stack.push((*cond, true));
                }
                _ => {}
            }
        }
    }
}

impl Default for Simplifier {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simplify_not() {
        let mut manager = TermManager::new();
        let mut simplifier = Simplifier::new();

        // not(true) => false
        let t = manager.mk_true();
        let not_t = manager.mk_not(t);
        let result = simplifier.simplify(not_t, &mut manager);
        assert!(matches!(
            manager.get(result).expect("key should exist in map").kind,
            TermKind::False
        ));

        // not(false) => true
        let f = manager.mk_false();
        let not_f = manager.mk_not(f);
        let result = simplifier.simplify(not_f, &mut manager);
        assert!(matches!(
            manager.get(result).expect("key should exist in map").kind,
            TermKind::True
        ));
    }

    #[test]
    fn test_simplify_and() {
        let mut manager = TermManager::new();
        let mut simplifier = Simplifier::new();

        let x = manager.mk_var("x", manager.sorts.bool_sort);
        let t = manager.mk_true();
        let f = manager.mk_false();

        // and(x, true) => x
        let and_x_true = manager.mk_and([x, t]);
        let result = simplifier.simplify(and_x_true, &mut manager);
        assert_eq!(result, x);

        // and(x, false) => false
        let and_x_false = manager.mk_and([x, f]);
        let result = simplifier.simplify(and_x_false, &mut manager);
        assert!(matches!(
            manager.get(result).expect("key should exist in map").kind,
            TermKind::False
        ));
    }

    #[test]
    fn test_simplify_or() {
        let mut manager = TermManager::new();
        let mut simplifier = Simplifier::new();

        let x = manager.mk_var("x", manager.sorts.bool_sort);
        let t = manager.mk_true();
        let f = manager.mk_false();

        // or(x, false) => x
        let or_x_false = manager.mk_or([x, f]);
        let result = simplifier.simplify(or_x_false, &mut manager);
        assert_eq!(result, x);

        // or(x, true) => true
        let or_x_true = manager.mk_or([x, t]);
        let result = simplifier.simplify(or_x_true, &mut manager);
        assert!(matches!(
            manager.get(result).expect("key should exist in map").kind,
            TermKind::True
        ));
    }

    #[test]
    fn test_simplify_implies() {
        let mut manager = TermManager::new();
        let mut simplifier = Simplifier::new();

        let x = manager.mk_var("x", manager.sorts.bool_sort);
        let t = manager.mk_true();
        let f = manager.mk_false();

        // false => x  =  true
        let imp = manager.mk_implies(f, x);
        let result = simplifier.simplify(imp, &mut manager);
        assert!(matches!(
            manager.get(result).expect("key should exist in map").kind,
            TermKind::True
        ));

        // true => x  =  x
        let imp = manager.mk_implies(t, x);
        let result = simplifier.simplify(imp, &mut manager);
        assert_eq!(result, x);
    }

    #[test]
    fn test_simplify_ite() {
        let mut manager = TermManager::new();
        let mut simplifier = Simplifier::new();

        let x = manager.mk_var("x", manager.sorts.bool_sort);
        let y = manager.mk_var("y", manager.sorts.bool_sort);
        let t = manager.mk_true();
        let f = manager.mk_false();

        // ite(true, x, y) => x
        let ite = manager.mk_ite(t, x, y);
        let result = simplifier.simplify(ite, &mut manager);
        assert_eq!(result, x);

        // ite(false, x, y) => y
        let ite = manager.mk_ite(f, x, y);
        let result = simplifier.simplify(ite, &mut manager);
        assert_eq!(result, y);

        // ite(cond, x, x) => x
        let ite = manager.mk_ite(x, y, y);
        let result = simplifier.simplify(ite, &mut manager);
        assert_eq!(result, y);
    }

    #[test]
    fn test_simplify_eq() {
        let mut manager = TermManager::new();
        let mut simplifier = Simplifier::new();

        let x = manager.mk_var("x", manager.sorts.bool_sort);
        let t = manager.mk_true();
        let f = manager.mk_false();

        // x = x  =>  true
        let eq = manager.mk_eq(x, x);
        let result = simplifier.simplify(eq, &mut manager);
        assert!(matches!(
            manager.get(result).expect("key should exist in map").kind,
            TermKind::True
        ));

        // true = false  =>  false
        let eq = manager.mk_eq(t, f);
        let result = simplifier.simplify(eq, &mut manager);
        assert!(matches!(
            manager.get(result).expect("key should exist in map").kind,
            TermKind::False
        ));
    }

    #[test]
    fn test_simplify_assertions() {
        let mut manager = TermManager::new();
        let mut simplifier = Simplifier::new();

        let x = manager.mk_var("x", manager.sorts.bool_sort);
        let t = manager.mk_true();
        let f = manager.mk_false();

        // Simplify a list of assertions
        let assertions = vec![manager.mk_and([x, t]), manager.mk_or([x, f])];
        let (simplified, found_false) = simplifier.simplify_assertions(&assertions, &mut manager);

        assert!(!found_false);
        assert_eq!(simplified.len(), 2);
        assert_eq!(simplified[0], x); // and(x, true) => x
        assert_eq!(simplified[1], x); // or(x, false) => x

        // Test with a false assertion
        let assertions_with_false = vec![x, f];
        let (_, found_false) = simplifier.simplify_assertions(&assertions_with_false, &mut manager);
        assert!(found_false);
    }

    #[test]
    fn test_simplifier_reset() {
        let mut manager = TermManager::new();
        let mut simplifier = Simplifier::new();

        let x = manager.mk_var("x", manager.sorts.bool_sort);
        let y = manager.mk_var("y", manager.sorts.bool_sort);

        // Perform a simplification to populate the cache
        let eq = manager.mk_eq(x, x);
        let result1 = simplifier.simplify(eq, &mut manager);
        assert!(matches!(
            manager.get(result1).expect("key should exist in map").kind,
            TermKind::True
        ));

        // Create another term that would be cached
        let eq2 = manager.mk_eq(y, y);
        let result2 = simplifier.simplify(eq2, &mut manager);
        assert!(matches!(
            manager.get(result2).expect("key should exist in map").kind,
            TermKind::True
        ));

        // Reset the simplifier
        simplifier.reset();

        // Verify stats are cleared
        let stats_after_reset = simplifier.stats();
        assert_eq!(stats_after_reset.const_propagations, 0);
        assert_eq!(stats_after_reset.terms_eliminated, 0);
        assert_eq!(stats_after_reset.trivial_equalities, 0);
        assert_eq!(stats_after_reset.contradictions_found, 0);
    }

    /// `simplify` used to recurse once per nesting level. Returning at all is
    /// the assertion (a stack overflow aborts the process).
    #[test]
    fn simplify_survives_a_deep_negation_chain_on_a_small_stack() {
        // Stack and depth scale together (1 MiB/100k -> 128 KiB/12.5k): the
        // ~10 B-per-frame threshold is the pin, so never raise one alone.
        const DEPTH: usize = 12_500;

        let handle = std::thread::Builder::new()
            .stack_size(1 << 17)
            .spawn(|| {
                let mut manager = TermManager::new();
                let mut simplifier = Simplifier::new();

                let mut term = manager.mk_var("p", manager.sorts.bool_sort);
                for _ in 0..DEPTH {
                    term = manager.mk_not(term);
                }

                let result = simplifier.simplify(term, &mut manager);
                manager.get(result).is_some()
            })
            .expect("spawning the worker thread should succeed");

        assert!(handle.join().expect("the walk must not overflow"));
    }

    /// The same, through the n-ary conjunction path (which also drives the
    /// flattening rules).
    #[test]
    fn simplify_survives_a_deep_conjunction_nest_on_a_small_stack() {
        // Stack and depth scale together (1 MiB/50k -> 128 KiB/6.25k): the
        // ~21 B-per-frame threshold is the pin, so never raise one alone.
        const DEPTH: usize = 6_250;

        let handle = std::thread::Builder::new()
            .stack_size(1 << 17)
            .spawn(|| {
                let mut manager = TermManager::new();
                let mut simplifier = Simplifier::new();

                // `mk_and` flattens nested conjunctions, so alternate the
                // connective to actually build depth rather than width.
                let leaf = manager.mk_var("q", manager.sorts.bool_sort);
                let mut term = manager.mk_var("p", manager.sorts.bool_sort);
                for level in 0..DEPTH {
                    term = if level % 2 == 0 {
                        manager.mk_and([term, leaf])
                    } else {
                        manager.mk_or([term, leaf])
                    };
                }

                let result = simplifier.simplify(term, &mut manager);
                manager.get(result).is_some()
            })
            .expect("spawning the worker thread should succeed");

        assert!(handle.join().expect("the walk must not overflow"));
    }

    /// `unit_propagation` walks the same shapes through `substitute_units`.
    #[test]
    fn unit_propagation_survives_a_deep_negation_chain_on_a_small_stack() {
        // Stack and depth scale together (1 MiB/100k -> 128 KiB/12.5k): the
        // ~10 B-per-frame threshold is the pin, so never raise one alone.
        const DEPTH: usize = 12_500;

        let handle = std::thread::Builder::new()
            .stack_size(1 << 17)
            .spawn(|| {
                let mut manager = TermManager::new();
                let mut simplifier = Simplifier::new();

                let p = manager.mk_var("p", manager.sorts.bool_sort);
                let mut term = p;
                for _ in 0..DEPTH {
                    term = manager.mk_not(term);
                }

                let not_p = manager.mk_not(p);
                let results = simplifier.unit_propagation(&[not_p, term], &mut manager);
                results.len()
            })
            .expect("spawning the worker thread should succeed");

        assert_eq!(handle.join().expect("the walk must not overflow"), 2);
    }

    /// `detect_pure_literals` walks the formula with no memo of its own; the
    /// visited set must collapse a doubling DAG or this never finishes.
    #[test]
    fn detect_pure_literals_collapses_a_shared_dag() {
        let mut manager = TermManager::new();
        let simplifier = Simplifier::new();

        // Alternate the connective: `mk_and`/`mk_or` flatten a nested node of
        // their own kind, which would build width instead of a shared DAG.
        let mut term = manager.mk_var("p", manager.sorts.bool_sort);
        for level in 0..55 {
            term = if level % 2 == 0 {
                manager.mk_and([term, term])
            } else {
                manager.mk_or([term, term])
            };
        }

        let pure = simplifier.detect_pure_literals(&[term], &manager);
        assert_eq!(pure.len(), 1);
    }

    /// Semantic pin: a `not(not(x))` chain of even length simplifies back to
    /// the variable, of odd length to its negation.
    #[test]
    fn simplify_double_negation_pins() {
        let mut manager = TermManager::new();
        let mut simplifier = Simplifier::new();

        let p = manager.mk_var("p", manager.sorts.bool_sort);
        let not_p = manager.mk_not(p);

        let mut even = p;
        for _ in 0..8 {
            even = manager.mk_not(even);
        }
        assert_eq!(simplifier.simplify(even, &mut manager), p);

        let mut odd = p;
        for _ in 0..9 {
            odd = manager.mk_not(odd);
        }
        assert_eq!(simplifier.simplify(odd, &mut manager), not_p);
    }

    /// Semantic pin: contradiction detection still short-circuits a large
    /// conjunction, and flattening still merges nested conjunctions.
    #[test]
    fn simplify_conjunction_pins() {
        let mut manager = TermManager::new();
        let mut simplifier = Simplifier::new();

        let p = manager.mk_var("p", manager.sorts.bool_sort);
        let q = manager.mk_var("q", manager.sorts.bool_sort);
        let not_p = manager.mk_not(p);

        let contradiction = manager.mk_and([p, q, not_p]);
        let simplified = simplifier.simplify(contradiction, &mut manager);
        assert!(matches!(
            manager
                .get(simplified)
                .expect("simplified term exists")
                .kind,
            TermKind::False
        ));

        let inner = manager.mk_and([p, q]);
        let outer = manager.mk_and([inner, q]);
        let flattened = simplifier.simplify(outer, &mut manager);
        let expected = manager.mk_and([p, q]);
        assert_eq!(flattened, expected);
    }

    /// Semantic pin: unit propagation replaces the assigned literal and
    /// leaves everything else alone.
    #[test]
    fn unit_propagation_substitutes_only_assigned_literals() {
        let mut manager = TermManager::new();
        let mut simplifier = Simplifier::new();

        let p = manager.mk_var("p", manager.sorts.bool_sort);
        let q = manager.mk_var("q", manager.sorts.bool_sort);
        let not_p = manager.mk_not(p);
        let clause = manager.mk_or([p, q]);

        let results = simplifier.unit_propagation(&[not_p, clause], &mut manager);
        assert_eq!(results.len(), 2);

        let false_term = manager.mk_false();
        let expected = manager.mk_or([false_term, q]);
        assert_eq!(results[1], expected);
    }
}
