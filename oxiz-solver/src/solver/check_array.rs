//! Array theory constraint checking
//!
//! The two ground evaluators the checks below lean on live in their own
//! submodules, because both walk *input-shaped* term structure and both are
//! written as explicit heap frame stacks rather than as native recursion:
//!
//! * [`eval_bv`] — bit-vector expressions, for the cross-theory select check.
//! * [`eval_int`] — integer expressions modulo read-over-write, for the
//!   ordering check.

#[allow(unused_imports)]
use crate::prelude::*;
use oxiz_core::ast::{TermId, TermKind, TermManager};

use super::Solver;

mod eval_bv;
mod eval_int;

#[cfg(test)]
mod tests;

impl Solver {
    pub(super) fn check_array_constraints(&self, manager: &TermManager) -> bool {
        // Collect select constraints: (select a i) = v
        let mut select_values: FxHashMap<(TermId, TermId), TermId> = FxHashMap::default();
        // Collect store-select patterns: (select (store a i v) i)
        let mut store_select_same_index: Vec<(TermId, TermId, TermId, TermId)> = Vec::new(); // (array, index, stored_val, result)
        // Collect array equalities: a = b
        let mut array_equalities: Vec<(TermId, TermId)> = Vec::new();
        // Collect all select assertions: (select_term, asserted_value)
        let mut select_assertions: Vec<(TermId, TermId)> = Vec::new();
        // Collect negated select assertions: not(= (select ...) val) -> (select_term, val)
        let mut negated_select_assertions: Vec<(TermId, TermId)> = Vec::new();
        // Collect read-consistency conflicts detected during collection
        let mut read_conflicts: Vec<(TermId, TermId)> = Vec::new();

        // Collect array variable aliases: array_var → store_term
        // For assertions of the form (= B (store A i v)), maps B → the store term.
        // This allows select(B, i) to be resolved via the read-over-write axiom.
        let array_var_aliases = self.collect_array_var_aliases(manager);

        self.collect_array_constraints(
            manager,
            &mut select_values,
            &mut store_select_same_index,
            &mut array_equalities,
            &mut select_assertions,
            &mut negated_select_assertions,
            &mut read_conflicts,
        );

        // Resolve alias-based conflicts:
        // For each select_assertion (select_term, asserted_value) where the array in
        // select_term is an alias for a store, also check the aliased version.
        let mut alias_select_assertions: Vec<(TermId, TermId)> = Vec::new();
        for &(select_term, asserted_value) in &select_assertions {
            if let Some(resolved) =
                self.resolve_select_through_alias(select_term, &array_var_aliases, manager)
            {
                alias_select_assertions.push((resolved, asserted_value));
            }
        }
        select_assertions.extend(alias_select_assertions);

        // Similarly resolve negated select assertions through aliases.
        let mut alias_negated: Vec<(TermId, TermId)> = Vec::new();
        for &(select_term, negated_val) in &negated_select_assertions {
            if let Some(resolved) =
                self.resolve_select_through_alias(select_term, &array_var_aliases, manager)
            {
                alias_negated.push((resolved, negated_val));
            }
        }
        negated_select_assertions.extend(alias_negated);

        // Also inject alias-aware values into select_values so BV cross-theory checks work.
        // When (= val (select B i)) and B aliases store(A, i, v), we can infer val = v.
        self.inject_alias_select_values(&array_var_aliases, &mut select_values, manager);

        // Check: Alias-derived BV ordering conflicts.
        // When (= val (select B i)), B aliases (store A i w), we infer val = w.
        // If BV ordering constraints on val are inconsistent with val = w, detect UNSAT.
        if !array_var_aliases.is_empty()
            && self.check_alias_bv_ordering_conflict(&array_var_aliases, manager)
        {
            return true;
        }

        // Check: Integer ordering conflicts implied by read-over-write.
        // This covers ALIA cases where a store forces a concrete select value
        // that is then used under <, <=, >, >= constraints.
        if self.check_int_ordering_conflict(&array_var_aliases, manager) {
            return true;
        }

        // Check: Read-consistency conflicts (same array, same index, different values)
        for &(existing_val, new_val) in &read_conflicts {
            if self.are_different_values(existing_val, new_val, manager) {
                return true; // Conflict: (select a i) = v1 and (select a i) = v2 with v1 != v2
            }
        }

        // Check: Read-over-write with same index (array_03)
        // The axiom says: select(store(a, i, v), i) = v
        // So if we have assertion (= (select (store a i stored_val) i) result)
        // Then result MUST equal stored_val. If they're different, it's UNSAT.
        for &(_array, _index, stored_val, result) in &store_select_same_index {
            if result != stored_val {
                // Check if they're actually different concrete values
                if self.are_different_values(stored_val, result, manager) {
                    return true; // Conflict: axiom says result should be stored_val
                }
            }
        }

        // Check: Nested array read-over-write (array_08)
        // For each select assertion (select X i) = v, recursively evaluate X
        // to see if it simplifies via the axiom to a different value.
        // We also apply alias-aware evaluation to handle the pattern:
        //   (= B (store A i w))  +  (= (select B i) v)  where v ≠ w → UNSAT
        for &(select_term, asserted_value) in &select_assertions {
            // Standard evaluation (handles direct store terms in the array position).
            if let Some(evaluated_value) = self.evaluate_select_axiom(select_term, manager) {
                if evaluated_value != asserted_value
                    && self.are_different_values(evaluated_value, asserted_value, manager)
                {
                    return true; // Conflict: axiom says it should be evaluated_value
                }
            }
            // Alias-aware evaluation (handles array variables aliased to store terms).
            if !array_var_aliases.is_empty() {
                if let Some(evaluated_value) =
                    self.evaluate_select_axiom_with_alias(select_term, &array_var_aliases, manager)
                {
                    if evaluated_value != asserted_value
                        && self.are_different_values(evaluated_value, asserted_value, manager)
                    {
                        return true;
                    }
                }
            }
        }

        // Check: Negated store-select axiom enforcement
        // For each not(= (select X i) val), if the read-over-write axiom implies
        // select(X, i) = axiom_val, and axiom_val equals negated_val (directly or via positive
        // equalities), then we have a direct contradiction.
        // This handles two cases:
        //   1. Direct: not(= (select (store a 3 5) 3) 5) → axiom gives 5, negated is 5 → UNSAT
        //   2. Indirect: not(= (select (store a i v) i) 42) with (= v 42) → axiom gives v,
        //      v is constrained to 42 by positive assertion → UNSAT
        for &(select_term, negated_val) in &negated_select_assertions {
            // Standard evaluation.
            if let Some(axiom_val) = self.evaluate_select_axiom(select_term, manager) {
                if axiom_val == negated_val
                    || self.values_equal_concrete(axiom_val, negated_val, manager)
                    || self.is_value_constrained_to(axiom_val, negated_val, manager, &select_values)
                {
                    return true; // Contradiction: axiom forces this value, assertion denies it
                }
            }
            // Alias-aware evaluation.
            if !array_var_aliases.is_empty() {
                if let Some(axiom_val) =
                    self.evaluate_select_axiom_with_alias(select_term, &array_var_aliases, manager)
                {
                    if axiom_val == negated_val
                        || self.values_equal_concrete(axiom_val, negated_val, manager)
                        || self.is_value_constrained_to(
                            axiom_val,
                            negated_val,
                            manager,
                            &select_values,
                        )
                    {
                        return true;
                    }
                }
            }
            // Also check via direct store-select (one level, without recursive evaluation)
            if let Some(stored_val) = self.get_store_select_same_index_value(select_term, manager) {
                if stored_val == negated_val
                    || self.values_equal_concrete(stored_val, negated_val, manager)
                    || self.is_value_constrained_to(
                        stored_val,
                        negated_val,
                        manager,
                        &select_values,
                    )
                {
                    return true; // Contradiction: direct store axiom value matches negated value
                }
            }
        }

        // Check: Extensionality (array_06)
        // If a = b, then (select a i) = (select b i) for all i
        for &(array_a, array_b) in &array_equalities {
            // Check if there's a constraint that says select(a, i) != select(b, i) for some i
            for (&(sel_array, sel_index), &sel_val) in &select_values {
                if sel_array == array_a {
                    // Look for select(b, same_index) with different value
                    if let Some(&other_val) = select_values.get(&(array_b, sel_index)) {
                        if sel_val != other_val {
                            // Check if they're different literals
                            if self.are_different_values(sel_val, other_val, manager) {
                                return true;
                            }
                        }
                    }
                }
            }
            // Check for not(= (select a i) (select b i)) assertions
            for &assertion in &self.assertions {
                if self.is_select_inequality_assertion(assertion, array_a, array_b, manager) {
                    return true;
                }
            }
        }

        // Check: Store–store extensionality conflicts.
        // For a positive equality between two store terms, e.g.
        //   (= (store a i 1) (store b i 2))
        // extensionality requires select(lhs, k) = select(rhs, k) for every k.
        // Reading both sides at each store index via the read-over-write axiom
        // exposes a direct contradiction when the forced values differ (here at
        // index i: 1 ≠ 2 → UNSAT).  This is the sound conflict half of the array
        // honesty story; the SAT-side honesty gate lives in
        // `array_atoms_need_theory` (consulted by the Context layer), because the
        // EUF congruence core alone can place two store terms in one class
        // WITHOUT enforcing element-wise agreement — a source of spurious `Sat`.
        for &(x, y) in &self.collect_positive_array_term_equalities(manager) {
            if self.store_extensionality_conflict(x, y, manager) {
                return true;
            }
        }

        // Check: Cross-theory conflict (QF_ABV with variable equalities + BV arithmetic)
        // Example: x=#x05, select(a,x)=bvadd(x,#x01), select(a,#x05)=#x10
        // select(a,x) evaluates via x=5 to select(a,5)=6, but select(a,5)=16 → conflict
        {
            let var_equalities = self.collect_bv_var_equalities(manager);
            if !var_equalities.is_empty() {
                if self.check_cross_theory_conflict(&select_values, &var_equalities, manager) {
                    return true;
                }
            }
        }

        false
    }

    /// Evaluate a select term by repeatedly applying the read-over-write axiom
    /// select(store(a, i, v), i) = v
    /// Returns Some(value) if the select can be evaluated to a concrete value
    ///
    /// The axiom is applied to a fixpoint by a loop rather than by recursion.
    /// The recursive shape was `evaluate(stored_val).unwrap_or(stored_val)`,
    /// i.e. "keep rewriting while the axiom applies, and keep the last value
    /// that it did apply to", which is what `resolved` records here.
    fn evaluate_select_axiom(&self, term: TermId, manager: &TermManager) -> Option<TermId> {
        let mut current = term;
        let mut resolved: Option<TermId> = None;
        loop {
            let Some(term_data) = manager.get(current) else {
                return resolved;
            };
            let TermKind::Select(array, index) = &term_data.kind else {
                return resolved;
            };

            // The array position may itself need read-over-write simplification
            // first; failing that, the original array may already be a store.
            let simplified_array = self.simplify_array_term(*array, manager);
            let stored = [simplified_array, *array]
                .into_iter()
                .find_map(|candidate| {
                    let TermKind::Store(_base, store_idx, stored_val) =
                        &manager.get(candidate)?.kind
                    else {
                        return None;
                    };
                    self.terms_equal_simple(*store_idx, *index, manager)
                        .then_some(*stored_val)
                });

            let Some(stored_val) = stored else {
                return resolved;
            };
            resolved = Some(stored_val);
            current = stored_val;
        }
    }

    /// Simplify an array term by applying the read-over-write axiom
    /// If the term is select(store(a, i, v), i), return v
    ///
    /// The rewrite is applied to a fixpoint by a loop rather than by tail
    /// recursion: the `select`/`store` nesting is input-controlled and this
    /// runs on whatever stack `check_sat`'s caller has.
    fn simplify_array_term(&self, term: TermId, manager: &TermManager) -> TermId {
        let mut current = term;
        loop {
            let Some(term_data) = manager.get(current) else {
                return current;
            };

            let TermKind::Select(array, index) = &term_data.kind else {
                return current;
            };
            // Check if array is a store with the same index
            let Some(array_data) = manager.get(*array) else {
                return current;
            };
            let TermKind::Store(_base, store_idx, stored_val) = &array_data.kind else {
                return current;
            };
            if !self.terms_equal_simple(*store_idx, *index, manager) {
                return current;
            }
            // select(store(a, i, v), i) = v, then keep simplifying the result.
            current = *stored_val;
        }
    }

    /// Check if two terms represent different concrete values
    fn are_different_values(&self, a: TermId, b: TermId, manager: &TermManager) -> bool {
        if a == b {
            return false;
        }
        let (Some(a_data), Some(b_data)) = (manager.get(a), manager.get(b)) else {
            return false;
        };
        match (&a_data.kind, &b_data.kind) {
            (TermKind::IntConst(s1), TermKind::IntConst(s2)) => s1 != s2,
            (
                TermKind::BitVecConst {
                    value: v1,
                    width: w1,
                },
                TermKind::BitVecConst {
                    value: v2,
                    width: w2,
                },
            ) => w1 == w2 && v1 != v2,
            (TermKind::RealConst(r1), TermKind::RealConst(r2)) => r1 != r2,
            _ => false,
        }
    }

    /// Collect array constraints from the sub-terms of every assertion that are
    /// **unconditionally asserted**, carrying the polarity of each.
    ///
    /// The walk is an explicit heap worklist rather than recursion: it runs on
    /// whatever stack `check_sat`'s caller has, and an assertion's nesting
    /// depth is attacker-controlled, so one native frame per level is a process
    /// abort waiting to happen.  Children are pushed in reverse so they pop
    /// left to right — the recursive order, which matters because
    /// `select_values` is `insert`ed into and the *first* write for an
    /// `(array, index)` pair wins (a later one becomes a read conflict
    /// instead).
    ///
    /// Each worklist entry carries two flags, both of which the recursive
    /// version passed down:
    ///
    /// * `in_positive_context` — whether an odd number of `Not`s has been
    ///   crossed.  Only [`super::term_walk::asserted_children`] decides which
    ///   children inherit assertedness, and at which polarity; in particular an
    ///   `And` hands out its conjuncts only at *positive* polarity, because
    ///   `(not (and a b))` is `(or (not a) (not b))` and entails neither.
    /// * `collect_facts` — whether the term's own truth value is asserted at
    ///   all.  It is `false` for the operands of an equality: `(= a b)` asserts
    ///   only that `a` and `b` are *equal*, NOT that either holds on its own,
    ///   so a nested Boolean equality such as
    ///   `(= p (= (select (store a 3 5) 3) 6))` must not yield an asserted
    ///   read-over-write fact — doing so produced a spurious UNSAT for a
    ///   formula that is SAT with `p = false`.  An entry with `collect_facts`
    ///   clear is dropped immediately, exactly as the recursive version
    ///   returned at once; the flag is kept rather than folded away so the
    ///   equality arm's descent stays visible where the reasoning for it is.
    ///
    /// Re-visits are pruned by a set keyed on `(TermId, polarity)` — NOT on
    /// `TermId` alone, because on a shared-subterm DAG the same term is
    /// reachable under both polarities and each polarity yields different
    /// facts (dropping the second visit lost the negated-select fact).  Two
    /// visits at the *same* polarity, though, are exact duplicates: what a
    /// fact-collecting visit does is a function of `(term, polarity)` only, so
    /// a repeat could only append copies of facts already recorded — and
    /// `select_values` keeps the first write for a key, so a repeat cannot
    /// even manufacture a spurious read conflict against itself.  Without the
    /// set, a ladder like `(and x (not (not x)))` — buildable with shared
    /// `let` bindings — walks `x` once per *path*, which doubles per level:
    /// sixty levels of linear-size input became 2⁶⁰ visits and `check_sat`
    /// never returned.  Entries with `collect_facts` clear bypass the set
    /// entirely: they do nothing when popped, and letting one mark its term
    /// visited would suppress a later fact-collecting visit of the same node.
    fn collect_array_constraints(
        &self,
        manager: &TermManager,
        select_values: &mut FxHashMap<(TermId, TermId), TermId>,
        store_select_same_index: &mut Vec<(TermId, TermId, TermId, TermId)>,
        array_equalities: &mut Vec<(TermId, TermId)>,
        select_assertions: &mut Vec<(TermId, TermId)>,
        negated_select_assertions: &mut Vec<(TermId, TermId)>,
        read_conflicts: &mut Vec<(TermId, TermId)>,
    ) {
        // `(term, in_positive_context, collect_facts)`, with the first
        // assertion on top so assertions are visited left to right.
        let mut worklist: Vec<(TermId, bool, bool)> = self
            .assertions
            .iter()
            .rev()
            .map(|&assertion| (assertion, true, true))
            .collect();
        let mut visited: FxHashSet<(TermId, bool)> = FxHashSet::default();

        while let Some((term, in_positive_context, collect_facts)) = worklist.pop() {
            // Inside an equality operand nothing is individually asserted, so we
            // must not collect any read-over-write / extensionality facts from this
            // subtree.  Descending further could only reinterpret non-asserted
            // Boolean structure (nested Eq/And/Not) as asserted, which is unsound.
            if !collect_facts {
                continue;
            }

            // A repeat at the same polarity is an exact duplicate — see the
            // doc comment for why the polarity must be part of the key.
            if !visited.insert((term, in_positive_context)) {
                continue;
            }

            let Some(term_data) = manager.get(term) else {
                continue;
            };

            match &term_data.kind {
                TermKind::Eq(lhs, rhs) => {
                    // Only check for array equality when in positive context (not inside a Not)
                    // Array equality like (= a b) only means a equals b when it's asserted directly,
                    // not when it's negated as (not (= a b))
                    if in_positive_context {
                        if self.is_array_variable(*lhs, manager)
                            && self.is_array_variable(*rhs, manager)
                        {
                            array_equalities.push((*lhs, *rhs));
                        }
                    }

                    // Check for (select a i) = v — only in positive context
                    if in_positive_context {
                        if let Some((array, index)) = self.extract_select(*lhs, manager) {
                            if let Some(&existing_val) = select_values.get(&(array, index)) {
                                if existing_val != *rhs {
                                    read_conflicts.push((existing_val, *rhs));
                                }
                            } else {
                                select_values.insert((array, index), *rhs);
                            }
                            // Also record for nested array evaluation (array_08)
                            select_assertions.push((*lhs, *rhs));
                        }
                        if let Some((array, index)) = self.extract_select(*rhs, manager) {
                            if let Some(&existing_val) = select_values.get(&(array, index)) {
                                if existing_val != *lhs {
                                    read_conflicts.push((existing_val, *lhs));
                                }
                            } else {
                                select_values.insert((array, index), *lhs);
                            }
                            // Also record for nested array evaluation (array_08)
                            select_assertions.push((*rhs, *lhs));
                        }

                        // Check for (select (store a i v) i) = result
                        if let Some((inner_array, outer_index)) = self.extract_select(*lhs, manager)
                        {
                            if let Some((base_array, store_index, stored_val)) =
                                self.extract_store(inner_array, manager)
                            {
                                // Check if indices are the same
                                if self.terms_equal_simple(outer_index, store_index, manager) {
                                    store_select_same_index.push((
                                        base_array,
                                        store_index,
                                        stored_val,
                                        *rhs,
                                    ));
                                }
                            }
                        }
                        if let Some((inner_array, outer_index)) = self.extract_select(*rhs, manager)
                        {
                            if let Some((base_array, store_index, stored_val)) =
                                self.extract_store(inner_array, manager)
                            {
                                if self.terms_equal_simple(outer_index, store_index, manager) {
                                    store_select_same_index.push((
                                        base_array,
                                        store_index,
                                        stored_val,
                                        *lhs,
                                    ));
                                }
                            }
                        }
                    } else {
                        // Negative context: we are inside a not(= ...) expression.
                        // Collect negated select assertions: not(= (select array idx) val)
                        // These mean the assertion claims select(array, idx) != val.
                        // If the store-select axiom forces select(array, idx) = val, contradiction.
                        if self.extract_select(*lhs, manager).is_some() {
                            negated_select_assertions.push((*lhs, *rhs));
                        }
                        if self.extract_select(*rhs, manager).is_some() {
                            negated_select_assertions.push((*rhs, *lhs));
                        }
                    }

                    // Descend into the operands with `collect_facts = false`:
                    // an equality's operands are not individually asserted, so
                    // any Boolean structure inside them (a nested Eq/And/Not)
                    // must not be treated as an asserted read-over-write fact.
                    // The asserted equality itself has already been recorded
                    // above.  Pushed left operand last so it pops first.
                    worklist.push((*rhs, in_positive_context, false));
                    worklist.push((*lhs, in_positive_context, false));
                }
                // `And` / `Or` / `Not` are the only nodes that carry unconditional
                // assertedness downwards.  Which children qualify depends on the
                // polarity, and `asserted_children` is the single place that rule
                // lives: an `And` hands out its conjuncts only at *positive*
                // polarity, because `(not (and a b))` is `(or (not a) (not b))` and
                // entails neither conjunct.  Passing `in_positive_context` straight
                // through here previously refuted the satisfiable
                // `(not (and (= (select (store a 3 5) 3) 5) p))`.
                TermKind::And(_) | TermKind::Or(_) | TermKind::Not(_) => {
                    let children =
                        super::term_walk::asserted_children(&term_data.kind, in_positive_context);
                    worklist.extend(
                        children
                            .into_iter()
                            .rev()
                            .map(|(child, child_positive)| (child, child_positive, collect_facts)),
                    );
                }
                _ => {}
            }
        }
    }

    /// Check if term is an array variable
    fn is_array_variable(&self, term: TermId, manager: &TermManager) -> bool {
        let Some(term_data) = manager.get(term) else {
            return false;
        };
        if let TermKind::Var(_) = &term_data.kind {
            // Check if the sort is an array sort
            if let Some(sort) = manager.sorts.get(term_data.sort) {
                return matches!(sort.kind, oxiz_core::SortKind::Array { .. });
            }
        }
        false
    }

    /// Extract (select array index) pattern
    fn extract_select(&self, term: TermId, manager: &TermManager) -> Option<(TermId, TermId)> {
        let term_data = manager.get(term)?;
        if let TermKind::Select(array, index) = &term_data.kind {
            Some((*array, *index))
        } else {
            None
        }
    }

    /// Extract (store array index value) pattern
    fn extract_store(
        &self,
        term: TermId,
        manager: &TermManager,
    ) -> Option<(TermId, TermId, TermId)> {
        let term_data = manager.get(term)?;
        if let TermKind::Store(array, index, value) = &term_data.kind {
            Some((*array, *index, *value))
        } else {
            None
        }
    }

    /// Check if two terms are structurally equal (simple comparison)
    fn terms_equal_simple(&self, a: TermId, b: TermId, manager: &TermManager) -> bool {
        if a == b {
            return true;
        }
        let (Some(a_data), Some(b_data)) = (manager.get(a), manager.get(b)) else {
            return false;
        };
        match (&a_data.kind, &b_data.kind) {
            (TermKind::IntConst(s1), TermKind::IntConst(s2)) => s1 == s2,
            _ => false,
        }
    }

    /// Check if assertion says (= term1 term2)
    #[allow(dead_code)]
    fn asserts_equality(
        &self,
        assertion: TermId,
        term1: TermId,
        term2: TermId,
        manager: &TermManager,
    ) -> bool {
        let Some(assertion_data) = manager.get(assertion) else {
            return false;
        };
        if let TermKind::Eq(lhs, rhs) = &assertion_data.kind {
            (*lhs == term1 && *rhs == term2) || (*lhs == term2 && *rhs == term1)
        } else {
            false
        }
    }

    /// Check if two terms represent equal concrete values (both are concrete literals with same value).
    /// Unlike `are_different_values`, this returns true when the values are provably equal.
    fn values_equal_concrete(&self, a: TermId, b: TermId, manager: &TermManager) -> bool {
        if a == b {
            return true;
        }
        let (Some(a_data), Some(b_data)) = (manager.get(a), manager.get(b)) else {
            return false;
        };
        match (&a_data.kind, &b_data.kind) {
            (TermKind::IntConst(s1), TermKind::IntConst(s2)) => s1 == s2,
            (
                TermKind::BitVecConst {
                    value: v1,
                    width: w1,
                },
                TermKind::BitVecConst {
                    value: v2,
                    width: w2,
                },
            ) => w1 == w2 && v1 == v2,
            (TermKind::RealConst(r1), TermKind::RealConst(r2)) => r1 == r2,
            _ => false,
        }
    }

    /// For a select term `(select array index)`, if `array` is a store expression
    /// `(store base store_idx stored_val)` and `index == store_idx`, return `stored_val`.
    /// This directly applies the read-over-write axiom at one level.
    fn get_store_select_same_index_value(
        &self,
        select_term: TermId,
        manager: &TermManager,
    ) -> Option<TermId> {
        let term_data = manager.get(select_term)?;
        if let TermKind::Select(array, index) = &term_data.kind {
            let array_data = manager.get(*array)?;
            if let TermKind::Store(_base, store_idx, stored_val) = &array_data.kind {
                if self.terms_equal_simple(*store_idx, *index, manager) {
                    return Some(*stored_val);
                }
            }
        }
        None
    }

    /// Check if `value_term` is constrained by positive select-equality assertions to equal
    /// `target_val`. Used to detect cases where the stored variable is pinned to a concrete
    /// value that conflicts with a negated assertion.
    /// For example: `(= v 42)` asserted, and we want to know if `v` is constrained to equal 42.
    fn is_value_constrained_to(
        &self,
        value_term: TermId,
        target_val: TermId,
        manager: &TermManager,
        select_values: &FxHashMap<(TermId, TermId), TermId>,
    ) -> bool {
        // Direct identity check
        if value_term == target_val {
            return true;
        }
        if self.values_equal_concrete(value_term, target_val, manager) {
            return true;
        }

        // Check if there is a positive equality assertion (= value_term target_val)
        // by scanning the assertions for direct equalities.
        for &assertion in &self.assertions {
            let Some(assertion_data) = manager.get(assertion) else {
                continue;
            };
            if let TermKind::Eq(lhs, rhs) = &assertion_data.kind {
                // Check (= value_term target_val) or (= target_val value_term)
                if (*lhs == value_term && self.values_equal_concrete(*rhs, target_val, manager))
                    || (*rhs == value_term && self.values_equal_concrete(*lhs, target_val, manager))
                {
                    return true;
                }
                // Also check if value_term is bound to a select result that maps to target_val
                if *lhs == value_term {
                    if let Some((sel_array, sel_index)) = self.extract_select(*rhs, manager) {
                        if let Some(&mapped_val) = select_values.get(&(sel_array, sel_index)) {
                            if self.values_equal_concrete(mapped_val, target_val, manager) {
                                return true;
                            }
                        }
                    }
                }
                if *rhs == value_term {
                    if let Some((sel_array, sel_index)) = self.extract_select(*lhs, manager) {
                        if let Some(&mapped_val) = select_values.get(&(sel_array, sel_index)) {
                            if self.values_equal_concrete(mapped_val, target_val, manager) {
                                return true;
                            }
                        }
                    }
                }
            }
        }
        false
    }

    /// Collect BV variable-to-constant equalities from assertions.
    /// For each assertion of the form `(= Var BitVecConst)` or `(= BitVecConst Var)`,
    /// record the mapping from the variable TermId to (concrete_value, width).
    fn collect_bv_var_equalities(
        &self,
        manager: &TermManager,
    ) -> FxHashMap<TermId, (num_bigint::BigInt, u32)> {
        let mut result: FxHashMap<TermId, (num_bigint::BigInt, u32)> = FxHashMap::default();
        for &assertion in &self.assertions {
            let Some(data) = manager.get(assertion) else {
                continue;
            };
            if let TermKind::Eq(lhs, rhs) = &data.kind {
                self.try_record_var_const_eq(*lhs, *rhs, manager, &mut result);
                self.try_record_var_const_eq(*rhs, *lhs, manager, &mut result);
            }
        }
        result
    }

    /// If `var_term` is a Var and `val_term` is a BitVecConst, record the mapping.
    fn try_record_var_const_eq(
        &self,
        var_term: TermId,
        val_term: TermId,
        manager: &TermManager,
        result: &mut FxHashMap<TermId, (num_bigint::BigInt, u32)>,
    ) {
        let (Some(var_data), Some(val_data)) = (manager.get(var_term), manager.get(val_term))
        else {
            return;
        };
        if let TermKind::Var(_) = &var_data.kind {
            if let TermKind::BitVecConst { value, width } = &val_data.kind {
                result.insert(var_term, (value.clone(), *width));
            }
        }
    }

    /// Cross-theory conflict check: detect conflicts that require variable substitution.
    ///
    /// Given:
    ///   var_equalities:  x → (5, 8)      from `(= x #x05)`
    ///   select_values:   (a, x)   → bvadd(x, #x01)   from `(= (select a x) (bvadd x #x01))`
    ///                    (a, #x05) → #x10             from `(= (select a #x05) #x10)`
    ///
    /// After evaluating indices and values:
    ///   (a, x) index evaluates to 5, value bvadd(x,1) evaluates to 6
    ///   (a, #x05) index is 5, value #x10 is 16
    ///   Same index, different values → UNSAT
    fn check_cross_theory_conflict(
        &self,
        select_values: &FxHashMap<(TermId, TermId), TermId>,
        var_equalities: &FxHashMap<TermId, (num_bigint::BigInt, u32)>,
        manager: &TermManager,
    ) -> bool {
        use num_bigint::BigInt;

        // Build a list of (array_term, evaluated_index: (BigInt,u32), evaluated_value: (BigInt,u32))
        // for all select_values entries that can be fully evaluated.
        struct EvalEntry {
            array: TermId,
            index_val: (BigInt, u32),
            value_val: (BigInt, u32),
        }

        let mut evaluated: Vec<EvalEntry> = Vec::new();

        for (&(array, index_term), &value_term) in select_values {
            let Some(index_val) = self.evaluate_bv_expr(index_term, var_equalities, manager) else {
                continue;
            };
            let Some(value_val) = self.evaluate_bv_expr(value_term, var_equalities, manager) else {
                continue;
            };
            evaluated.push(EvalEntry {
                array,
                index_val,
                value_val,
            });
        }

        // Check all pairs with the same array and same evaluated index
        for i in 0..evaluated.len() {
            for j in (i + 1)..evaluated.len() {
                let ei = &evaluated[i];
                let ej = &evaluated[j];
                if ei.array != ej.array {
                    continue;
                }
                // Indices must have same width and value to be considered identical
                if ei.index_val != ej.index_val {
                    continue;
                }
                // Same array, same index → must have same value
                if ei.value_val != ej.value_val {
                    return true; // Conflict
                }
            }
        }

        false
    }

    /// Check if assertion says not(= (select a i) (select b i))
    fn is_select_inequality_assertion(
        &self,
        assertion: TermId,
        array_a: TermId,
        array_b: TermId,
        manager: &TermManager,
    ) -> bool {
        let Some(assertion_data) = manager.get(assertion) else {
            return false;
        };
        if let TermKind::Not(inner) = &assertion_data.kind {
            let Some(inner_data) = manager.get(*inner) else {
                return false;
            };
            if let TermKind::Eq(lhs, rhs) = &inner_data.kind {
                // Check if lhs is select(a, i) and rhs is select(b, i)
                if let (Some((sel_a, idx_a)), Some((sel_b, idx_b))) = (
                    self.extract_select(*lhs, manager),
                    self.extract_select(*rhs, manager),
                ) {
                    if ((sel_a == array_a && sel_b == array_b)
                        || (sel_a == array_b && sel_b == array_a))
                        && self.terms_equal_simple(idx_a, idx_b, manager)
                    {
                        return true;
                    }
                }
            }
        }
        false
    }

    // ──────────────────────────────────────────────────────────────────────────
    // Array variable alias resolution
    //
    // These methods handle the pattern:
    //   (declare-const B Array)
    //   (assert (= B (store A i v)))   ← B is an alias for the store term
    //   (assert (= (select B i) W))    ← select must resolve through B's alias
    // ──────────────────────────────────────────────────────────────────────────

    /// Collect array variable aliases from assertions.
    ///
    /// For each assertion `(= B (store A i v))` or `(= (store A i v) B)` where
    /// `B` is a variable with an array sort, record `B → store_term_id`.
    ///
    /// Multiple levels of aliasing (B → store1 → store2) are handled by a
    /// fixpoint iteration: at most `max_iters` passes to resolve chains.
    fn collect_array_var_aliases(&self, manager: &TermManager) -> FxHashMap<TermId, TermId> {
        let mut aliases: FxHashMap<TermId, TermId> = FxHashMap::default();

        for &assertion in &self.assertions {
            let Some(data) = manager.get(assertion) else {
                continue;
            };
            if let TermKind::Eq(lhs, rhs) = &data.kind {
                self.try_record_array_alias(*lhs, *rhs, manager, &mut aliases);
                self.try_record_array_alias(*rhs, *lhs, manager, &mut aliases);
            }
        }

        // Fixpoint: resolve transitive aliases (B → C, C → store(…) becomes B → store(…))
        let max_iters = 8;
        for _ in 0..max_iters {
            let mut changed = false;
            let keys: Vec<TermId> = aliases.keys().copied().collect();
            for key in keys {
                let target = aliases[&key];
                // If the alias target is itself aliased to a store, follow through.
                if let Some(&next_target) = aliases.get(&target) {
                    let target_data = manager.get(next_target);
                    if target_data.is_some_and(|d| matches!(d.kind, TermKind::Store(..))) {
                        aliases.insert(key, next_target);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }

        aliases
    }

    /// If `var_term` is an array variable and `store_term` is a Store expression,
    /// record `var_term → store_term` in `aliases`.
    fn try_record_array_alias(
        &self,
        var_term: TermId,
        store_term: TermId,
        manager: &TermManager,
        aliases: &mut FxHashMap<TermId, TermId>,
    ) {
        let (Some(var_data), Some(store_data)) = (manager.get(var_term), manager.get(store_term))
        else {
            return;
        };
        // LHS must be a variable (declared array constant).
        if !matches!(var_data.kind, TermKind::Var(_)) {
            return;
        }
        // RHS must be a Store expression.
        if !matches!(store_data.kind, TermKind::Store(..)) {
            return;
        }
        aliases.insert(var_term, store_term);
    }

    /// Given a select term `(select B i)`, check if `B` is in `array_var_aliases`.
    /// If so, return a *virtual* select term that uses the aliased store expression.
    ///
    /// Because we cannot create new TermIds here (no mutable manager), we instead
    /// return the *original select term* with its array replaced by the alias
    /// target if the alias target is a Store — but since we cannot mutate the
    /// term graph, we return a synthetic representation by returning the raw
    /// store term that would be the array operand.
    ///
    /// Concretely, we return `Some(virtual_select_id)` only when the resolved
    /// array is a `Store` and the select index matches the store index, letting
    /// the caller use `evaluate_select_axiom_with_alias` to get the stored value.
    fn resolve_select_through_alias(
        &self,
        select_term: TermId,
        aliases: &FxHashMap<TermId, TermId>,
        manager: &TermManager,
    ) -> Option<TermId> {
        let term_data = manager.get(select_term)?;
        let TermKind::Select(array, _index) = &term_data.kind else {
            return None;
        };
        // Only apply when the array is a Var that has an alias.
        let array_data = manager.get(*array)?;
        if !matches!(array_data.kind, TermKind::Var(_)) {
            return None;
        }
        aliases.get(array)?;
        // Return the select term unchanged — evaluate_select_axiom will resolve
        // it via the alias map passed through the wrapper.
        // (We signal "this needs alias resolution" by returning Some(select_term).)
        Some(select_term)
    }

    /// Evaluate a select term with awareness of array variable aliases.
    ///
    /// Like `evaluate_select_axiom`, but before checking if the array is a Store,
    /// first resolves the array through `aliases`.
    fn evaluate_select_axiom_with_alias(
        &self,
        select_term: TermId,
        aliases: &FxHashMap<TermId, TermId>,
        manager: &TermManager,
    ) -> Option<TermId> {
        let term_data = manager.get(select_term)?;
        let TermKind::Select(array, index) = &term_data.kind else {
            return None;
        };

        // Resolve the array through the alias map.
        let resolved_array = {
            let arr_data = manager.get(*array)?;
            if matches!(arr_data.kind, TermKind::Var(_)) {
                aliases.get(array).copied().unwrap_or(*array)
            } else {
                *array
            }
        };

        // Apply read-over-write axiom on the resolved array.
        let resolved_data = manager.get(resolved_array)?;
        if let TermKind::Store(_base, store_idx, stored_val) = &resolved_data.kind {
            if self.terms_equal_simple(*store_idx, *index, manager) {
                return Some(*stored_val);
            }
        }

        // Fall back to the standard evaluation (handles nested stores).
        self.evaluate_select_axiom(select_term, manager)
    }

    /// Inject alias-derived values into `select_values`.
    ///
    /// For every `(= val (select B i))` assertion where `B` is aliased to a
    /// store expression `(store A i v)`, we know `val = v` by the read-over-write
    /// axiom.  Add `(virtual_B_store, i) → v` and `(B_var, i) → v` into
    /// `select_values` so that downstream BV cross-theory checks (which use
    /// `select_values`) can detect contradictions involving `val`.
    ///
    /// We also directly check for UNSAT: if `(B_var, i)` already maps to a
    /// different concrete value than `v`, we detect a conflict.
    fn inject_alias_select_values(
        &self,
        aliases: &FxHashMap<TermId, TermId>,
        select_values: &mut FxHashMap<(TermId, TermId), TermId>,
        manager: &TermManager,
    ) {
        if aliases.is_empty() {
            return;
        }

        // Scan assertions for `(= val (select B i))` or `(= (select B i) val)`.
        for &assertion in &self.assertions {
            let Some(data) = manager.get(assertion) else {
                continue;
            };
            if let TermKind::Eq(lhs, rhs) = &data.kind {
                self.maybe_inject_alias_value(*lhs, *rhs, aliases, select_values, manager);
                self.maybe_inject_alias_value(*rhs, *lhs, aliases, select_values, manager);
            }
        }
    }

    /// Helper: if `select_term` is `(select B i)` and `B` aliases `(store A i v)`,
    /// record `(B, i) → v` and `(store_term, i) → v` in `select_values`.
    fn maybe_inject_alias_value(
        &self,
        select_term: TermId,
        _value_term: TermId,
        aliases: &FxHashMap<TermId, TermId>,
        select_values: &mut FxHashMap<(TermId, TermId), TermId>,
        manager: &TermManager,
    ) {
        let Some(data) = manager.get(select_term) else {
            return;
        };
        let TermKind::Select(array, index) = &data.kind else {
            return;
        };
        let Some(arr_data) = manager.get(*array) else {
            return;
        };
        if !matches!(arr_data.kind, TermKind::Var(_)) {
            return;
        }
        let Some(&store_term) = aliases.get(array) else {
            return;
        };
        let Some(store_data) = manager.get(store_term) else {
            return;
        };
        let TermKind::Store(_base, store_idx, stored_val) = &store_data.kind else {
            return;
        };
        if !self.terms_equal_simple(*store_idx, *index, manager) {
            return;
        }
        // `stored_val` is the value that the axiom forces at this index.
        // Record under the original array variable key so downstream checks
        // can look it up.
        select_values.entry((*array, *index)).or_insert(*stored_val);
    }

    // ──────────────────────────────────────────────────────────────────────────
    // Alias-derived BV ordering conflict detection
    //
    // Pattern:
    //   (= B (store A i w))           ← B aliases the store
    //   (= val (select B i))           ← val is bound to select(B, i) = w (by axiom)
    //   (bvugt val w)                  ← requires val > w, but val = w → UNSAT
    // ──────────────────────────────────────────────────────────────────────────

    /// Check for BV ordering conflicts that arise when a variable is derived
    /// from an alias-resolved array select.
    ///
    /// Specifically:
    /// 1. Build a map `derived_values: TermId → (BigInt, u32)` mapping scalar
    ///    variables to their concrete BV values implied by array axiom + aliases.
    /// 2. Scan BV ordering assertions (`bvugt`, `bvult`, `bvuge`, `bvule`) and
    ///    check if the derived value violates the ordering constraint.
    fn check_alias_bv_ordering_conflict(
        &self,
        aliases: &FxHashMap<TermId, TermId>,
        manager: &TermManager,
    ) -> bool {
        use num_bigint::BigInt;

        // Step 1: Build derived_values map.
        // For each assertion (= val (select B i)) where B aliases (store A i w)
        // and w is a concrete BV constant, record val → (w_value, width).
        let mut derived_values: FxHashMap<TermId, (BigInt, u32)> = FxHashMap::default();

        for &assertion in &self.assertions {
            let Some(data) = manager.get(assertion) else {
                continue;
            };
            if let TermKind::Eq(lhs, rhs) = &data.kind {
                self.try_derive_bv_from_alias_select(
                    *lhs,
                    *rhs,
                    aliases,
                    &mut derived_values,
                    manager,
                );
                self.try_derive_bv_from_alias_select(
                    *rhs,
                    *lhs,
                    aliases,
                    &mut derived_values,
                    manager,
                );
            }
        }

        if derived_values.is_empty() {
            return false;
        }

        // Step 2: Scan BV ordering assertions and check for conflicts.
        for &assertion in &self.assertions {
            let Some(data) = manager.get(assertion) else {
                continue;
            };
            if self.check_bv_ordering_against_derived(assertion, &derived_values, manager) {
                return true;
            }
            // Also check negated equalities: (not (= a b)) where a is derived and b is concrete.
            if let TermKind::Not(inner) = &data.kind {
                if let Some(inner_data) = manager.get(*inner) {
                    if let TermKind::Eq(lhs, rhs) = &inner_data.kind {
                        // not(= val concrete): val must be concrete by axiom but the negation says it isn't
                        if let Some((derived_val, dw)) = derived_values.get(lhs) {
                            if let Some(rhs_data) = manager.get(*rhs) {
                                if let TermKind::BitVecConst { value, width } = &rhs_data.kind {
                                    if *width == *dw && derived_val == value {
                                        return true;
                                    }
                                }
                            }
                        }
                        if let Some((derived_val, dw)) = derived_values.get(rhs) {
                            if let Some(lhs_data) = manager.get(*lhs) {
                                if let TermKind::BitVecConst { value, width } = &lhs_data.kind {
                                    if *width == *dw && derived_val == value {
                                        return true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        false
    }

    /// If `select_like` is `(select B i)` where `B` is in `aliases` and the stored
    /// value at index `i` is a concrete BV constant, and `scalar` is a Var,
    /// record `scalar → (stored_value, width)` in `derived_values`.
    fn try_derive_bv_from_alias_select(
        &self,
        scalar: TermId,
        select_like: TermId,
        aliases: &FxHashMap<TermId, TermId>,
        derived_values: &mut FxHashMap<TermId, (num_bigint::BigInt, u32)>,
        manager: &TermManager,
    ) {
        // `scalar` must be a Var (not a constant expression).
        let Some(scalar_data) = manager.get(scalar) else {
            return;
        };
        if !matches!(scalar_data.kind, TermKind::Var(_)) {
            return;
        }
        // `select_like` must be a Select.
        let Some(sel_data) = manager.get(select_like) else {
            return;
        };
        let TermKind::Select(array, index) = &sel_data.kind else {
            return;
        };
        // `array` must be a Var that is in the alias map.
        let Some(arr_data) = manager.get(*array) else {
            return;
        };
        if !matches!(arr_data.kind, TermKind::Var(_)) {
            return;
        }
        let Some(&store_term) = aliases.get(array) else {
            return;
        };
        let Some(store_data) = manager.get(store_term) else {
            return;
        };
        let TermKind::Store(_base, store_idx, stored_val) = &store_data.kind else {
            return;
        };
        // Indices must match.
        if !self.terms_equal_simple(*store_idx, *index, manager) {
            return;
        }
        // `stored_val` must be a concrete BV constant.
        let Some(stored_data) = manager.get(*stored_val) else {
            return;
        };
        if let TermKind::BitVecConst { value, width } = &stored_data.kind {
            derived_values.insert(scalar, (value.clone(), *width));
        }
    }

    /// Check whether a single BV ordering assertion conflicts with the given
    /// `derived_values` map.
    ///
    /// Handles: `bvugt`, `bvult`, `bvuge`, `bvule`, `bvsgt`, `bvslt`, `bvsge`,
    /// `bvsle`.  For each ordering assertion `(op a b)`, if one side is in
    /// `derived_values`, evaluate the constraint and return `true` if it is
    /// provably false.
    fn check_bv_ordering_against_derived(
        &self,
        assertion: TermId,
        derived_values: &FxHashMap<TermId, (num_bigint::BigInt, u32)>,
        manager: &TermManager,
    ) -> bool {
        use num_bigint::BigInt;
        use num_traits::One;

        let Some(data) = manager.get(assertion) else {
            return false;
        };

        // Helper: get concrete BV value for a term (either from derived_values or literal).
        let get_bv_val = |term: TermId| -> Option<(BigInt, u32)> {
            if let Some(v) = derived_values.get(&term) {
                return Some(v.clone());
            }
            let d = manager.get(term)?;
            if let TermKind::BitVecConst { value, width } = &d.kind {
                return Some((value.clone(), *width));
            }
            None
        };

        match &data.kind {
            TermKind::BvUlt(a, b) => {
                // a < b (unsigned)
                if let (Some((va, wa)), Some((vb, wb))) = (get_bv_val(*a), get_bv_val(*b)) {
                    if wa == wb {
                        return va >= vb; // conflict when NOT (va < vb)
                    }
                }
            }
            TermKind::BvUle(a, b) => {
                if let (Some((va, wa)), Some((vb, wb))) = (get_bv_val(*a), get_bv_val(*b)) {
                    if wa == wb {
                        return va > vb;
                    }
                }
            }
            // BvUgt(a, b) ≡ BvUlt(b, a): conflict when !(b < a) i.e. a <= b.
            // BvUge(a, b) ≡ BvUle(b, a): conflict when !(b <= a) i.e. a < b.
            // These are handled by the BvUlt/BvUle arms above with swapped args.
            // No separate BvUgt/BvUge variants exist in TermKind.
            TermKind::BvSlt(a, b) => {
                if let (Some((va, wa)), Some((vb, wb))) = (get_bv_val(*a), get_bv_val(*b)) {
                    if wa == wb {
                        let half = BigInt::one() << (wa as usize - 1);
                        let mod_val = BigInt::one() << wa as usize;
                        let signed_a = if va >= half {
                            va.clone() - &mod_val
                        } else {
                            va.clone()
                        };
                        let signed_b = if vb >= half {
                            vb.clone() - &mod_val
                        } else {
                            vb.clone()
                        };
                        return signed_a >= signed_b;
                    }
                }
            }
            TermKind::BvSle(a, b) => {
                if let (Some((va, wa)), Some((vb, wb))) = (get_bv_val(*a), get_bv_val(*b)) {
                    if wa == wb {
                        let half = BigInt::one() << (wa as usize - 1);
                        let mod_val = BigInt::one() << wa as usize;
                        let signed_a = if va >= half {
                            va.clone() - &mod_val
                        } else {
                            va.clone()
                        };
                        let signed_b = if vb >= half {
                            vb.clone() - &mod_val
                        } else {
                            vb.clone()
                        };
                        return signed_a > signed_b;
                    }
                }
            }
            // BvSgt(a, b) ≡ BvSlt(b, a): handled by BvSlt with swapped args.
            // BvSge(a, b) ≡ BvSle(b, a): handled by BvSle with swapped args.
            // No separate BvSgt/BvSge variants exist in TermKind.
            _ => {}
        }

        false
    }

    /// Check whether any integer ordering assertion is contradicted by a value
    /// forced by the array read-over-write axiom.
    ///
    /// This handles both direct terms like:
    ///   (< (select (store a 0 42) 0) 5)
    /// and alias-based forms like:
    ///   (= a1 (store a 0 42))
    ///   (< (select a1 0) 5)
    fn check_int_ordering_conflict(
        &self,
        aliases: &FxHashMap<TermId, TermId>,
        manager: &TermManager,
    ) -> bool {
        for &assertion in &self.assertions {
            let Some(data) = manager.get(assertion) else {
                continue;
            };

            let Some((lhs, rhs, ordering)) = (match &data.kind {
                TermKind::Lt(lhs, rhs) => Some((*lhs, *rhs, IntOrdering::Lt)),
                TermKind::Le(lhs, rhs) => Some((*lhs, *rhs, IntOrdering::Le)),
                TermKind::Gt(lhs, rhs) => Some((*lhs, *rhs, IntOrdering::Gt)),
                TermKind::Ge(lhs, rhs) => Some((*lhs, *rhs, IntOrdering::Ge)),
                _ => None,
            }) else {
                continue;
            };

            let Some(lhs_val) = self.evaluate_int_expr_with_array_axiom(lhs, aliases, manager)
            else {
                continue;
            };
            let Some(rhs_val) = self.evaluate_int_expr_with_array_axiom(rhs, aliases, manager)
            else {
                continue;
            };

            let holds = match ordering {
                IntOrdering::Lt => lhs_val < rhs_val,
                IntOrdering::Le => lhs_val <= rhs_val,
                IntOrdering::Gt => lhs_val > rhs_val,
                IntOrdering::Ge => lhs_val >= rhs_val,
            };

            if !holds {
                return true;
            }
        }

        false
    }

    /// True when `term` has an array sort.
    fn is_array_sorted(&self, term: TermId, manager: &TermManager) -> bool {
        manager.get(term).is_some_and(|d| {
            manager
                .sorts
                .get(d.sort)
                .is_some_and(|s| matches!(s.kind, oxiz_core::SortKind::Array { .. }))
        })
    }

    /// True when `term` is a `Store` expression (a structurally committed array
    /// value, as opposed to a plain array variable).
    fn is_store_term(&self, term: TermId, manager: &TermManager) -> bool {
        manager
            .get(term)
            .is_some_and(|d| matches!(d.kind, TermKind::Store(..)))
    }

    /// Collect positive (asserted-true) equalities `(= X Y)` where **both** sides
    /// are `Store` terms of array sort and `X` and `Y` are not the identical term.
    ///
    /// These are exactly the array equalities the EUF congruence core cannot
    /// decide soundly on its own: it may unify the two store terms into a single
    /// class without ever checking that their bases agree element-wise. Reflexive
    /// equalities (`X == Y`) are trivially satisfiable and excluded. Equalities
    /// appearing under a `Not` (i.e. disequalities) are excluded — a disequality
    /// of two distinct store terms is soundly satisfiable by keeping them apart.
    fn collect_positive_array_term_equalities(
        &self,
        manager: &TermManager,
    ) -> Vec<(TermId, TermId)> {
        let mut out = Vec::new();
        self.scan_positive_array_eq(manager, &mut out);
        out
    }

    /// Polarity-aware walker for
    /// [`Solver::collect_positive_array_term_equalities`]. Descends only into the
    /// sub-terms that are unconditionally asserted — see
    /// [`super::term_walk::asserted_children`] — and records a store=store
    /// equality only at positive polarity.
    ///
    /// The descent used to pass `positive` straight through an `And`, which made
    /// a doubly-negated equality inside `(not (and (not (= …)) p))` look
    /// asserted and refuted a formula that is satisfiable with `p = false`.
    ///
    /// Iterative, and pushing children in reverse so they pop left to right,
    /// for the same reasons as [`Solver::collect_array_constraints`] — as is
    /// the `(TermId, polarity)`-keyed revisit set, without which a shared
    /// Boolean sub-DAG is re-walked once per *path* to it, which doubles per
    /// level on a `(and x (not (not x)))` ladder.  A repeat at the same
    /// polarity could only push a duplicate pair into `out`, and both
    /// consumers re-run the same extensionality check on a duplicate.
    fn scan_positive_array_eq(&self, manager: &TermManager, out: &mut Vec<(TermId, TermId)>) {
        let mut worklist: Vec<(TermId, bool)> = self
            .assertions
            .iter()
            .rev()
            .map(|&assertion| (assertion, true))
            .collect();
        let mut visited: FxHashSet<(TermId, bool)> = FxHashSet::default();

        while let Some((term, positive)) = worklist.pop() {
            if !visited.insert((term, positive)) {
                continue;
            }
            let Some(data) = manager.get(term) else {
                continue;
            };
            match &data.kind {
                TermKind::And(_) | TermKind::Or(_) | TermKind::Not(_) => {
                    let children = super::term_walk::asserted_children(&data.kind, positive);
                    worklist.extend(children.into_iter().rev());
                }
                TermKind::Eq(lhs, rhs)
                    if positive
                        && *lhs != *rhs
                        && self.is_store_term(*lhs, manager)
                        && self.is_store_term(*rhs, manager)
                        && self.is_array_sorted(*lhs, manager)
                        && self.is_array_sorted(*rhs, manager) =>
                {
                    out.push((*lhs, *rhs));
                }
                _ => {}
            }
        }
    }

    /// Collect the store indices along the store chain rooted at `array` (i.e. the
    /// index of every `(store base idx val)` node until a non-store base is
    /// reached).
    ///
    /// A loop, not tail recursion: a store chain is as long as the input makes
    /// it, and one native frame per link is a process abort on a small stack.
    fn collect_store_indices(&self, array: TermId, manager: &TermManager, out: &mut Vec<TermId>) {
        let mut current = array;
        while let Some(data) = manager.get(current) {
            let TermKind::Store(base, idx, _val) = &data.kind else {
                return;
            };
            out.push(*idx);
            current = *base;
        }
    }

    /// Evaluate `(select array index)` through the read-over-write axiom, chasing
    /// nested stores. Returns `Some(value)` only when the value is forced (the
    /// index provably matches a store index, or provably differs at every store
    /// down to a store whose index matches); returns `None` when the outcome is
    /// ambiguous (base is a variable, or index/store-index relationship unknown).
    ///
    /// The store chain is walked by a loop rather than by tail recursion, for
    /// the same reason as [`Solver::collect_store_indices`].
    fn eval_read(&self, array: TermId, index: TermId, manager: &TermManager) -> Option<TermId> {
        let mut current = array;
        loop {
            let data = manager.get(current)?;
            let TermKind::Store(base, store_idx, stored_val) = &data.kind else {
                return None;
            };
            if self.terms_equal_simple(*store_idx, index, manager) {
                return Some(*stored_val);
            }
            if !self.are_different_values(*store_idx, index, manager) {
                // The relationship between `store_idx` and `index` is unknown:
                // cannot decide which value the read yields.
                return None;
            }
            current = *base;
        }
    }

    /// Detect an extensionality conflict between two store terms `x` and `y`:
    /// if reading both at some common store index yields two provably different
    /// concrete values, then `x = y` is unsatisfiable.
    fn store_extensionality_conflict(&self, x: TermId, y: TermId, manager: &TermManager) -> bool {
        let mut indices = Vec::new();
        self.collect_store_indices(x, manager, &mut indices);
        self.collect_store_indices(y, manager, &mut indices);
        for idx in indices {
            if let (Some(vx), Some(vy)) = (
                self.eval_read(x, idx, manager),
                self.eval_read(y, idx, manager),
            ) {
                if self.are_different_values(vx, vy, manager) {
                    return true;
                }
            }
        }
        false
    }

    /// Array soundness honesty gate (SAT side).
    ///
    /// Returns `true` when the assertion set contains a positive equality between
    /// two store terms that the [`store_extensionality_conflict`] check did not
    /// refute. Such an equality is *not* decided by the syntactic array checks or
    /// the EUF congruence core (which can satisfy `store_a = store_b` by merging
    /// the two terms into one class without enforcing that their bases agree at
    /// every index). Trusting the resulting assignment would risk a spurious
    /// `Sat`, so the caller (the `Context` command layer) downgrades `Sat` to
    /// `Unknown` when this returns `true` — never reporting `Sat` while an
    /// unchecked array atom remains.
    ///
    /// [`store_extensionality_conflict`]: Solver::store_extensionality_conflict
    pub(crate) fn array_atoms_need_theory(&self, manager: &TermManager) -> bool {
        for &(x, y) in &self.collect_positive_array_term_equalities(manager) {
            if !self.store_extensionality_conflict(x, y, manager) {
                return true;
            }
        }
        false
    }
}

#[derive(Clone, Copy)]
enum IntOrdering {
    Lt,
    Le,
    Gt,
    Ge,
}
