//! String theory constraint checking

#[allow(unused_imports)]
use crate::prelude::*;
use num_traits::ToPrimitive;
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_theories::string::{eval_ground_bool, solve_ground_string_model};

use super::Solver;
use super::term_walk::asserted_children;
use super::types::Model;

impl Solver {
    pub(super) fn check_string_constraints(&self, manager: &TermManager) -> bool {
        // Ground refutation (runs first, and needs none of the collection
        // below).  A string sub-formula with no variables has one fixed truth
        // value; if an *unconditionally asserted* one is `false`, the assertion
        // set is refuted outright.  Far more general than the syntactic checks
        // that follow, which stay because they also refute formulas whose
        // operands are variables.
        if self.ground_string_conflict(manager) {
            return true;
        }

        // Collect string variable assignments and length constraints
        let mut string_assignments: FxHashMap<TermId, String> = FxHashMap::default();
        let mut length_constraints: FxHashMap<TermId, i64> = FxHashMap::default();
        let mut concat_equalities: Vec<(Vec<TermId>, String)> = Vec::new();
        let mut replace_all_constraints: Vec<(TermId, TermId, String, String, String)> = Vec::new();
        let mut string_equalities: Vec<(TermId, TermId)> = Vec::new();

        // First pass: collect all string assignments and constraints from assertions
        self.collect_string_constraints(
            manager,
            &mut string_assignments,
            &mut length_constraints,
            &mut concat_equalities,
            &mut replace_all_constraints,
            &mut string_equalities,
        );

        // Check 0: constant-equality conflicts.  Every collected equality holds
        // unconditionally (they come from conjunctive contexts only), so terms
        // linked by them share a value.  A class that is forced to two *different*
        // string constants – `s = "x" ∧ s = "y"`, `a = "p" ∧ b = "q" ∧ a = b`, or
        // a bare `"x" = "y"` – is refuted by constant propagation alone.
        // Reference: Z3's theory_seq.cpp reduces constant-vs-constant sequence
        // equalities to `false` in `solve_eqs`.
        if self.propagate_string_equalities(manager, &string_equalities, &mut string_assignments) {
            return true;
        }

        // Second pass: Now that all variable assignments are collected, resolve replace_all constraints
        // where source was a variable that is now known
        self.collect_replace_all_with_resolved_vars(
            manager,
            &string_assignments,
            &mut replace_all_constraints,
        );

        // Check 1: Length vs concrete string conflicts (string_04 fix)
        // If we have len(x) = n and x = "literal", check if len("literal") == n
        for (&var, &declared_len) in &length_constraints {
            if let Some(value) = string_assignments.get(&var) {
                let actual_len = value.chars().count() as i64;
                if actual_len != declared_len {
                    return true; // Conflict: declared length != actual length
                }
            }
        }

        // Check 2: Concatenation length consistency (string_02 fix)
        // If we have concat(a, b, c) = "result", check if sum of lengths is consistent
        for (operands, result_str) in &concat_equalities {
            let result_len = result_str.chars().count() as i64;
            let mut total_declared_len = 0i64;
            let mut all_have_length = true;

            for operand in operands {
                if let Some(&len) = length_constraints.get(operand) {
                    total_declared_len += len;
                } else if let Some(value) = string_assignments.get(operand) {
                    total_declared_len += value.chars().count() as i64;
                } else {
                    all_have_length = false;
                    break;
                }
            }

            if all_have_length && total_declared_len != result_len {
                return true; // Conflict: sum of operand lengths != result length
            }
        }

        // Check 2b: Concatenation *content* consistency.  A concatenation whose
        // leading (resp. trailing) operands have known values forces the target
        // constant to start (resp. end) with them, e.g. `(str.++ "a" s) = "bcd"`
        // is refutable without ever guessing `s`.  Complements Check 2, which
        // only fires when *every* operand length is known.
        // Reference: Z3's theory_seq.cpp `solve_eqs` / `is_ternary_eq` prefix and
        // suffix reduction of `str.++` equations against a constant.
        for (operands, result_str) in &concat_equalities {
            if self.concat_content_conflict(operands, result_str, manager, &string_assignments) {
                return true;
            }
        }

        // Check 3: Replace-all operation semantics (string_08 fix)
        // If we have replace_all(s, old, new) = result, with s, old, new, result all known,
        // verify that the operation produces the expected result
        for (result_var, source_var, source_val, pattern, replacement) in &replace_all_constraints {
            // Check if result is assigned to a concrete value
            if let Some(result_val) = string_assignments.get(result_var) {
                // If source contains the pattern and pattern != replacement,
                // then result cannot equal source
                if !pattern.is_empty() && source_val.contains(pattern) && pattern != replacement {
                    // Compute actual result
                    let actual_result = source_val.replace(pattern, replacement);
                    if &actual_result != result_val {
                        return true; // Conflict: replace_all result mismatch
                    }
                }
            }
            // Also check if source is concrete but has a length constraint
            // The source_var might not be concrete but the source_val is already collected
            if length_constraints.contains_key(source_var) {
                if let Some(result_val) = string_assignments.get(result_var) {
                    // Source is constrained but result is concrete - check pattern effects
                    if !pattern.is_empty() {
                        // Check if pattern exists in source - if so, result must be different
                        if source_val.contains(pattern) && pattern != replacement {
                            // If source and result are claimed to be equal, but replacement would change it
                            if source_val == result_val.as_str() {
                                return true; // Conflict
                            }
                        }
                    }
                }
            }
        }

        false // No conflict found
    }

    /// Refute the assertion set when an **unconditionally asserted** sub-formula
    /// is a closed (variable-free) term whose value is the opposite of the
    /// polarity it is asserted with.
    ///
    /// # Why this is the missing half of the ground string procedure
    ///
    /// [`oxiz_theories::string::solve_ground_string_model`] can already
    /// *evaluate* every ground string operator – that is how a satisfiable
    /// ground formula gets its `Sat` certificate.  What it deliberately never
    /// produces is `Unsat`: a formula whose evaluation comes out `false` merely
    /// fails to verify, and the solver then reported the honest but far too
    /// weak `Unknown`.  A fully ground string formula is decidable, so this
    /// closes the loop: the same evaluator, run over an empty model, decides the
    /// refutation direction as well.
    ///
    /// # Soundness
    ///
    /// Two independent properties are needed, and they are kept strictly apart:
    ///
    /// * **Value.**  [`eval_ground_bool`] runs with an empty model, so a
    ///   variable – of any sort – evaluates to `None` and the `None` propagates.
    ///   A `Some(v)` answer therefore holds in *every* interpretation.  Because
    ///   such a value is the same wherever the term occurs, evaluating a term is
    ///   safe regardless of the polarity it sits at.
    /// * **Assertedness.**  What is *not* polarity-independent is whether a
    ///   sub-formula is asserted at all.  A fact taken from inside an `Or`, an
    ///   `Implies`, an `Ite`, or a Bool-sorted `Eq` is conditional, and treating
    ///   it as unconditional is exactly the bug class that produced false
    ///   `unsat` answers here before.  Descent therefore goes through
    ///   [`asserted_children`] and nothing else, carrying the polarity with it.
    ///
    /// A node that hands out asserted children needs no evaluation of its own:
    /// `And`⁺, `Or`⁻ and `Not` are refuted exactly when one of the children the
    /// walk already visits is, so skipping them avoids re-evaluating the whole
    /// sub-tree once per level of an `And` spine.  Every other node – including
    /// `And`⁻ and `Or`⁺, where de Morgan makes the children conditional – is
    /// evaluated as a unit.
    fn ground_string_conflict(&self, manager: &TermManager) -> bool {
        // Keep non-string problems off this path entirely: the evaluator is
        // recursive over the assertion DAG and there is nothing for it to
        // decide unless a string constant or string operator is present.
        if !self.mentions_string_term(manager) {
            return false;
        }

        let mut visited: FxHashSet<(TermId, bool)> = FxHashSet::default();
        let mut stack: Vec<(TermId, bool)> =
            self.assertions.iter().map(|&term| (term, true)).collect();
        while let Some((term, positive)) = stack.pop() {
            if !visited.insert((term, positive)) {
                continue;
            }
            let Some(term_data) = manager.get(term) else {
                continue;
            };
            let children = asserted_children(&term_data.kind, positive);
            if children.is_empty() {
                if eval_ground_bool(manager, term) == Some(!positive) {
                    return true;
                }
            } else {
                stack.extend(children);
            }
        }
        false
    }

    /// Whether the assertion set mentions any string constant or string-theory
    /// operator, i.e. whether ground string evaluation could decide anything.
    ///
    /// A formula built only from string *variables* and equalities has no closed
    /// string sub-term, so the ground refutation has nothing to fold and this
    /// gate skips it.
    fn mentions_string_term(&self, manager: &TermManager) -> bool {
        self.any_subterm(manager, |_, kind| {
            matches!(kind, TermKind::StringLit(_)) || Self::is_string_theory_atom(kind)
        })
    }

    /// Whether any sub-term reachable from an assertion satisfies `predicate`.
    ///
    /// One linear, visited-set-deduplicated walk over the whole assertion DAG,
    /// shared by the three presence tests in this module.  It descends through
    /// *every* structural child, including conditional ones, so – unlike
    /// [`asserted_children`] – its answer says nothing about whether a sub-term
    /// is asserted.  It may therefore only ever gate work; it must never be used
    /// to justify a conflict.
    fn any_subterm(
        &self,
        manager: &TermManager,
        predicate: impl Fn(TermId, &TermKind) -> bool,
    ) -> bool {
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut stack: Vec<TermId> = self.assertions.clone();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            let Some(term_data) = manager.get(term) else {
                continue;
            };
            if predicate(term, &term_data.kind) {
                return true;
            }
            super::term_walk::collect_structural_children(&term_data.kind, &mut stack);
        }
        false
    }

    /// Merge the collected (unconditionally asserted) string equalities into
    /// equivalence classes and push each class's constant value onto every one of
    /// its members.
    ///
    /// Returns `true` when a class is forced to two *different* string constants,
    /// which refutes the assertion set outright.  On `false` the resolved values
    /// are written back into `string_assignments`, so the length / concatenation
    /// / replace checks see values that reach a term through a chain of
    /// equalities, not just through a syntactically adjacent literal.
    fn propagate_string_equalities(
        &self,
        manager: &TermManager,
        equalities: &[(TermId, TermId)],
        string_assignments: &mut FxHashMap<TermId, String>,
    ) -> bool {
        if equalities.is_empty() {
            return false;
        }

        // Union-find over every term mentioned by an asserted string equality.
        let mut parent: FxHashMap<TermId, TermId> = FxHashMap::default();
        for &(lhs, rhs) in equalities {
            parent.entry(lhs).or_insert(lhs);
            parent.entry(rhs).or_insert(rhs);
            let lhs_root = Self::uf_find(&mut parent, lhs);
            let rhs_root = Self::uf_find(&mut parent, rhs);
            if lhs_root != rhs_root {
                parent.insert(lhs_root, rhs_root);
            }
        }

        // Each class may carry at most one constant value.
        let members: Vec<TermId> = parent.keys().copied().collect();
        let mut class_value: FxHashMap<TermId, String> = FxHashMap::default();
        for &member in &members {
            let Some(value) = self
                .get_string_literal(member, manager)
                .or_else(|| string_assignments.get(&member).cloned())
            else {
                continue;
            };
            let root = Self::uf_find(&mut parent, member);
            match class_value.get(&root) {
                Some(existing) if *existing != value => return true,
                Some(_) => {}
                None => {
                    class_value.insert(root, value);
                }
            }
        }

        // Publish the resolved value to every member of a pinned class.
        for &member in &members {
            let root = Self::uf_find(&mut parent, member);
            if let Some(value) = class_value.get(&root) {
                string_assignments
                    .entry(member)
                    .or_insert_with(|| value.clone());
            }
        }

        false
    }

    /// Union-find representative of `term`, with path compression.
    fn uf_find(parent: &mut FxHashMap<TermId, TermId>, term: TermId) -> TermId {
        let mut root = term;
        while let Some(&next) = parent.get(&root) {
            if next == root {
                break;
            }
            root = next;
        }
        let mut cursor = term;
        while let Some(&next) = parent.get(&cursor) {
            if next == cursor {
                break;
            }
            parent.insert(cursor, root);
            cursor = next;
        }
        root
    }

    /// Whether a concatenation equation `str.++ ops… = result` is refuted by the
    /// known values of its outermost operands.
    ///
    /// Consumes known operand values from the left and from the right; the target
    /// constant must then start with the known prefix, end with the known suffix,
    /// and be long enough to hold both.  When *every* operand is known the
    /// concatenation must equal the target exactly.
    fn concat_content_conflict(
        &self,
        operands: &[TermId],
        result: &str,
        manager: &TermManager,
        string_assignments: &FxHashMap<TermId, String>,
    ) -> bool {
        let value_of = |term: TermId| -> Option<String> {
            self.get_string_literal(term, manager)
                .or_else(|| string_assignments.get(&term).cloned())
        };

        let mut prefix = String::new();
        let mut lo = 0usize;
        while lo < operands.len() {
            let Some(value) = value_of(operands[lo]) else {
                break;
            };
            prefix.push_str(&value);
            lo += 1;
        }

        // Every operand is pinned: the concatenation is fully determined.
        if lo == operands.len() {
            return prefix != result;
        }

        let mut suffix = String::new();
        let mut hi = operands.len();
        while hi > lo {
            let Some(value) = value_of(operands[hi - 1]) else {
                break;
            };
            suffix.insert_str(0, &value);
            hi -= 1;
        }

        if !result.starts_with(&prefix) || !result.ends_with(&suffix) {
            return true;
        }
        prefix.chars().count() + suffix.chars().count() > result.chars().count()
    }

    /// Whether `term` has the SMT-LIB `String` sort.
    fn is_string_sorted(&self, term: TermId, manager: &TermManager) -> bool {
        manager
            .get(term)
            .and_then(|t| manager.sorts.get(t.sort))
            .is_some_and(oxiz_core::sort::Sort::is_string)
    }

    /// Collect string constraints from the sub-terms of every assertion that
    /// are asserted **positively and unconditionally**.
    ///
    /// Only the assertion itself and the conjuncts of a top-level `And` are
    /// unconditionally true, so that is exactly how far this descends.  Facts
    /// harvested from a disjunct, a negation, or an implication branch would be
    /// hypothetical, and the definite-conflict checks built on top of them would
    /// report a spurious `unsat` for satisfiable inputs such as
    /// `(or (= x "short") (= (str.len x) 10))`.
    ///
    /// # Why not `term_walk::asserted_children`
    ///
    /// The general rule also hands out a `Not`'s body and an `Or`'s disjuncts
    /// at *negative* polarity, but the `Eq` arm below records its facts as
    /// positive ones and has no polarity to consult: reached through
    /// `(not (or (= x "abc") p))` it would record `x = "abc"` when the
    /// assertion states the opposite.  Descending through `And` alone keeps
    /// every fact positive by construction.
    ///
    /// The walk is an explicit heap worklist rather than recursion – an
    /// assertion's nesting depth is attacker-controlled and this runs on
    /// whatever stack `check_sat`'s caller has.  Conjuncts are pushed in
    /// reverse so they pop left to right, matching the recursive order, which
    /// matters because `string_assignments` / `length_constraints` are
    /// `insert`ed into and the last write for a term wins.  There is no
    /// `visited` set, exactly as before.
    fn collect_string_constraints(
        &self,
        manager: &TermManager,
        string_assignments: &mut FxHashMap<TermId, String>,
        length_constraints: &mut FxHashMap<TermId, i64>,
        concat_equalities: &mut Vec<(Vec<TermId>, String)>,
        replace_all_constraints: &mut Vec<(TermId, TermId, String, String, String)>,
        string_equalities: &mut Vec<(TermId, TermId)>,
    ) {
        let mut worklist: Vec<TermId> = self.assertions.iter().rev().copied().collect();

        while let Some(term) = worklist.pop() {
            let Some(term_data) = manager.get(term) else {
                continue;
            };

            match &term_data.kind {
                // Handle equality: look for string-related equalities
                TermKind::Eq(lhs, rhs) => {
                    // Record the equality itself so equality chains between string
                    // terms can be closed under transitivity below.
                    if self.is_string_sorted(*lhs, manager) && self.is_string_sorted(*rhs, manager)
                    {
                        string_equalities.push((*lhs, *rhs));
                    }

                    // Check for variable = string literal
                    if let Some(lit) = self.get_string_literal(*rhs, manager) {
                        // lhs = "literal"
                        if self.is_string_variable(*lhs, manager) {
                            string_assignments.insert(*lhs, lit);
                        }
                    } else if let Some(lit) = self.get_string_literal(*lhs, manager) {
                        // "literal" = rhs
                        if self.is_string_variable(*rhs, manager) {
                            string_assignments.insert(*rhs, lit);
                        }
                    }

                    // Check for length constraint: (= (str.len x) n)
                    if let Some((var, len)) = self.extract_length_constraint(*lhs, *rhs, manager) {
                        length_constraints.insert(var, len);
                    } else if let Some((var, len)) =
                        self.extract_length_constraint(*rhs, *lhs, manager)
                    {
                        length_constraints.insert(var, len);
                    }

                    // Check for concat equality: (= (str.++ a b c) "result")
                    if let Some(result_str) = self.get_string_literal(*rhs, manager) {
                        if let Some(operands) = self.extract_concat_operands(*lhs, manager) {
                            concat_equalities.push((operands, result_str));
                        }
                    } else if let Some(result_str) = self.get_string_literal(*lhs, manager) {
                        if let Some(operands) = self.extract_concat_operands(*rhs, manager) {
                            concat_equalities.push((operands, result_str));
                        }
                    }

                    // Check for replace_all: (= result (str.replace_all s old new))
                    if let Some((source, pattern, replacement)) =
                        self.extract_replace_all(*rhs, manager)
                    {
                        // Get source value either directly or via variable assignment
                        let source_val = self
                            .get_string_literal(source, manager)
                            .or_else(|| string_assignments.get(&source).cloned());
                        if let Some(source_val) = source_val {
                            if let Some(pattern_val) = self.get_string_literal(pattern, manager) {
                                if let Some(replacement_val) =
                                    self.get_string_literal(replacement, manager)
                                {
                                    replace_all_constraints.push((
                                        *lhs,
                                        source,
                                        source_val,
                                        pattern_val,
                                        replacement_val,
                                    ));
                                }
                            }
                        }
                    } else if let Some((source, pattern, replacement)) =
                        self.extract_replace_all(*lhs, manager)
                    {
                        // Get source value either directly or via variable assignment
                        let source_val = self
                            .get_string_literal(source, manager)
                            .or_else(|| string_assignments.get(&source).cloned());
                        if let Some(source_val) = source_val {
                            if let Some(pattern_val) = self.get_string_literal(pattern, manager) {
                                if let Some(replacement_val) =
                                    self.get_string_literal(replacement, manager)
                                {
                                    replace_all_constraints.push((
                                        *rhs,
                                        source,
                                        source_val,
                                        pattern_val,
                                        replacement_val,
                                    ));
                                }
                            }
                        }
                    }

                    // No descent into `lhs`/`rhs`: the only formulas reachable from
                    // an equality's operands sit behind a Boolean equality, which is
                    // a polarity boundary – their facts are not unconditional.
                }

                // Handle And: every conjunct is asserted too.
                TermKind::And(args) => {
                    worklist.extend(args.iter().rev().copied());
                }

                // `Or` / `Not` / `Implies` / `Ite` are deliberately *not* traversed:
                // a fact under any of them is conditional, and the definite-conflict
                // checks may only reason about unconditional ones.
                _ => {}
            }
        }
    }

    /// Get string literal value from a term
    fn get_string_literal(&self, term: TermId, manager: &TermManager) -> Option<String> {
        let term_data = manager.get(term)?;
        if let TermKind::StringLit(s) = &term_data.kind {
            Some(s.clone())
        } else {
            None
        }
    }

    /// Check if a term is a string variable (not a literal or operation)
    fn is_string_variable(&self, term: TermId, manager: &TermManager) -> bool {
        let Some(term_data) = manager.get(term) else {
            return false;
        };
        matches!(term_data.kind, TermKind::Var(_))
    }

    /// Extract length constraint: (str.len var) = n
    fn extract_length_constraint(
        &self,
        lhs: TermId,
        rhs: TermId,
        manager: &TermManager,
    ) -> Option<(TermId, i64)> {
        let lhs_data = manager.get(lhs)?;
        let rhs_data = manager.get(rhs)?;

        // Check if lhs is (str.len var) and rhs is an integer constant
        if let TermKind::StrLen(inner) = &lhs_data.kind {
            if let TermKind::IntConst(n) = &rhs_data.kind {
                return n.to_i64().map(|len| (*inner, len));
            }
        }

        None
    }

    /// Extract operands from a concat expression
    fn extract_concat_operands(&self, term: TermId, manager: &TermManager) -> Option<Vec<TermId>> {
        let term_data = manager.get(term)?;

        match &term_data.kind {
            TermKind::StrConcat(lhs, rhs) => {
                let mut operands = Vec::new();
                // Flatten nested concats
                self.flatten_concat(*lhs, manager, &mut operands);
                self.flatten_concat(*rhs, manager, &mut operands);
                Some(operands)
            }
            _ => None,
        }
    }

    /// Flatten a concat tree into a list of operands, left to right.
    ///
    /// Iterative for the same reason as the collectors above: a `str.++` chain
    /// is built by folding an n-ary application into nested binary nodes, so
    /// `(str.++ x1 … x5000)` is a 5000-deep tree and one native frame per level
    /// aborted the process on a 1 MiB stack.  The worklist pushes `rhs` before
    /// `lhs` so that popping yields the left operand first, which is what makes
    /// the output order match the recursive version's.
    fn flatten_concat(&self, term: TermId, manager: &TermManager, operands: &mut Vec<TermId>) {
        let mut worklist = vec![term];
        while let Some(current) = worklist.pop() {
            let Some(term_data) = manager.get(current) else {
                operands.push(current);
                continue;
            };

            match &term_data.kind {
                TermKind::StrConcat(lhs, rhs) => {
                    worklist.push(*rhs);
                    worklist.push(*lhs);
                }
                _ => {
                    operands.push(current);
                }
            }
        }
    }

    /// Extract replace_all operation: (str.replace_all source pattern replacement)
    fn extract_replace_all(
        &self,
        term: TermId,
        manager: &TermManager,
    ) -> Option<(TermId, TermId, TermId)> {
        let term_data = manager.get(term)?;
        if let TermKind::StrReplaceAll(source, pattern, replacement) = &term_data.kind {
            Some((*source, *pattern, *replacement))
        } else {
            None
        }
    }

    /// Second pass collection for replace_all with resolved variable
    /// assignments.
    ///
    /// Same descent, same order and same absence of a `visited` set as
    /// [`Self::collect_string_constraints`], and iterative for the same reason.
    fn collect_replace_all_with_resolved_vars(
        &self,
        manager: &TermManager,
        string_assignments: &FxHashMap<TermId, String>,
        replace_all_constraints: &mut Vec<(TermId, TermId, String, String, String)>,
    ) {
        let mut worklist: Vec<TermId> = self.assertions.iter().rev().copied().collect();

        while let Some(term) = worklist.pop() {
            let Some(term_data) = manager.get(term) else {
                continue;
            };

            match &term_data.kind {
                TermKind::Eq(lhs, rhs) => {
                    // Check for replace_all with variable source that is now resolved
                    if let Some((source, pattern, replacement)) =
                        self.extract_replace_all(*rhs, manager)
                    {
                        // Try to resolve source from assignments
                        if let Some(source_val) = string_assignments.get(&source) {
                            if let Some(pattern_val) = self.get_string_literal(pattern, manager) {
                                if let Some(replacement_val) =
                                    self.get_string_literal(replacement, manager)
                                {
                                    // Only add if not already present
                                    let entry = (
                                        *lhs,
                                        source,
                                        source_val.clone(),
                                        pattern_val,
                                        replacement_val,
                                    );
                                    if !replace_all_constraints.contains(&entry) {
                                        replace_all_constraints.push(entry);
                                    }
                                }
                            }
                        }
                    } else if let Some((source, pattern, replacement)) =
                        self.extract_replace_all(*lhs, manager)
                    {
                        // Try to resolve source from assignments
                        if let Some(source_val) = string_assignments.get(&source) {
                            if let Some(pattern_val) = self.get_string_literal(pattern, manager) {
                                if let Some(replacement_val) =
                                    self.get_string_literal(replacement, manager)
                                {
                                    // Only add if not already present
                                    let entry = (
                                        *rhs,
                                        source,
                                        source_val.clone(),
                                        pattern_val,
                                        replacement_val,
                                    );
                                    if !replace_all_constraints.contains(&entry) {
                                        replace_all_constraints.push(entry);
                                    }
                                }
                            }
                        }
                    }

                    // No descent into the operands – see
                    // `collect_string_constraints` for why an equality's
                    // children are a polarity boundary.
                }
                TermKind::And(args) => {
                    worklist.extend(args.iter().rev().copied());
                }
                // `Or` / `Not` / `Implies` are conditional contexts and are not
                // traversed; see `collect_string_constraints`.
                _ => {}
            }
        }
    }

    /// Returns `true` if `kind` is a string-theory operation or predicate whose
    /// value / truth the incomplete string checks above cannot certify.
    ///
    /// These atoms are mapped to fresh SAT variables by `encode.rs` and are
    /// never evaluated by a real string theory, so a positive `Sat` answer that
    /// relies on them is unsound.  Bare string literals are excluded – they only
    /// participate through structural equality, which the EUF core handles.
    fn is_string_theory_atom(kind: &TermKind) -> bool {
        matches!(
            kind,
            TermKind::StrConcat(_, _)
                | TermKind::StrLen(_)
                | TermKind::StrSubstr(_, _, _)
                | TermKind::StrAt(_, _)
                | TermKind::StrContains(_, _)
                | TermKind::StrPrefixOf(_, _)
                | TermKind::StrSuffixOf(_, _)
                | TermKind::StrIndexOf(_, _, _)
                | TermKind::StrReplace(_, _, _)
                | TermKind::StrReplaceAll(_, _, _)
                | TermKind::StrReplaceRe(_, _, _)
                | TermKind::StrReplaceReAll(_, _, _)
                | TermKind::StrToInt(_)
                | TermKind::IntToStr(_)
                | TermKind::StrInRe(_, _)
                | TermKind::StrLt(_, _)
                | TermKind::StrLe(_, _)
                | TermKind::StrToCode(_)
                | TermKind::StrFromCode(_)
        )
    }

    /// Attempt to decide the ground string fragment by constructing and
    /// *verifying* a concrete model with the string theory's ground solver
    /// ([`oxiz_theories::string::solve_ground_string_model`]).
    ///
    /// Returns `true` only when a concrete assignment to every string variable
    /// makes the whole assertion set evaluate to `true` – a sound `Sat`
    /// certificate. When no such witness is found within the search bounds it
    /// returns `false`, and the caller keeps the honest `Unknown` verdict.
    ///
    /// On success the verified witness is *published* as the solver's model, so
    /// a following `(get-value ...)` / `(get-model)` reports real string values
    /// instead of `(error "No model available")`.  This path never runs the SAT
    /// core, so nothing else would populate the model.
    pub(super) fn ground_string_model_sat(&mut self, manager: &mut TermManager) -> bool {
        let Some(assignment) = solve_ground_string_model(manager, &self.assertions) else {
            return false;
        };
        let mut model = Model::new();
        for (term, value) in assignment {
            let value_term = manager.mk_string_lit(&value);
            model.set(term, value_term);
        }
        self.model = Some(model);
        true
    }

    /// Fill in the string part of a model built by the CDCL(T) core.
    ///
    /// The core carries no string theory, so string-sorted variables never get a
    /// value from the SAT / arithmetic / bit-vector extraction passes and
    /// `(get-value (s))` would echo `s` back unevaluated.  The ground string
    /// decision procedure supplies one, and only ever returns an assignment it
    /// has verified against *every* assertion, so the published values are
    /// consistent with the formula.  Existing entries are never overwritten.
    ///
    /// The ground procedure's evaluator only knows string variables, so it
    /// declines to certify anything whose assertions also mention a free
    /// Boolean / arithmetic variable.  In that case fall back to the values that
    /// the unconditional equalities *force* – still sound, just narrower.
    pub(super) fn extract_string_model(&self, model: &mut Model, manager: &mut TermManager) {
        if !self.has_string_sorted_var(manager) {
            return;
        }
        if let Some(assignment) = solve_ground_string_model(manager, &self.assertions) {
            for (term, value) in assignment {
                if model.get(term).is_none() {
                    let value_term = manager.mk_string_lit(&value);
                    model.set(term, value_term);
                }
            }
            return;
        }
        let forced: Vec<(TermId, String)> = self
            .forced_string_values(manager)
            .into_iter()
            .filter(|(term, _)| {
                matches!(manager.get(*term).map(|t| &t.kind), Some(TermKind::Var(_)))
            })
            .collect();
        for (term, value) in forced {
            if model.get(term).is_none() {
                let value_term = manager.mk_string_lit(&value);
                model.set(term, value_term);
            }
        }
    }

    /// The string values that the unconditionally asserted equalities force,
    /// closed under transitivity.
    ///
    /// Contradictory facts yield an empty map: `check_string_constraints` has
    /// already refuted such an assertion set, so no model is being built for it.
    fn forced_string_values(&self, manager: &TermManager) -> FxHashMap<TermId, String> {
        let mut string_assignments: FxHashMap<TermId, String> = FxHashMap::default();
        let mut length_constraints: FxHashMap<TermId, i64> = FxHashMap::default();
        let mut concat_equalities: Vec<(Vec<TermId>, String)> = Vec::new();
        let mut replace_all_constraints: Vec<(TermId, TermId, String, String, String)> = Vec::new();
        let mut string_equalities: Vec<(TermId, TermId)> = Vec::new();

        self.collect_string_constraints(
            manager,
            &mut string_assignments,
            &mut length_constraints,
            &mut concat_equalities,
            &mut replace_all_constraints,
            &mut string_equalities,
        );

        if self.propagate_string_equalities(manager, &string_equalities, &mut string_assignments) {
            return FxHashMap::default();
        }
        string_assignments
    }

    /// Whether any assertion mentions a `String`-sorted variable.  Used to keep
    /// the string model-extraction pass off the hot path of string-free problems.
    fn has_string_sorted_var(&self, manager: &TermManager) -> bool {
        self.any_subterm(manager, |term, kind| {
            matches!(kind, TermKind::Var(_)) && self.is_string_sorted(term, manager)
        })
    }

    /// Returns `true` when the current assertion set contains any string-theory
    /// atom that the incomplete string conflict checks cannot decide.
    ///
    /// When this holds and no definite string conflict was found, the solver
    /// MUST answer `Unknown` rather than let the SAT core treat the atom as a
    /// free Boolean – the latter would report `Sat` for unsatisfiable formulas
    /// such as `(= s "abc") ∧ (str.contains s "xyz")`.
    pub(super) fn string_atoms_need_theory(&self, manager: &TermManager) -> bool {
        self.any_subterm(manager, |_, kind| Self::is_string_theory_atom(kind))
    }
}

#[cfg(test)]
mod tests {
    use super::Solver;
    use crate::prelude::*;
    use oxiz_core::ast::{TermId, TermKind, TermManager};
    use smallvec::smallvec;

    /// The two fact sets these tests inspect.
    type StringFacts = (FxHashMap<TermId, String>, FxHashMap<TermId, i64>);

    /// Run the string collector over `assertions`.
    fn collect(manager: &TermManager, assertions: Vec<TermId>) -> StringFacts {
        let mut solver = Solver::new();
        solver.assertions = assertions;
        let mut assignments = FxHashMap::default();
        let mut lengths = FxHashMap::default();
        let mut concats = Vec::new();
        let mut replaces = Vec::new();
        let mut equalities = Vec::new();
        solver.collect_string_constraints(
            manager,
            &mut assignments,
            &mut lengths,
            &mut concats,
            &mut replaces,
            &mut equalities,
        );
        (assignments, lengths)
    }

    /// The flattened operand list of the one concat equality in `assertions`.
    fn concat_operands(
        manager: &TermManager,
        assertions: Vec<TermId>,
    ) -> Vec<(Vec<TermId>, String)> {
        let mut solver = Solver::new();
        solver.assertions = assertions;
        let mut assignments = FxHashMap::default();
        let mut lengths = FxHashMap::default();
        let mut concats = Vec::new();
        let mut replaces = Vec::new();
        let mut equalities = Vec::new();
        solver.collect_string_constraints(
            manager,
            &mut assignments,
            &mut lengths,
            &mut concats,
            &mut replaces,
            &mut equalities,
        );
        concats
    }

    /// A two-conjunct `And` the builder cannot flatten into its parent – see
    /// `check_dt.rs`'s twin for why `mk_and` will not do.
    fn nested_and(manager: &mut TermManager, first: TermId, second: TermId) -> TermId {
        let bool_sort = manager.sorts.bool_sort;
        manager.intern_term(TermKind::And(smallvec![first, second]), bool_sort)
    }

    /// An asserted `(= x "abc")` pins `x`; the same equality inside one
    /// disjunct of an `Or`, or under a `Not`, is conditional and must not be
    /// harvested – `(or (= x "short") (= (str.len x) 10))` is satisfiable and
    /// the length check would otherwise refute it.
    #[test]
    fn only_unconditional_equalities_are_collected() {
        let mut manager = TermManager::new();
        let string_sort = manager.sorts.string_sort();
        let x = manager.mk_var("x", string_sort);
        let abc = manager.mk_string_lit("abc");
        let p = manager.mk_var("p", manager.sorts.bool_sort);
        let equality = manager.mk_eq(x, abc);

        let (assignments, _) = collect(&manager, vec![equality]);
        assert_eq!(assignments.get(&x), Some(&"abc".to_string()));

        let disjunction = manager.mk_or([equality, p]);
        let (assignments, _) = collect(&manager, vec![disjunction]);
        assert!(assignments.is_empty());

        let negated = manager.mk_not(equality);
        let (assignments, _) = collect(&manager, vec![negated]);
        assert!(assignments.is_empty());

        let conjunction = manager.mk_and([equality, p]);
        let (assignments, _) = collect(&manager, vec![conjunction]);
        assert_eq!(assignments.get(&x), Some(&"abc".to_string()));
    }

    /// Conjuncts are visited left to right, so a later assignment for the same
    /// variable overwrites an earlier one.
    #[test]
    fn later_conjuncts_win_the_assignment_map() {
        let mut manager = TermManager::new();
        let string_sort = manager.sorts.string_sort();
        let x = manager.mk_var("x", string_sort);
        let first_value = manager.mk_string_lit("first");
        let second_value = manager.mk_string_lit("second");
        let first = manager.mk_eq(x, first_value);
        let second = manager.mk_eq(x, second_value);
        let assertion = nested_and(&mut manager, first, second);

        let (assignments, _) = collect(&manager, vec![assertion]);
        assert_eq!(assignments.get(&x), Some(&"second".to_string()));
    }

    /// `flatten_concat` yields the operands of a `str.++` tree left to right,
    /// whatever shape the tree has.
    #[test]
    fn concat_operands_come_out_left_to_right() {
        let mut manager = TermManager::new();
        let string_sort = manager.sorts.string_sort();
        let a = manager.mk_var("a", string_sort);
        let b = manager.mk_var("b", string_sort);
        let c = manager.mk_var("c", string_sort);
        let d = manager.mk_var("d", string_sort);
        // `(str.++ (str.++ a b) (str.++ c d))` – both a left and a right spine.
        let left = manager.mk_str_concat(a, b);
        let right = manager.mk_str_concat(c, d);
        let concat = manager.mk_str_concat(left, right);
        let target = manager.mk_string_lit("abcd");
        let assertion = manager.mk_eq(concat, target);

        let collected = concat_operands(&manager, vec![assertion]);
        assert_eq!(collected, vec![(vec![a, b, c, d], "abcd".to_string())]);
    }

    /// A `str.++` chain 25 000 deep is flattened on the heap, not the native
    /// stack – this is the shape (`(str.++ x1 … xN)` folded into nested binary
    /// nodes) that aborted the process before.
    #[test]
    fn deep_concat_chain_flattens_on_a_worker_stack() {
        // Stack and depth scale together (1 MiB/200k -> 128 KiB/25k): the
        // ~5 B-per-frame threshold is the pin, so never raise one alone.
        const DEPTH: usize = 25_000;

        let operand_count = std::thread::Builder::new()
            .stack_size(1 << 17)
            .spawn(|| {
                let mut manager = TermManager::new();
                let string_sort = manager.sorts.string_sort();
                let mut chain = manager.mk_var("x0", string_sort);
                for level in 1..=DEPTH {
                    let next = manager.mk_var(&format!("x{level}"), string_sort);
                    chain = manager.mk_str_concat(chain, next);
                }
                let target = manager.mk_string_lit("abc");
                let assertion = manager.mk_eq(chain, target);
                concat_operands(&manager, vec![assertion])
            })
            .expect("spawn worker thread")
            .join()
            .expect("worker thread must return, not abort");

        assert_eq!(operand_count.len(), 1);
        assert_eq!(operand_count[0].0.len(), DEPTH + 1);
        assert_eq!(operand_count[0].1, "abc");
    }

    /// A deeply nested conjunction is walked on the heap, and the equality at
    /// the bottom is still collected.
    #[test]
    fn deeply_nested_conjunction_walks_on_a_worker_stack() {
        // Stack and depth scale together (1 MiB/200k -> 128 KiB/25k): the
        // ~5 B-per-frame threshold is the pin, so never raise one alone.
        const DEPTH: usize = 25_000;

        let assignment = std::thread::Builder::new()
            .stack_size(1 << 17)
            .spawn(|| {
                let mut manager = TermManager::new();
                let string_sort = manager.sorts.string_sort();
                let x = manager.mk_var("x", string_sort);
                let abc = manager.mk_string_lit("abc");
                let filler = manager.mk_var("p", manager.sorts.bool_sort);
                let mut chain = manager.mk_eq(x, abc);
                for _ in 0..DEPTH {
                    chain = nested_and(&mut manager, chain, filler);
                }
                let (assignments, _) = collect(&manager, vec![chain]);
                assignments.get(&x).cloned()
            })
            .expect("spawn worker thread")
            .join()
            .expect("worker thread must return, not abort");

        assert_eq!(assignment, Some("abc".to_string()));
    }
}
