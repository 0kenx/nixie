//! Datatype theory constraint checking

#[allow(unused_imports)]
use crate::prelude::*;
use oxiz_core::ast::{TermId, TermKind, TermManager};

use super::Solver;

impl Solver {
    pub(super) fn check_dt_constraints(&self, manager: &TermManager) -> bool {
        // Collect positive constructor tester constraints: ((_ is Constructor) x)
        let mut constructor_testers: FxHashMap<TermId, Vec<String>> = FxHashMap::default();
        // Collect negative constructor tester constraints: (not ((_ is Constructor) x))
        let mut negative_testers: FxHashMap<TermId, Vec<String>> = FxHashMap::default();
        // Collect constructor equalities: x = Constructor(...)
        let mut constructor_equalities: FxHashMap<TermId, Vec<String>> = FxHashMap::default();
        // Collect DT variable equalities: x = y where both are DT variables
        let mut dt_var_equalities: Vec<(TermId, TermId)> = Vec::new();

        self.collect_dt_constraints_v2(
            manager,
            &mut constructor_testers,
            &mut negative_testers,
            &mut constructor_equalities,
            &mut dt_var_equalities,
        );

        // Check: If a variable has multiple different constructor testers, it's UNSAT
        for (_var, testers) in &constructor_testers {
            if testers.len() > 1 {
                // Multiple different constructors asserted for the same variable
                // Check if they're actually different
                let first = &testers[0];
                for tester in testers.iter().skip(1) {
                    if tester != first {
                        return true; // Conflict: x is Constructor1 AND x is Constructor2
                    }
                }
            }
        }

        // Check: If a variable has a positive and negative tester for the same constructor
        for (var, pos_testers) in &constructor_testers {
            if let Some(neg_testers) = negative_testers.get(var) {
                for pos in pos_testers {
                    for neg in neg_testers {
                        if pos == neg {
                            return true; // Conflict: (is Cons x) AND (not (is Cons x))
                        }
                    }
                }
            }
        }

        // Check: If a variable has different constructor equalities, it's UNSAT
        for (_var, constructors) in &constructor_equalities {
            if constructors.len() > 1 {
                let first = &constructors[0];
                for cons in constructors.iter().skip(1) {
                    if cons != first {
                        return true; // Conflict: x = Constructor1 AND x = Constructor2
                    }
                }
            }
        }

        // Check: If a variable has a constructor tester that conflicts with its equality
        for (var, testers) in &constructor_testers {
            if let Some(equalities) = constructor_equalities.get(var) {
                for tester in testers {
                    for eq_cons in equalities {
                        if tester != eq_cons {
                            return true; // Conflict: (is Cons1 x) AND x = Cons2(...)
                        }
                    }
                }
            }
        }

        // Check: If a variable has a negative tester that conflicts with its equality
        for (var, neg_testers) in &negative_testers {
            if let Some(equalities) = constructor_equalities.get(var) {
                for neg in neg_testers {
                    for eq_cons in equalities {
                        if neg == eq_cons {
                            return true; // Conflict: (not (is Cons x)) AND x = Cons(...)
                        }
                    }
                }
            }
        }

        // Check cross-variable constraints through equality
        // If l1 = l2 and they have conflicting tester constraints, it's UNSAT
        for &(var1, var2) in &dt_var_equalities {
            // Case 1: var1 has positive tester, var2 has negative tester for same constructor
            if let Some(pos1) = constructor_testers.get(&var1) {
                if let Some(neg2) = negative_testers.get(&var2) {
                    for p in pos1 {
                        for n in neg2 {
                            if p == n {
                                // l1 = l2, (is Cons l1), (not (is Cons l2)) => UNSAT
                                return true;
                            }
                        }
                    }
                }
            }
            // Case 2: var2 has positive tester, var1 has negative tester for same constructor
            if let Some(pos2) = constructor_testers.get(&var2) {
                if let Some(neg1) = negative_testers.get(&var1) {
                    for p in pos2 {
                        for n in neg1 {
                            if p == n {
                                // l1 = l2, (is Cons l2), (not (is Cons l1)) => UNSAT
                                return true;
                            }
                        }
                    }
                }
            }

            // Case 3: var1 has different positive tester than var2
            if let Some(pos1) = constructor_testers.get(&var1) {
                if let Some(pos2) = constructor_testers.get(&var2) {
                    for p1 in pos1 {
                        for p2 in pos2 {
                            if p1 != p2 {
                                // l1 = l2, (is Cons1 l1), (is Cons2 l2) where Cons1 != Cons2 => UNSAT
                                return true;
                            }
                        }
                    }
                }
            }

            // Case 4: var1 has constructor equality, var2 has conflicting negative tester
            if let Some(eq1) = constructor_equalities.get(&var1) {
                if let Some(neg2) = negative_testers.get(&var2) {
                    for e in eq1 {
                        for n in neg2 {
                            if e == n {
                                // l1 = l2, l1 = Cons(...), (not (is Cons l2)) => UNSAT
                                return true;
                            }
                        }
                    }
                }
            }
            // Case 5: var2 has constructor equality, var1 has conflicting negative tester
            if let Some(eq2) = constructor_equalities.get(&var2) {
                if let Some(neg1) = negative_testers.get(&var1) {
                    for e in eq2 {
                        for n in neg1 {
                            if e == n {
                                // l1 = l2, l2 = Cons(...), (not (is Cons l1)) => UNSAT
                                return true;
                            }
                        }
                    }
                }
            }

            // Case 6: var1 has constructor equality, var2 has conflicting positive tester
            if let Some(eq1) = constructor_equalities.get(&var1) {
                if let Some(pos2) = constructor_testers.get(&var2) {
                    for e in eq1 {
                        for p in pos2 {
                            if e != p {
                                // l1 = l2, l1 = Cons1(...), (is Cons2 l2) where Cons1 != Cons2 => UNSAT
                                return true;
                            }
                        }
                    }
                }
            }
            // Case 7: var2 has constructor equality, var1 has conflicting positive tester
            if let Some(eq2) = constructor_equalities.get(&var2) {
                if let Some(pos1) = constructor_testers.get(&var1) {
                    for e in eq2 {
                        for p in pos1 {
                            if e != p {
                                // l1 = l2, l2 = Cons1(...), (is Cons2 l1) where Cons1 != Cons2 => UNSAT
                                return true;
                            }
                        }
                    }
                }
            }

            // Case 8: Both have different constructor equalities
            if let Some(eq1) = constructor_equalities.get(&var1) {
                if let Some(eq2) = constructor_equalities.get(&var2) {
                    for e1 in eq1 {
                        for e2 in eq2 {
                            if e1 != e2 {
                                // l1 = l2, l1 = Cons1(...), l2 = Cons2(...) where Cons1 != Cons2 => UNSAT
                                return true;
                            }
                        }
                    }
                }
            }
        }

        false
    }

    /// Collect datatype constraints from the sub-terms of every assertion that
    /// are asserted **unconditionally**, carrying a polarity that records
    /// whether an odd number of `Not`s has been crossed on the way in.
    ///
    /// Every fact recorded here feeds a definite-conflict check in
    /// [`Self::check_dt_constraints`], which answers `Unsat` outright, so the
    /// descent is restricted to the sub-terms the assertion set genuinely
    /// entails – see
    /// [`super::term_walk::asserted_children`] for the rule and its rationale.
    /// The two boundaries this collector used to cross:
    ///
    /// * An equality's operands. This AST has no `Iff`, so `(= t p)` on two
    ///   Bool-sorted terms is a `TermKind::Eq`; it is satisfied with both sides
    ///   false, so `(= ((_ is cons) x) p)` does not assert `((_ is cons) x)`.
    /// * `And` conjuncts reached at negative polarity, where
    ///   `(not (and a b))` is a disjunction and entails neither conjunct.
    ///
    /// The walk is driven by an explicit heap worklist rather than by
    /// recursion: it runs on whatever stack `check_sat`'s caller happens to
    /// have, and an assertion's nesting depth is attacker-controlled, so one
    /// native frame per level is a process abort waiting to happen.  Children
    /// are pushed in reverse so that popping visits them left to right – the
    /// order the recursive descent had, which matters because several of the
    /// maps below are order-sensitive (`testers[0]` is compared against the
    /// rest, and `push` order decides it).
    ///
    /// There is deliberately no `visited` set.  A shared sub-term can be
    /// reached at *both* polarities on a DAG, and skipping the second visit on
    /// a `TermId`-keyed set would silently drop the fact that belongs to the
    /// other polarity.
    fn collect_dt_constraints_v2(
        &self,
        manager: &TermManager,
        constructor_testers: &mut FxHashMap<TermId, Vec<String>>,
        negative_testers: &mut FxHashMap<TermId, Vec<String>>,
        constructor_equalities: &mut FxHashMap<TermId, Vec<String>>,
        dt_var_equalities: &mut Vec<(TermId, TermId)>,
    ) {
        // Assertions are themselves visited left to right, so the first one
        // must be on top of the stack.
        let mut worklist: Vec<(TermId, bool)> = self
            .assertions
            .iter()
            .rev()
            .map(|&assertion| (assertion, true))
            .collect();

        while let Some((term, in_positive_context)) = worklist.pop() {
            let Some(term_data) = manager.get(term) else {
                continue;
            };

            match &term_data.kind {
                TermKind::DtTester { constructor, arg } => {
                    let cons_name = manager.resolve_str(*constructor).to_string();
                    if in_positive_context {
                        // Positive: ((_ is Constructor) var)
                        constructor_testers.entry(*arg).or_default().push(cons_name);
                    } else {
                        // Negative: (not ((_ is Constructor) var))
                        negative_testers.entry(*arg).or_default().push(cons_name);
                    }
                }
                // A negated equality is a DISequality and yields no constructor
                // fact, so the arm is guarded rather than entered-then-tested.
                // Either way there is no descent into `lhs` / `rhs`: an equality's
                // operands are a polarity boundary.  `(= ((_ is cons) x) p)` is
                // satisfied with both sides false, so recording `((_ is cons) x)`
                // as a tester fact refuted satisfiable inputs.
                TermKind::Eq(lhs, rhs) if in_positive_context => {
                    // Check for x = Constructor(...)
                    if let Some(rhs_data) = manager.get(*rhs) {
                        if let TermKind::DtConstructor { constructor, .. } = &rhs_data.kind {
                            if self.is_dt_variable(*lhs, manager) {
                                constructor_equalities
                                    .entry(*lhs)
                                    .or_default()
                                    .push(manager.resolve_str(*constructor).to_string());
                            }
                        }
                    }
                    if let Some(lhs_data) = manager.get(*lhs) {
                        if let TermKind::DtConstructor { constructor, .. } = &lhs_data.kind {
                            if self.is_dt_variable(*rhs, manager) {
                                constructor_equalities
                                    .entry(*rhs)
                                    .or_default()
                                    .push(manager.resolve_str(*constructor).to_string());
                            }
                        }
                    }

                    // Check for DT variable equality: x = y where both are DT variables
                    if self.is_dt_variable(*lhs, manager) && self.is_dt_variable(*rhs, manager) {
                        dt_var_equalities.push((*lhs, *rhs));
                    }
                }
                // `And` / `Or` / `Not` are the only nodes that can carry an
                // unconditional fact downwards, and `asserted_children` is the
                // single place that decides which – in particular it refuses to
                // hand out `And` conjuncts at negative polarity.
                TermKind::And(_) | TermKind::Or(_) | TermKind::Not(_) => {
                    let children =
                        super::term_walk::asserted_children(&term_data.kind, in_positive_context);
                    worklist.extend(children.into_iter().rev());
                }
                _ => {}
            }
        }
    }

    /// Collect datatype constraints from a term.
    ///
    /// Legacy v1 collector, superseded by [`Self::collect_dt_constraints_v2`]
    /// (which additionally harvests negative testers and variable equalities)
    /// but kept with identical semantics: positive testers and constructor
    /// equalities only, polarity carried through `And` / `Or` / `Not` exactly
    /// as [`super::term_walk::asserted_children`] prescribes.
    #[allow(dead_code)]
    fn collect_dt_constraints(
        &self,
        term: TermId,
        manager: &TermManager,
        constructor_testers: &mut FxHashMap<TermId, Vec<String>>,
        constructor_equalities: &mut FxHashMap<TermId, Vec<String>>,
    ) {
        self.collect_dt_constraints_inner(
            term,
            manager,
            constructor_testers,
            constructor_equalities,
            true,
        );
    }

    /// The walk behind [`Self::collect_dt_constraints`], starting at an
    /// arbitrary polarity.
    ///
    /// Driven by an explicit heap worklist rather than by recursion, for the
    /// same reason as [`Self::collect_dt_constraints_v2`]: the input's nesting
    /// depth is caller-controlled, and one native frame per level is a process
    /// abort waiting to happen.  Children are pushed in reverse so that popping
    /// visits them left to right – the order the recursive descent had, which
    /// the order-sensitive `Vec` pushes below depend on.  There is deliberately
    /// no `visited` set, exactly as before: a shared sub-term contributes its
    /// facts once per occurrence and can be reached at both polarities.
    #[allow(dead_code)]
    fn collect_dt_constraints_inner(
        &self,
        term: TermId,
        manager: &TermManager,
        constructor_testers: &mut FxHashMap<TermId, Vec<String>>,
        constructor_equalities: &mut FxHashMap<TermId, Vec<String>>,
        in_positive_context: bool,
    ) {
        let mut worklist: Vec<(TermId, bool)> = vec![(term, in_positive_context)];

        while let Some((term, in_positive_context)) = worklist.pop() {
            let Some(term_data) = manager.get(term) else {
                continue;
            };

            match &term_data.kind {
                TermKind::DtTester { constructor, arg } if in_positive_context => {
                    // ((_ is Constructor) var) - only collect when in positive
                    // context; v1 has no negative-tester map, so a tester reached
                    // at negative polarity falls through to the no-op arm below.
                    constructor_testers
                        .entry(*arg)
                        .or_default()
                        .push(manager.resolve_str(*constructor).to_string());
                }
                // Check for x = Constructor(...) - only collect when in positive
                // context; a negated equality is a DISequality.  No descent into the
                // operands either – see `collect_dt_constraints_v2` for why an
                // equality's children are a polarity boundary.
                TermKind::Eq(lhs, rhs) if in_positive_context => {
                    if let Some(rhs_data) = manager.get(*rhs) {
                        if let TermKind::DtConstructor { constructor, .. } = &rhs_data.kind {
                            if self.is_dt_variable(*lhs, manager) {
                                constructor_equalities
                                    .entry(*lhs)
                                    .or_default()
                                    .push(manager.resolve_str(*constructor).to_string());
                            }
                        }
                    }
                    if let Some(lhs_data) = manager.get(*lhs) {
                        if let TermKind::DtConstructor { constructor, .. } = &lhs_data.kind {
                            if self.is_dt_variable(*rhs, manager) {
                                constructor_equalities
                                    .entry(*rhs)
                                    .or_default()
                                    .push(manager.resolve_str(*constructor).to_string());
                            }
                        }
                    }
                }
                TermKind::And(_) | TermKind::Or(_) | TermKind::Not(_) => {
                    let children =
                        super::term_walk::asserted_children(&term_data.kind, in_positive_context);
                    worklist.extend(children.into_iter().rev());
                }
                _ => {}
            }
        }
    }

    /// Check if a term is a datatype variable
    fn is_dt_variable(&self, term: TermId, manager: &TermManager) -> bool {
        let Some(term_data) = manager.get(term) else {
            return false;
        };
        matches!(term_data.kind, TermKind::Var(_))
    }
}

#[cfg(test)]
mod tests {
    use super::Solver;
    use crate::prelude::*;
    use oxiz_core::ast::{TermId, TermKind, TermManager};
    use smallvec::smallvec;

    /// The four fact sets [`Solver::collect_dt_constraints_v2`] fills in.
    type DtFacts = (
        FxHashMap<TermId, Vec<String>>,
        FxHashMap<TermId, Vec<String>>,
        FxHashMap<TermId, Vec<String>>,
        Vec<(TermId, TermId)>,
    );

    /// Run the datatype collector over `assertions`.
    fn collect(manager: &TermManager, assertions: Vec<TermId>) -> DtFacts {
        let mut solver = Solver::new();
        solver.assertions = assertions;
        let mut testers = FxHashMap::default();
        let mut negative = FxHashMap::default();
        let mut equalities = FxHashMap::default();
        let mut var_equalities = Vec::new();
        solver.collect_dt_constraints_v2(
            manager,
            &mut testers,
            &mut negative,
            &mut equalities,
            &mut var_equalities,
        );
        (testers, negative, equalities, var_equalities)
    }

    /// A two-conjunct `And` that the builder cannot flatten into its parent.
    ///
    /// `mk_and` splices a nested `And` operand into the outer one, so it can
    /// never produce the *nesting* these tests need; `intern_term` is the
    /// public builder entry point that hands back exactly the node asked for.
    fn nested_and(manager: &mut TermManager, first: TermId, second: TermId) -> TermId {
        let bool_sort = manager.sorts.bool_sort;
        manager.intern_term(TermKind::And(smallvec![first, second]), bool_sort)
    }

    /// A conjunction hands every conjunct to the collector at positive
    /// polarity; a `Not` flips the polarity, so the tester underneath becomes a
    /// *negative* fact.
    #[test]
    fn conjuncts_are_collected_and_negation_flips_the_side() {
        let mut manager = TermManager::new();
        let list = manager.sorts.mk_datatype_sort("List");
        let x = manager.mk_var("x", list);
        let is_cons = manager.mk_dt_tester("cons", x);
        let is_nil = manager.mk_dt_tester("nil", x);
        let not_nil = manager.mk_not(is_nil);
        let assertion = manager.mk_and([is_cons, not_nil]);

        let (testers, negative, _, _) = collect(&manager, vec![assertion]);
        assert_eq!(testers.get(&x), Some(&vec!["cons".to_string()]));
        assert_eq!(negative.get(&x), Some(&vec!["nil".to_string()]));
    }

    /// The polarity boundaries: a tester inside one disjunct of an `Or` is
    /// conditional and must not be harvested, and a *negated* `And` may hand
    /// out nothing either – `(not (and a b))` is `(or (not a) (not b))`.
    #[test]
    fn conditional_testers_are_not_harvested() {
        let mut manager = TermManager::new();
        let list = manager.sorts.mk_datatype_sort("List");
        let bool_sort = manager.sorts.bool_sort;
        let x = manager.mk_var("x", list);
        let p = manager.mk_var("p", bool_sort);
        let is_cons = manager.mk_dt_tester("cons", x);

        let disjunction = manager.mk_or([is_cons, p]);
        let (testers, negative, _, _) = collect(&manager, vec![disjunction]);
        assert!(testers.is_empty());
        assert!(negative.is_empty());

        let conjunction = manager.mk_and([is_cons, p]);
        let negated = manager.mk_not(conjunction);
        let (testers, negative, _, _) = collect(&manager, vec![negated]);
        assert!(testers.is_empty());
        assert!(negative.is_empty());
    }

    /// `(not (or ((_ is cons) x) p))` *is* `(and (not ..) (not p))`, so the
    /// tester underneath is entailed – negatively.
    #[test]
    fn negated_disjunction_entails_its_disjuncts_negatively() {
        let mut manager = TermManager::new();
        let list = manager.sorts.mk_datatype_sort("List");
        let bool_sort = manager.sorts.bool_sort;
        let x = manager.mk_var("x", list);
        let p = manager.mk_var("p", bool_sort);
        let is_cons = manager.mk_dt_tester("cons", x);
        let disjunction = manager.mk_or([is_cons, p]);
        let negated = manager.mk_not(disjunction);

        let (testers, negative, _, _) = collect(&manager, vec![negated]);
        assert!(testers.is_empty());
        assert_eq!(negative.get(&x), Some(&vec!["cons".to_string()]));
    }

    /// Assertions and conjuncts alike are visited left to right.  The order is
    /// load-bearing: the mutual-exclusivity check compares `testers[0]` against
    /// every later entry.
    #[test]
    fn facts_are_recorded_in_source_order() {
        let mut manager = TermManager::new();
        let list = manager.sorts.mk_datatype_sort("List");
        let x = manager.mk_var("x", list);
        let cons = manager.mk_dt_tester("cons", x);
        let nil = manager.mk_dt_tester("nil", x);
        let leaf = manager.mk_dt_tester("leaf", x);
        let node = manager.mk_dt_tester("node", x);

        // `(and cons (and nil leaf))`, kept nested, then a second assertion.
        let inner = nested_and(&mut manager, nil, leaf);
        let first = nested_and(&mut manager, cons, inner);

        let (testers, _, _, _) = collect(&manager, vec![first, node]);
        assert_eq!(
            testers.get(&x),
            Some(&vec![
                "cons".to_string(),
                "nil".to_string(),
                "leaf".to_string(),
                "node".to_string(),
            ])
        );
    }

    /// A deeply nested conjunction is walked on the heap, not the native stack,
    /// and still collects exactly the fact at the bottom of it.
    #[test]
    fn deeply_nested_conjunction_walks_on_a_worker_stack() {
        // Stack and depth scale together (1 MiB/200k -> 128 KiB/25k): the
        // ~5 B-per-frame threshold is the pin, so never raise one alone.
        const DEPTH: usize = 25_000;

        let (testers, negative) = std::thread::Builder::new()
            .stack_size(1 << 17)
            .spawn(|| {
                let mut manager = TermManager::new();
                let list = manager.sorts.mk_datatype_sort("List");
                let bool_sort = manager.sorts.bool_sort;
                let x = manager.mk_var("x", list);
                let filler = manager.mk_var("p", bool_sort);
                let mut chain = manager.mk_dt_tester("cons", x);
                for _ in 0..DEPTH {
                    chain = nested_and(&mut manager, chain, filler);
                }
                let (testers, negative, _, _) = collect(&manager, vec![chain]);
                (testers.get(&x).cloned(), negative.len())
            })
            .expect("spawn worker thread")
            .join()
            .expect("worker thread must return, not abort");

        assert_eq!(testers, Some(vec!["cons".to_string()]));
        assert_eq!(negative, 0);
    }

    /// The two fact sets the legacy v1 collector fills in.
    type DtFactsV1 = (
        FxHashMap<TermId, Vec<String>>,
        FxHashMap<TermId, Vec<String>>,
    );

    /// Run the legacy v1 collector over a single term.
    fn collect_v1(manager: &TermManager, term: TermId) -> DtFactsV1 {
        let solver = Solver::new();
        let mut testers = FxHashMap::default();
        let mut equalities = FxHashMap::default();
        solver.collect_dt_constraints(term, manager, &mut testers, &mut equalities);
        (testers, equalities)
    }

    /// The v1 collector's polarity semantics survive the iterative rewrite:
    /// positive testers and constructor equalities are harvested in source
    /// order, a tester reached at negative polarity is *dropped* (v1 has no
    /// negative-tester map), and a negated `And` entails neither conjunct.
    #[test]
    fn v1_collector_keeps_polarity_semantics_and_order() {
        let mut manager = TermManager::new();
        let list = manager.sorts.mk_datatype_sort("List");
        let x = manager.mk_var("x", list);
        let y = manager.mk_var("y", list);
        let is_cons = manager.mk_dt_tester("cons", x);
        let is_nil = manager.mk_dt_tester("nil", x);

        // Positive facts, nested: testers come out left to right, duplicates
        // and all – each occurrence contributes.
        let inner = nested_and(&mut manager, is_nil, is_cons);
        let both = nested_and(&mut manager, is_cons, inner);
        let (testers, _) = collect_v1(&manager, both);
        assert_eq!(
            testers.get(&x),
            Some(&vec![
                "cons".to_string(),
                "nil".to_string(),
                "cons".to_string(),
            ])
        );

        // `(not (or (is cons x) (is nil x)))` reaches both testers at negative
        // polarity; v1 records nothing for them.
        let disjunction = manager.mk_or([is_cons, is_nil]);
        let negated_or = manager.mk_not(disjunction);
        let (testers, _) = collect_v1(&manager, negated_or);
        assert!(testers.is_empty());

        // A negated `And` is a disjunction and entails neither conjunct.
        let conjunction = manager.mk_and([is_cons, is_nil]);
        let negated_and = manager.mk_not(conjunction);
        let (testers, _) = collect_v1(&manager, negated_and);
        assert!(testers.is_empty());

        // `y = (cons ...)` is harvested at positive polarity only; under a
        // `Not` it is a disequality and yields no constructor fact.
        let value = manager.mk_dt_constructor("cons", [x], list);
        let equality = manager.mk_eq(y, value);
        let (_, equalities) = collect_v1(&manager, equality);
        assert_eq!(equalities.get(&y), Some(&vec!["cons".to_string()]));
        let negated_eq = manager.mk_not(equality);
        let (_, equalities) = collect_v1(&manager, negated_eq);
        assert!(equalities.is_empty());
    }

    /// The legacy v1 collector walks a deeply nested conjunction on the heap
    /// too – returning at all on a 128 KiB stack is the proof, since its old
    /// recursive descent aborted the process on inputs this deep.
    #[test]
    fn v1_collector_walks_deep_nesting_on_a_worker_stack() {
        // Stack and depth scale together (1 MiB/200k -> 128 KiB/25k): the
        // ~5 B-per-frame threshold is the pin, so never raise one alone.
        const DEPTH: usize = 25_000;

        let (testers, equality_count) = std::thread::Builder::new()
            .stack_size(1 << 17)
            .spawn(|| {
                let mut manager = TermManager::new();
                let list = manager.sorts.mk_datatype_sort("List");
                let bool_sort = manager.sorts.bool_sort;
                let x = manager.mk_var("x", list);
                let filler = manager.mk_var("p", bool_sort);
                let mut chain = manager.mk_dt_tester("cons", x);
                for _ in 0..DEPTH {
                    chain = nested_and(&mut manager, chain, filler);
                }
                let (testers, equalities) = collect_v1(&manager, chain);
                (testers.get(&x).cloned(), equalities.len())
            })
            .expect("spawn worker thread")
            .join()
            .expect("worker thread must return, not abort");

        assert_eq!(testers, Some(vec!["cons".to_string()]));
        assert_eq!(equality_count, 0);
    }
}
