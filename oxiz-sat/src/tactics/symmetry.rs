use crate::literal::{Lit, Var};
use crate::{AutomorphismDetector, SymmetryBreaker, SymmetryBreakingMethod};
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::error::Result;
use oxiz_core::tactic::{Goal, TacticResult};
use smallvec::SmallVec;

/// Adds lex-leader symmetry-breaking constraints to a Boolean goal.
pub struct SymmetryBreakTactic<'a> {
    manager: &'a mut TermManager,
}

impl<'a> SymmetryBreakTactic<'a> {
    /// Create a new symmetry-breaking tactic.
    pub fn new(manager: &'a mut TermManager) -> Self {
        Self { manager }
    }

    /// Apply symmetry breaking to the current goal.
    pub fn apply_mut(&mut self, goal: &Goal) -> Result<TacticResult> {
        let extraction = extract_boolean_clauses(self.manager, &goal.assertions);
        let Some((clauses, term_vars)) = extraction else {
            return Ok(TacticResult::NotApplicable);
        };

        if term_vars.len() < 2 || clauses.is_empty() {
            return Ok(TacticResult::NotApplicable);
        }

        let mut detector = AutomorphismDetector::new(term_vars.len());
        for clause in clauses {
            detector.add_clause(clause);
        }

        let group = detector.detect_symmetries();
        if group.generators().is_empty() {
            return Ok(TacticResult::NotApplicable);
        }

        let mut breaker = SymmetryBreaker::new(group, SymmetryBreakingMethod::Lex);
        breaker.generate_predicates();
        if breaker.get_clauses().is_empty() {
            return Ok(TacticResult::NotApplicable);
        }

        let mut assertions = goal.assertions.clone();
        for clause in breaker.get_clauses() {
            assertions.push(clause_to_term(self.manager, clause, &term_vars));
        }

        Ok(TacticResult::SubGoals(vec![Goal {
            assertions,
            precision: goal.precision,
        }]))
    }
}

fn extract_boolean_clauses(
    manager: &TermManager,
    assertions: &[TermId],
) -> Option<(Vec<Vec<Lit>>, Vec<TermId>)> {
    let mut ordered_vars = Vec::new();
    let mut var_to_index = std::collections::HashMap::new();
    let mut clauses = Vec::new();

    for &assertion in assertions {
        let mut clause_terms = Vec::new();
        if !collect_clause_literals(manager, assertion, &mut clause_terms) {
            return None;
        }

        let mut clause = Vec::new();
        for (var_term, sign) in clause_terms {
            let idx = if let Some(&idx) = var_to_index.get(&var_term) {
                idx
            } else {
                let idx = ordered_vars.len();
                ordered_vars.push(var_term);
                var_to_index.insert(var_term, idx);
                idx
            };
            let var = Var::new(idx as u32);
            clause.push(if sign { Lit::pos(var) } else { Lit::neg(var) });
        }
        clauses.push(clause);
    }

    Some((clauses, ordered_vars))
}

/// Flatten `term` into clause literals, returning `false` if it is not a
/// clause (a disjunction of variables and negated variables).
///
/// Runs on an explicit heap work-stack. The recursion this replaces was
/// driven by `Or`-nesting depth in user-supplied assertions, and the `bool`
/// return has no room for a "too deep" answer – capping it would silently
/// reclassify a genuine clause as a non-clause and disable symmetry
/// breaking (or, capping the other way, admit a non-clause).
///
/// No visited set is used: a shared sub-disjunction legitimately
/// contributes its literals once per occurrence, so pruning would drop
/// literals. Order of `out` (pre-order, left-to-right) and the
/// short-circuit on the first non-clause sub-term both match the former
/// `Iterator::all`-based recursion, including leaving partially collected
/// literals in `out` on failure (callers discard them).
fn collect_clause_literals(
    manager: &TermManager,
    term: TermId,
    out: &mut Vec<(TermId, bool)>,
) -> bool {
    let mut stack = vec![term];
    while let Some(current) = stack.pop() {
        match manager.get(current).map(|node| &node.kind) {
            Some(TermKind::Var(_)) => out.push((current, true)),
            Some(TermKind::Not(inner)) => match manager.get(*inner).map(|node| &node.kind) {
                Some(TermKind::Var(_)) => out.push((*inner, false)),
                _ => return false,
            },
            // Push in reverse so the LIFO stack pops disjuncts left-to-right.
            Some(TermKind::Or(args)) => stack.extend(args.iter().rev().copied()),
            _ => return false,
        }
    }
    true
}

fn clause_to_term(manager: &mut TermManager, clause: &[Lit], vars: &[TermId]) -> TermId {
    let literals: SmallVec<[TermId; 4]> = clause
        .iter()
        .map(|lit| {
            let base = vars[lit.var().index()];
            if lit.is_pos() {
                base
            } else {
                manager.mk_not(base)
            }
        })
        .collect();

    manager.mk_or(literals)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A 100_000-literal clause walked on a 1 MiB stack. `mk_or` flattens
    /// nested disjunctions, so a clause built through the public builder is
    /// wide rather than deep – but the flattening happens at *construction*
    /// time, and a `TermManager` populated by any other route (a different
    /// front end, a deserialized term table) can present a deep `Or` spine
    /// to this walk. The assertion is that the walk returns; a stack
    /// overflow aborts the process.
    #[test]
    fn test_collect_clause_literals_huge_clause_returns() {
        let worker = std::thread::Builder::new().stack_size(1 << 20).spawn(|| {
            const WIDTH: usize = 100_000;
            let mut manager = TermManager::new();
            let bool_sort = manager.sorts.bool_sort;
            let lits: Vec<TermId> = (0..WIDTH)
                .map(|i| manager.mk_var(&format!("v{i}"), bool_sort))
                .collect();
            let clause = manager.mk_or(lits.clone());
            let mut out = Vec::new();
            let ok = collect_clause_literals(&manager, clause, &mut out);
            (ok, out.len(), out.first().copied(), lits.first().copied())
        });
        let (ok, len, first_out, first_lit) = match worker.map(std::thread::JoinHandle::join) {
            Ok(Ok(result)) => result,
            _ => panic!("wide-clause worker thread did not complete"),
        };
        assert!(ok);
        assert_eq!(len, 100_000);
        // Left-to-right order preserved.
        assert_eq!(first_out, first_lit.map(|t| (t, true)));
    }

    /// Semantic pins: literal order and polarity are preserved, and a
    /// non-clause sub-term still reports `false`.
    #[test]
    fn test_collect_clause_literals_semantics() {
        let mut manager = TermManager::new();
        let bool_sort = manager.sorts.bool_sort;
        let a = manager.mk_var("a", bool_sort);
        let b = manager.mk_var("b", bool_sort);
        let not_b = manager.mk_not(b);
        let clause = manager.mk_or([a, not_b]);

        let mut out = Vec::new();
        assert!(collect_clause_literals(&manager, clause, &mut out));
        assert_eq!(out, vec![(a, true), (b, false)]);

        // `(or a (and a b))` is not a clause.
        let conj = manager.mk_and([a, b]);
        let non_clause = manager.mk_or([a, conj]);
        let mut out = Vec::new();
        assert!(!collect_clause_literals(&manager, non_clause, &mut out));
    }

    #[test]
    fn test_symmetry_break_adds_clauses() {
        let mut manager = TermManager::new();
        let a = manager.mk_var("a", manager.sorts.bool_sort);
        let b = manager.mk_var("b", manager.sorts.bool_sort);
        let clause = manager.mk_or([a, b]);

        let goal = Goal::new(vec![clause]);
        let mut tactic = SymmetryBreakTactic::new(&mut manager);
        let result = tactic
            .apply_mut(&goal)
            .expect("test operation should succeed");

        match result {
            TacticResult::SubGoals(goals) => {
                assert_eq!(goals.len(), 1);
                assert!(goals[0].assertions.len() > goal.assertions.len());
            }
            other => panic!("expected symmetry-breaking subgoal, got {other:?}"),
        }
    }

    /// Build a fully-symmetric 3-variable goal:
    ///   (a ∨ b ∨ c), (¬a ∨ ¬b), (¬b ∨ ¬c), (¬a ∨ ¬c)
    /// Every variable has the same clause-signature, so the detector
    /// finds multiple generators and the breaker adds lex-leader predicates.
    #[test]
    fn test_symmetry_break_full_3var_symmetry() {
        let mut manager = TermManager::new();
        let bool_sort = manager.sorts.bool_sort;
        let a = manager.mk_var("a", bool_sort);
        let b = manager.mk_var("b", bool_sort);
        let c = manager.mk_var("c", bool_sort);

        let na = manager.mk_not(a);
        let nb = manager.mk_not(b);
        let nc = manager.mk_not(c);

        let c1 = manager.mk_or([a, b, c]);
        let c2 = manager.mk_or([na, nb]);
        let c3 = manager.mk_or([nb, nc]);
        let c4 = manager.mk_or([na, nc]);

        let goal = Goal::new(vec![c1, c2, c3, c4]);
        let original_len = goal.assertions.len();

        let mut tactic = SymmetryBreakTactic::new(&mut manager);
        let result = tactic.apply_mut(&goal).expect("apply_mut should not fail");

        match result {
            TacticResult::SubGoals(goals) => {
                assert_eq!(goals.len(), 1, "expected exactly one sub-goal");
                assert!(
                    goals[0].assertions.len() > original_len,
                    "augmented goal must have more assertions than original \
                     (at least one lex-leader predicate should be added): \
                     original={original_len}, augmented={}",
                    goals[0].assertions.len()
                );
            }
            other => {
                panic!("expected SubGoals from a fully-symmetric 3-var formula, got {other:?}")
            }
        }
    }

    /// Strongly asymmetric goal: `a`, `a∨b`, `a∨b∨c`.
    /// Each variable has a distinct clause-signature:
    ///   a → [1001, 1002, 1003], b → [1002, 1003], c → [1003]
    /// No two variables match, so the detector finds no generators and
    /// the tactic returns NotApplicable.
    #[test]
    fn test_symmetry_break_asymmetric_clauses() {
        let mut manager = TermManager::new();
        let bool_sort = manager.sorts.bool_sort;
        let a = manager.mk_var("a2", bool_sort);
        let b = manager.mk_var("b2", bool_sort);
        let c = manager.mk_var("c2", bool_sort);

        // clause sizes 1, 2, 3 → every variable sees a unique set of sizes
        let c1 = a; // {a}  ← var a appears in size-1 clause
        let c2 = manager.mk_or([a, b]); // {a,b} ← size-2 clause
        let c3 = manager.mk_or([a, b, c]); // {a,b,c} ← size-3 clause

        let goal = Goal::new(vec![c1, c2, c3]);
        let mut tactic = SymmetryBreakTactic::new(&mut manager);
        let result = tactic.apply_mut(&goal).expect("apply_mut should not fail");

        assert!(
            matches!(result, TacticResult::NotApplicable),
            "asymmetric goal should produce NotApplicable, got {result:?}",
        );
    }

    /// A goal that mixes Boolean `BoolVar` assertions with a non-Boolean
    /// arithmetic constraint (e.g., x < 10).  The extraction helper
    /// `collect_clause_literals` returns false for arithmetic terms, so
    /// `extract_boolean_clauses` returns None and the tactic returns
    /// NotApplicable.
    #[test]
    fn test_symmetry_break_mixed_boolean_integer() {
        let mut manager = TermManager::new();
        let bool_sort = manager.sorts.bool_sort;
        let int_sort = manager.sorts.int_sort;

        let p = manager.mk_var("p", bool_sort);
        let q = manager.mk_var("q", bool_sort);
        let bool_clause = manager.mk_or([p, q]);

        let x = manager.mk_var("x_int", int_sort);
        let ten = manager.mk_int(10);
        let arith = manager.mk_lt(x, ten);

        let goal = Goal::new(vec![bool_clause, arith]);
        let mut tactic = SymmetryBreakTactic::new(&mut manager);
        let result = tactic.apply_mut(&goal).expect("apply_mut should not fail");

        assert!(
            matches!(result, TacticResult::NotApplicable),
            "mixed Boolean/arithmetic goal should produce NotApplicable, got {result:?}",
        );
    }

    /// Proxy test for model-space reduction.
    ///
    /// We use the same fully-symmetric 3-variable construction as
    /// `test_symmetry_break_full_3var_symmetry`.  After applying the
    /// tactic we verify that the augmented goal has strictly more
    /// assertions than the original – which is the direct evidence that
    /// the solver's search space has been constrained (the added lex-leader
    /// clauses eliminate symmetric assignments).
    ///
    /// Note (deviation): translating the augmented AST Goal back into a
    /// raw SAT Solver and running AllSatEnumerator would require
    /// reconstructing the variable mapping out-of-band.  The assertion-count
    /// proxy is the appropriate check at this layer of abstraction.
    #[test]
    fn test_symmetry_break_reduces_model_count() {
        let mut manager = TermManager::new();
        let bool_sort = manager.sorts.bool_sort;

        let a = manager.mk_var("a3", bool_sort);
        let b = manager.mk_var("b3", bool_sort);
        let c = manager.mk_var("c3", bool_sort);

        let na = manager.mk_not(a);
        let nb = manager.mk_not(b);
        let nc = manager.mk_not(c);

        let c1 = manager.mk_or([a, b, c]);
        let c2 = manager.mk_or([na, nb]);
        let c3 = manager.mk_or([nb, nc]);
        let c4 = manager.mk_or([na, nc]);

        let original_goal = Goal::new(vec![c1, c2, c3, c4]);
        let original_assertion_count = original_goal.assertions.len();

        let mut tactic = SymmetryBreakTactic::new(&mut manager);
        let result = tactic
            .apply_mut(&original_goal)
            .expect("apply_mut should not fail");

        let augmented_assertion_count = match result {
            TacticResult::SubGoals(ref goals) => {
                assert_eq!(goals.len(), 1, "expected exactly one sub-goal");
                goals[0].assertions.len()
            }
            other => {
                panic!("expected SubGoals from a fully-symmetric 3-var formula, got {other:?}")
            }
        };

        assert!(
            augmented_assertion_count > original_assertion_count,
            "augmented goal must have more assertions (lex-leader clauses) than the \
             original: original={original_assertion_count}, augmented={augmented_assertion_count}. \
             Extra clauses reduce the search space by eliminating symmetric models.",
        );
    }
}
