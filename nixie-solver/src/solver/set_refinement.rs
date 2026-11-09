//! Refine membership congruence for element equalities introduced after set reduction.
//!
//! CVC5 registers SET_MEMBER with its equality engine (theory_sets.cpp).
//! Our assert-time reduction cannot anticipate later datatype/theory equalities.
//! At a candidate, opposite membership values require their elements to differ;
//! assert the guarded congruence theorem and let the owning theories decide it.

use super::Solver;
#[allow(unused_imports)]
use crate::prelude::*;
use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_sat::LBool;

#[derive(Default)]
struct MembershipPartition {
    positive: Vec<(TermId, TermId)>,
    negative: Vec<(TermId, TermId)>,
}

impl Solver {
    /// `Err` means the deterministic scan budget was exhausted: no Sat claim.
    pub(super) fn refine_set_membership(&mut self, manager: &mut TermManager) -> Result<bool, ()> {
        if !self.has_set_or_bag_terms {
            return Ok(false);
        }
        let mut by_set: BTreeMap<TermId, MembershipPartition> = BTreeMap::new();
        for (&atom, &var) in &self.term_to_var {
            let Some(TermKind::SetMember(element, set)) = manager.get(atom).map(|n| &n.kind) else {
                continue;
            };
            match self.sat.model_value(var) {
                LBool::True => by_set
                    .entry(*set)
                    .or_default()
                    .positive
                    .push((*element, atom)),
                LBool::False => by_set
                    .entry(*set)
                    .or_default()
                    .negative
                    .push((*element, atom)),
                LBool::Undef => {}
            }
        }
        // Collect before encoding anything: installing a lemma can backtrack
        // the candidate, whose membership assignment must remain one snapshot.
        let mut candidates = Vec::new();
        for (
            _,
            MembershipPartition {
                mut positive,
                mut negative,
            },
        ) in by_set
        {
            positive.sort_unstable();
            negative.sort_unstable();
            for &(x, mx) in &positive {
                for &(y, my) in &negative {
                    if candidates.len() >= 20_000 {
                        return Err(());
                    }
                    candidates.push((x, y, mx, my));
                }
            }
        }
        let mut lemmas = Vec::new();
        for (x, y, mx, my) in candidates {
            let same = manager.mk_eq(x, y);
            if same == manager.false_id
                || self
                    .term_to_var
                    .get(&same)
                    .is_some_and(|&var| self.sat.model_value(var) == LBool::False)
            {
                continue;
            }
            let agrees = manager.mk_eq(mx, my);
            let lemma = manager.mk_implies(same, agrees);
            if lemma == manager.true_id
                || self
                    .term_to_var
                    .get(&lemma)
                    .is_some_and(|&var| self.sat.model_value(var) == LBool::True)
            {
                continue;
            }
            lemmas.push(lemma);
        }
        for &lemma in &lemmas {
            let lit = self.encode(lemma, manager);
            self.sat.add_clause([lit]);
        }
        // Clauses and encode's memo use the ordinary assertion-scope journals.
        // No independent cache can survive a pop and suppress re-instantiation.
        Ok(!lemmas.is_empty())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SolverResult;
    use nixie_core::sort::DataTypeConstructor;
    use smallvec::smallvec;

    #[test]
    fn a_late_element_equality_cannot_disagree_on_membership_after_pop() {
        let mut m = TermManager::new();
        let sort = m.sorts.mk_datatype_sort("Color");
        let cs = ["red", "blue"].map(|name| DataTypeConstructor {
            name: m.intern_str(name),
            selectors: smallvec![],
        });
        m.declare_datatype("Color", cs.to_vec());
        let x = m.mk_var("x", sort);
        let y = m.mk_var("y", sort);
        let middle = m.mk_var("middle", sort);
        let set_sort = m.sorts.set(sort);
        let set = m.mk_var("s", set_sort);
        let mx = m.mk_set_member(x, set);
        let my = m.mk_set_member(y, set);
        let not_my = m.mk_not(my);
        let mut solver = Solver::new();
        solver.assert(mx, &mut m);
        solver.assert(not_my, &mut m);
        assert_eq!(solver.check(&mut m), SolverResult::Sat);
        for _ in 0..2 {
            solver.push();
            // Deliberately bypass assert-time set reduction, just as a theory
            // lemma created while checking does.
            for (left, right) in [(x, middle), (middle, y)] {
                let same = m.mk_eq(left, right);
                let lit = solver.encode(same, &mut m);
                solver.sat.add_clause([lit]);
            }
            solver.invalidate_results();
            assert_eq!(solver.check(&mut m), SolverResult::Unsat);
            solver.pop();
            assert_eq!(solver.check(&mut m), SolverResult::Sat);
        }
    }
}
