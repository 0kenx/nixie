//! SAT values of Boolean theory arguments belong to EUF's two-element domain.

use super::{Polarity, TheoryManager};
use nixie_core::ast::TermKind;
use nixie_sat::TheoryCheckResult;

impl TheoryManager<'_> {
    pub(super) fn share_boolean_values_with_euf(&mut self) -> Option<TheoryCheckResult> {
        if !self.euf.has_app_nodes() {
            return None;
        }
        let mut arguments: Vec<_> = self
            .euf
            .app_argument_terms()
            .into_iter()
            .filter(|&term| {
                self.manager
                    .get(term)
                    .is_some_and(|node| node.sort == self.manager.sorts.bool_sort)
            })
            .collect();
        arguments.sort_unstable();
        for term in arguments {
            let constant = match self.manager.get(term).map(|n| &n.kind) {
                Some(TermKind::True) => Some(true),
                Some(TermKind::False) => Some(false),
                _ => None,
            };
            let (value, reason) = if let Some(value) = constant {
                self.tautological_reasons.insert(term);
                (value, term)
            } else {
                let Some(&(lit, Polarity::Both)) =
                    self.boolean_encodings.and_then(|m| m.get(&term))
                else {
                    self.resource_exhausted = true;
                    return Some(TheoryCheckResult::Sat);
                };
                let Some(assigned) = self.assigned_pol_of(lit.var()) else {
                    self.resource_exhausted = true;
                    return Some(TheoryCheckResult::Sat);
                };
                let Some(&reason) = self.var_to_term.get(lit.var().index()) else {
                    self.resource_exhausted = true;
                    return Some(TheoryCheckResult::Sat);
                };
                (assigned != lit.is_neg(), reason)
            };
            let node = self.intern_term_for_congruence(term, self.manager);
            let (t, f) = self.ensure_bool_nodes();
            let target = if value { t } else { f };
            if !self.euf.are_equal(node, target) && self.euf.merge(node, target, reason).is_err() {
                self.resource_exhausted = true;
                return Some(TheoryCheckResult::Sat);
            }
            if let Some(terms) = self.euf.check_conflicts() {
                return Some(self.conflict_from_terms(&terms));
            }
        }
        None
    }
}
