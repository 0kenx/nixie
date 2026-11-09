//! Shared preparation of closed quantifier obligations.
//!
//! Guards define an equisatisfiable extension, so their obligations are
//! unconditional derived assertions. They never enter the user's assertion
//! list. A worklist handles newly closed nested binders without native recursion.

use super::{Solver, binder_row, finite_expand, quant_guard};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::solver::trail::TrailOp;
use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::sort::SortKind;

impl Solver {
    pub(in crate::solver) fn guard_conditional_quantifiers(
        &mut self,
        term: TermId,
        manager: &mut TermManager,
    ) -> (TermId, Vec<TermId>) {
        let guarded =
            quant_guard::guard_conditional_quantifiers(term, manager, &mut self.next_skolem_id);
        match guarded {
            Some(guarded) => (guarded.term, guarded.obligations),
            None => (term, Vec::new()),
        }
    }

    pub(in crate::solver) fn assert_quantifier_obligations(
        &mut self,
        obligations: Vec<TermId>,
        manager: &mut TermManager,
    ) {
        let mut pending: Vec<_> = obligations
            .into_iter()
            .rev()
            .map(|term| (term, 0, true))
            .collect();
        let mut processed = 0usize;
        while let Some((term, depth, expand_row)) = pending.pop() {
            processed += 1;
            if processed > 4096 {
                self.encode_depth_exceeded = true;
                break;
            }
            // A missing definition would leave the fresh guard unconstrained.
            if depth >= 64 || self.term_exceeds_encode_depth(term, manager) {
                self.encode_depth_exceeded = true;
                continue;
            }
            if expand_row && let Some(row) = self.binder_row_lemma(term, manager) {
                pending.push((row, depth, false));
            }
            let expanded = self.finite_expand_assertion(term, manager).unwrap_or(term);
            let prepared = self.skolemize_asserted_existentials(expanded, manager);
            let (prepared, nested) = self.guard_conditional_quantifiers(prepared, manager);
            let prepared = self.eliminate_nonbool_ite(prepared, manager);
            let prepared = self.abstract_compound_bool_args(prepared, manager);
            let prepared = self.purify_numeric_uf_args(prepared, manager);
            self.register_asserted_quantifiers(prepared, manager);
            self.emit_assertion_clauses(prepared, manager);
            self.link_or_blast_bv_circuits(prepared, manager);
            self.add_arith_diseq_split(prepared, manager);
            pending.extend(nested.into_iter().rev().map(|term| (term, depth + 1, true)));
        }
    }

    pub(super) fn binder_row_lemma(
        &mut self,
        term: TermId,
        manager: &mut TermManager,
    ) -> Option<TermId> {
        if !finite_expand::contains_quantifier(term, manager) {
            return None;
        }
        binder_row::expand_reads_over_writes_under_binders(term, manager)
    }

    /// Preserve a conditional instance's outer guard. Only its definitions
    /// are unconditional; even a top-level binder inside that instance must
    /// be represented by a fresh guard rather than registered as a fact.
    pub(in crate::solver) fn prepare_ground_instance(
        &mut self,
        term: TermId,
        conditional: bool,
        manager: &mut TermManager,
    ) -> TermId {
        let key = (term, conditional);
        if let Some(&prepared) = self.prepared_ground_instances.get(&key) {
            return prepared;
        }
        let mut prepared = self.eliminate_nonbool_ite(term, manager);
        if finite_expand::contains_quantifier(prepared, manager) {
            prepared = self
                .finite_expand_assertion(prepared, manager)
                .unwrap_or(prepared);
            if !conditional {
                prepared = self.skolemize_asserted_existentials(prepared, manager);
            }
            let guarded = quant_guard::guard_quantifiers(
                prepared,
                manager,
                &mut self.next_skolem_id,
                conditional,
            );
            if let Some(guarded) = guarded {
                prepared = guarded.term;
                self.assert_quantifier_obligations(guarded.obligations, manager);
            }
            if !conditional {
                self.register_asserted_quantifiers(prepared, manager);
            } else if finite_expand::contains_quantifier(prepared, manager) {
                // A cap or an enclosing binder prevented a complete guard.
                self.unowned_quantifier_seen = true;
            }
            self.prepared_ground_instances.insert(key, prepared);
            self.trail
                .push(TrailOp::GroundInstancePrepared { term, conditional });
        }
        self.register_ground_instance_root(prepared, manager);
        prepared
    }

    pub(in crate::solver) fn seed_quantifier_domains(&mut self, manager: &mut TermManager) {
        if !self.has_quantifiers {
            return;
        }
        let mut stack = self.assertions.clone();
        let mut seen = FxHashSet::default();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            self.seed_binder_sort_witnesses(term, manager);
            if let Some(node) = manager.get(term) {
                stack.extend(nixie_core::ast::traversal::get_children(&node.kind));
            }
        }
    }

    /// Nonempty atomic domains need a ground inhabitant even when the source
    /// declares none. Infinite arithmetic domains retain their existing pools
    /// to avoid closing them under fresh arithmetic/function terms indefinitely.
    pub(super) fn seed_binder_sort_witnesses(
        &mut self,
        quantifier: TermId,
        manager: &mut TermManager,
    ) {
        let Some(node) = manager.get(quantifier) else {
            return;
        };
        let (TermKind::Forall { vars, .. } | TermKind::Exists { vars, .. }) = &node.kind else {
            return;
        };
        let sorts: Vec<_> = vars.iter().map(|&(_, sort)| sort).collect();
        for sort in sorts {
            if !matches!(
                manager.sorts.get(sort).map(|s| &s.kind),
                Some(
                    SortKind::Bool
                        | SortKind::BitVec(_)
                        | SortKind::RoundingMode
                        | SortKind::Uninterpreted(_)
                )
            ) || self.mbqi.has_candidate_of_sort(sort)
            {
                continue;
            }
            let Some(next) = self.next_skolem_id.checked_add(1) else {
                return;
            };
            let name =
                nixie_core::reserved::reserved_name("qwit", &self.next_skolem_id.to_string());
            self.next_skolem_id = next;
            let witness = manager.mk_var(&name, sort);
            self.mbqi.add_candidate(witness, sort);
        }
    }
}
