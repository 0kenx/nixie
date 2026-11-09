//! Explicit total choices for SMT-LIB's underspecified division by zero.
//! These are model proposals, never simplifications used to prove unsat.
use super::*;

impl Context {
    pub(super) fn repair_zero_division_publication(&mut self) -> bool {
        let mut stack = self.certified_goal();
        let mut seen = FxHashSet::default();
        let mut reads = Vec::new();
        let mut sorts = FxHashSet::default();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            let Some(node) = self.terms.get(term) else {
                return false;
            };
            if let TermKind::Div(_, denominator) = node.kind
                && literal_zero(denominator, &self.terms)
            {
                if node.sort != self.terms.sorts.int_sort && node.sort != self.terms.sorts.real_sort
                {
                    return false;
                }
                reads.push((term, node.sort));
                sorts.insert(node.sort);
            }
            stack.extend(nixie_core::ast::traversal::get_children(&node.kind));
        }
        if reads.is_empty() {
            return false;
        }
        for &sort in &sorts {
            let symbol = if sort == self.terms.sorts.int_sort {
                "div0"
            } else {
                "/0"
            };
            if self.declared_consts.iter().any(|d| d.name == symbol)
                || self.declared_funs.iter().any(|d| d.name == symbol)
            {
                return false;
            }
        }
        let saved = self.published.clone();
        let Some(mut model) = self.published_model().cloned() else {
            return false;
        };
        for (term, sort) in reads {
            let value = if sort == self.terms.sorts.int_sort {
                self.terms.mk_int(0)
            } else {
                self.terms
                    .mk_real(num_rational::Rational64::from_integer(0))
            };
            model.set(term, value);
        }
        self.published.model = Some(model);
        self.published.zero_division_sorts = sorts;
        if self.certify_printed_goal().is_ok() || self.repair_projected_functions() {
            return true;
        }
        self.published = saved;
        false
    }

    pub(super) fn fold_published_zero_division(&mut self, root: TermId) -> TermId {
        if self.published.zero_division_sorts.is_empty() {
            return root;
        }
        let mut stack = vec![root];
        let mut seen = FxHashSet::default();
        let mut replacements = FxHashMap::default();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            let Some(node) = self.terms.get(term) else {
                return root;
            };
            if let TermKind::Div(_, denominator) = node.kind
                && self.published.zero_division_sorts.contains(&node.sort)
                && literal_zero(denominator, &self.terms)
            {
                let value = if node.sort == self.terms.sorts.int_sort {
                    self.terms.mk_int(0)
                } else {
                    self.terms
                        .mk_real(num_rational::Rational64::from_integer(0))
                };
                replacements.insert(term, value);
            } else {
                stack.extend(nixie_core::ast::traversal::get_children(&node.kind));
            }
        }
        self.terms.substitute(root, &replacements)
    }
}

fn literal_zero(term: TermId, terms: &nixie_core::TermManager) -> bool {
    match terms.get(term).map(|t| &t.kind) {
        Some(TermKind::IntConst(n)) => n.is_zero(),
        Some(TermKind::RealConst(n)) => n.is_zero(),
        _ => false,
    }
}
