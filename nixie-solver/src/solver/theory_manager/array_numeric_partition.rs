//! Check the whole numeric arrangement that an array candidate relies on.

use super::*;
use num_rational::BigRational;

impl TheoryManager<'_> {
    fn exact_interface_value(&self, term: TermId) -> Option<BigRational> {
        let node = self.manager.get(term)?;
        if node.sort != self.manager.sorts.int_sort && node.sort != self.manager.sorts.real_sort {
            return None;
        }
        match &node.kind {
            TermKind::IntConst(v) => Some(BigRational::from_integer(v.clone())),
            TermKind::RealConst(v) => {
                Some(BigRational::new((*v.numer()).into(), (*v.denom()).into()))
            }
            _ => self.arith.value_exact(term),
        }
    }

    /// Model-equal arguments may be merged only as a temporary candidate.
    /// Ask CDCL for care splits if that partition conflicts, disagrees with
    /// numeric results, or induces new array equalities whose read consequences
    /// have not been refined. Compatible scalar partitions need no extra atoms.
    pub(super) fn check_array_numeric_partition(&mut self) {
        let mut terms: Vec<_> = self.euf.app_argument_terms().into_iter().collect();
        terms.sort_unstable();
        let mut groups: FxHashMap<(BigRational, nixie_core::SortId), TermId> = FxHashMap::default();
        let mut pairs = Vec::new();
        for term in terms {
            let Some(node) = self.manager.get(term) else {
                continue;
            };
            if node.sort != self.manager.sorts.int_sort && node.sort != self.manager.sorts.real_sort
            {
                continue;
            }
            let Some(value) = self.exact_interface_value(term) else {
                continue;
            };
            let Some(first) = groups.get(&(value.clone(), node.sort)).copied() else {
                groups.insert((value, node.sort), term);
                continue;
            };
            let (Some(a), Some(b)) = (self.euf.term_to_node(first), self.euf.term_to_node(term))
            else {
                continue;
            };
            if !self.euf.are_equal_immutable(a, b) {
                pairs.push((first, term));
            }
        }
        if pairs.is_empty() {
            return;
        }
        // Before/after class comparison keeps array equality obligations out
        // of a scratch scope: the ordinary array refinement must see them.
        let array_classes: Vec<_> = self
            .euf
            .all_node_indices()
            .filter_map(|node| {
                let term = self.euf.node_term(node)?;
                let sort = self.manager.sorts.get(self.manager.get(term)?.sort)?;
                if matches!(sort.kind, nixie_core::SortKind::Array { .. }) {
                    Some((node, self.euf.find_immutable(node)))
                } else {
                    None
                }
            })
            .collect();
        self.euf.push();
        let mut needs_split = false;
        for &(a, b) in &pairs {
            let (Some(na), Some(nb)) = (self.euf.term_to_node(a), self.euf.term_to_node(b)) else {
                needs_split = true;
                break;
            };
            if self.euf.merge(na, nb, b).is_err() {
                needs_split = true;
                break;
            }
        }
        if self.euf.check_conflicts().is_some() {
            needs_split = true;
        }
        let mut array_witness = FxHashMap::default();
        for (node, old_class) in array_classes {
            if needs_split {
                break;
            }
            let class = self.euf.find_immutable(node);
            if let Some(old) = array_witness.insert(class, old_class)
                && old != old_class
            {
                needs_split = true;
            }
        }
        let mut numeric_witness: FxHashMap<u32, BigRational> = FxHashMap::default();
        let nodes: Vec<_> = self.euf.all_node_indices().collect();
        for node in nodes {
            if needs_split {
                break;
            }
            let Some(term) = self.euf.node_term(node) else {
                continue;
            };
            let Some(value) = self.exact_interface_value(term) else {
                continue;
            };
            let class = self.euf.find_immutable(node);
            if let Some(old) = numeric_witness.insert(class, value.clone())
                && old != value
            {
                needs_split = true;
            }
        }
        self.euf.pop();
        if needs_split {
            self.arrangement_splits.extend(pairs);
        }
    }
}
