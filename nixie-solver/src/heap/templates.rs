//! Scope-independent expression memoization, never cached assumptions or clauses.

use super::*;
use rustc_hash::FxHashMap;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Key {
    Validity(Vec<TermId>),
    Coverage(Vec<(TermId, TermId)>, Vec<(TermId, TermId)>),
}

#[derive(Default)]
pub(super) struct Templates {
    terms: FxHashMap<Key, TermId>,
    pub(super) builds: usize,
    pub(super) hits: usize,
}

impl HeapSolver {
    fn template(&mut self, key: Key) -> TermId {
        if let Some(&term) = self.templates.terms.get(&key) {
            self.templates.hits += 1;
            if self.optimizations.cache_templates {
                return term;
            }
        }
        self.templates.builds += 1;
        let term = match &key {
            Key::Validity(locations) => {
                let zero = self.tm.mk_int(0);
                let mut valid = Vec::new();
                for (j, &location) in locations.iter().enumerate() {
                    let nil = self.tm.mk_eq(location, zero);
                    valid.push(self.tm.mk_not(nil));
                    for &other in &locations[..j] {
                        let alias = self.tm.mk_eq(location, other);
                        valid.push(self.tm.mk_not(alias));
                    }
                }
                self.tm.mk_and(valid)
            }
            Key::Coverage(cells, other) => {
                if cells.len() != other.len() {
                    self.tm.false_id
                } else {
                    let mut matches = Vec::new();
                    for &(location, value) in cells {
                        let mut choices = Vec::new();
                        for &(other_location, other_value) in other {
                            let address = self.tm.mk_eq(location, other_location);
                            let value = self.tm.mk_eq(value, other_value);
                            choices.push(self.tm.mk_and([address, value]));
                        }
                        matches.push(self.tm.mk_or(choices));
                    }
                    self.tm.mk_and(matches)
                }
            }
        };
        // Controls perform the same lookup/store, but recompute the expression.
        // The complete key uses current rewritten operands, not heaplet indices
        // or a scope-dependent equivalence class. TermManager IDs are permanent.
        self.templates.terms.insert(key, term);
        term
    }

    pub(super) fn heap_validity(&mut self, index: usize) -> TermId {
        let locations = self.spatial[index]
            .cells
            .iter()
            .map(|&(location, _)| self.definition_terms[location])
            .collect();
        self.template(Key::Validity(locations))
    }

    /// Equal-length directional membership. Without source validity this is
    /// NOT finite-map equality: a duplicate source can omit a destination cell.
    pub(super) fn same_heap(&mut self, i: usize, j: usize) -> TermId {
        self.heap_comparisons += 1;
        let cells = |index: usize| {
            self.spatial[index]
                .cells
                .iter()
                .map(|&(l, v)| (self.definition_terms[l], self.definition_terms[v]))
                .collect()
        };
        let key = Key::Coverage(cells(i), cells(j));
        self.template(key)
    }
}
