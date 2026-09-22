//! Exact, assertion-entailed substitutions used only in heap definitions.
//!
//! Original assertions and model evaluation are never replaced. Recompute this
//! mapping per private definition scope, so no equality survives a user pop.

use super::*;
use nixie_core::ast::TermKind;
use rustc_hash::FxHashMap;

struct Classes {
    parent: Vec<usize>,
    constants: Vec<Option<BigInt>>,
}

impl Classes {
    fn root(&mut self, index: usize) -> usize {
        let mut root = index;
        while self.parent[root] != root {
            root = self.parent[root];
        }
        let mut current = index;
        while self.parent[current] != current {
            let next = self.parent[current];
            self.parent[current] = root;
            current = next;
        }
        root
    }

    fn merge(&mut self, a: usize, b: usize) -> bool {
        let a = self.root(a);
        let b = self.root(b);
        if a == b {
            return true;
        }
        if let (Some(a), Some(b)) = (&self.constants[a], &self.constants[b])
            && a != b
        {
            return false;
        }
        // An earliest representative has already been rebuilt when used by a
        // later node. Constants need no child traversal and may occur later.
        let (root, child) = if self.constants[a].is_some() || (self.constants[b].is_none() && a < b)
        {
            (a, b)
        } else {
            (b, a)
        };
        self.parent[child] = root;
        true
    }
}

#[derive(Default)]
struct Bounds {
    lower: Option<BigInt>,
    upper: Option<BigInt>,
}

impl HeapSolver {
    pub(super) fn propagated_terms(
        &mut self,
        literals: &[(usize, bool)],
    ) -> Result<Vec<TermId>, HeapError> {
        let mut classes = Classes {
            parent: (0..self.nodes.len()).collect(),
            constants: self
                .terms
                .iter()
                .map(|&term| match self.tm.get(term).map(|t| &t.kind) {
                    Some(TermKind::IntConst(value)) => Some(value.clone()),
                    _ => None,
                })
                .collect(),
        };
        // Repeated handles/names and already-folded constants denote one term.
        let mut first = FxHashMap::default();
        for (index, &term) in self.terms.iter().enumerate() {
            if let Some(&previous) = first.get(&term) {
                if !classes.merge(previous, index) {
                    return Err(HeapError("identical terms have inconsistent constants"));
                }
            } else {
                first.insert(term, index);
            }
        }
        for &(index, polarity) in literals {
            if polarity
                && let Node::Eq(a, b) = self.nodes[index]
                && !classes.merge(a, b)
            {
                // Keep contradictory original assertions for backend reasoning.
                return Ok(self.terms.clone());
            }
        }
        let mut bounds: FxHashMap<usize, Bounds> = FxHashMap::default();
        for &(index, polarity) in literals {
            if polarity && let Node::Le(a, b) = self.nodes[index] {
                let a = classes.root(a);
                let b = classes.root(b);
                if let Some(value) = &classes.constants[a] {
                    let lower = &mut bounds.entry(b).or_default().lower;
                    if lower.as_ref().is_none_or(|old| old < value) {
                        *lower = Some(value.clone());
                    }
                }
                if let Some(value) = &classes.constants[b] {
                    let upper = &mut bounds.entry(a).or_default().upper;
                    if upper.as_ref().is_none_or(|old| old > value) {
                        *upper = Some(value.clone());
                    }
                }
            }
        }
        // Iterate node indices, not hash-map iteration order: stable term IDs
        // and backend search order must not depend on hash-table randomness.
        let mut exact = vec![None; self.nodes.len()];
        for (index, exact_term) in exact.iter_mut().enumerate() {
            if let Some(interval) = bounds.get(&index) {
                if let (Some(lower), Some(upper)) = (&interval.lower, &interval.upper) {
                    if lower > upper {
                        return Ok(self.terms.clone());
                    }
                    if lower == upper {
                        *exact_term = Some(self.tm.mk_int(lower.clone()));
                    }
                }
                if let Some(value) = &classes.constants[index]
                    && (interval.lower.as_ref().is_some_and(|lower| lower > value)
                        || interval.upper.as_ref().is_some_and(|upper| upper < value))
                {
                    return Ok(self.terms.clone());
                }
            }
        }
        let mut rewritten = Vec::with_capacity(self.nodes.len());
        for (index, node) in self.nodes.iter().enumerate() {
            let root = classes.root(index);
            let term = match node {
                Node::Integer(_)
                | Node::IntVar(_)
                | Node::Add(..)
                | Node::Sub(..)
                | Node::Scale(..) => {
                    if let Some(term) = exact[root] {
                        term
                    } else if classes.constants[root].is_some() {
                        self.terms[root]
                    } else if root != index {
                        *rewritten
                            .get(root)
                            .ok_or(HeapError("cyclic equality representative"))?
                    } else {
                        match node {
                            Node::Integer(_) | Node::IntVar(_) => self.terms[index],
                            Node::Add(a, b) => self.tm.mk_add([rewritten[*a], rewritten[*b]]),
                            Node::Sub(a, b) => self.tm.mk_sub(rewritten[*a], rewritten[*b]),
                            Node::Scale(coefficient, a) => {
                                let c = self.tm.mk_int(coefficient.clone());
                                self.tm.mk_mul([c, rewritten[*a]])
                            }
                            Node::Boolean(_)
                            | Node::BoolVar(_)
                            | Node::Eq(..)
                            | Node::Le(..)
                            | Node::Not(_)
                            | Node::And(_)
                            | Node::Or(_)
                            | Node::Heap(_) => {
                                return Err(HeapError("non-integer equality representative"));
                            }
                        }
                    }
                }
                // Substitution never changes asserted Boolean formulas.
                Node::Boolean(_)
                | Node::BoolVar(_)
                | Node::Eq(..)
                | Node::Le(..)
                | Node::Not(_)
                | Node::And(_)
                | Node::Or(_)
                | Node::Heap(_) => self.terms[index],
            };
            rewritten.push(term);
        }
        Ok(rewritten)
    }
}
