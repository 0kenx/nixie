//! Acyclicity **through the congruence closure** (`#P2b-83`, re-fix pass 16).
//!
//! The datatype axioms refute a cycle with the size measure
//! (`solver::dt_axioms`, "Acyclicity"), but only over the terms they
//! axiomatise: the terms of the assertions as written.  The search reasons
//! about the assertions as encoded, and the encoder purifies a numeric
//! argument of an uninterpreted function (`encode::numeric_purification`):
//! `(= (h 1) (cons x (cons 2 (h 1))))` is asserted as `(= (h n) (cons x (cons 2
//! (h n))))` beside `n = 1`, so the size lemmas speak of `(h 1)` and the atom
//! the search holds speaks of `(h n)`.  One constructor deep the refinement's
//! injectivity lemmas happened to close the gap (`#P2b-76`); two deep, every
//! build answered `sat` (z3: `unsat`), and the dev profile's datatype-model
//! net fired on the candidate.
//!
//! This is the occurs check Z3 runs, over the congruence classes of the
//! candidate: a class `K` holding a constructor application `u = C(…, a, …)`
//! whose datatype-sorted argument `a` lies in class `K'` is an edge `K → K'`.
//! A cycle `K₀ → K₁ → … → K₀` makes `u₀` a proper sub-term of itself, so the
//! conjunction `E` of equalities between each argument and the next
//! application is impossible: `¬E` is an instance of a
//! theorem of the datatype theory (acyclicity), valid at every assertion level.

use nixie_core::ast::{TermId, TermKind, TermManager};
use rustc_hash::{FxHashMap, FxHashSet};

use super::super::Solver;

/// A term absent from EUF still has an identity and may contain constructors.
/// Keep it separate from EUF node indices; skipping it would miss hidden cycles.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Class {
    Euf(u32),
    Term(TermId),
}

/// One edge of the class graph: the constructor application `u` (a member of
/// the source class) and its argument `a` (a member of the target class).
#[derive(Clone, Copy)]
struct Edge {
    application: TermId,
    argument: TermId,
    target: Class,
}

impl Solver {
    /// `Some(lemmas)`: one `¬E` per cycle the class graph of the candidate
    /// holds (empty when it is acyclic); `None` when a cycle contains invalid terms or exceeds the scan budget.
    pub(super) fn constructor_cycle_lemmas(
        &mut self,
        manager: &mut TermManager,
    ) -> Option<Vec<TermId>> {
        let class_of = |term| match self.euf.term_to_node(term) {
            Some(node) => Class::Euf(self.euf.find_immutable(node)),
            None => Class::Term(term),
        };
        let mut edges: FxHashMap<Class, Vec<Edge>> = FxHashMap::default();
        let mut pending = Vec::new();
        for (visited, node) in self.euf.all_node_indices().enumerate() {
            if visited >= 100_000 {
                return None;
            }
            pending.push(self.euf.node_term(node)?);
        }
        pending.sort_unstable_by_key(|term| std::cmp::Reverse(term.raw()));
        let mut seen = FxHashSet::default();
        let mut declarations = FxHashMap::default();
        let mut work = 0usize;
        while let Some(term) = pending.pop() {
            if !seen.insert(term) {
                continue;
            }
            work += 1;
            if work > 1_000_000 {
                return None;
            }
            let data = manager.get(term)?;
            let TermKind::DtConstructor { constructor, args } = &data.kind else {
                continue;
            };
            if let std::collections::hash_map::Entry::Vacant(entry) = declarations.entry(data.sort)
            {
                entry.insert(super::super::dt_axioms::resolve_decl(data.sort, manager)?);
            }
            let declaration = declarations.get(&data.sort)?;
            let name = manager.resolve_str(*constructor);
            let info = declaration.constructors.iter().find(|c| c.name == name)?;
            if info.fields.len() != args.len() {
                return None;
            }
            let source = class_of(term);
            for (&arg, field) in args.iter().zip(&info.fields) {
                work += 1;
                if work > 1_000_000 || manager.get(arg)?.sort != field.sort {
                    return None;
                }
                if !field.is_datatype {
                    continue;
                }
                pending.push(arg);
                edges.entry(source).or_default().push(Edge {
                    application: term,
                    argument: arg,
                    target: class_of(arg),
                });
            }
        }
        if edges.is_empty() {
            return Some(Vec::new());
        }
        let mut sources: Vec<Class> = edges.keys().copied().collect();
        sources.sort_unstable();

        // Iterative depth-first search; every back edge closes one cycle.
        let mut state: FxHashMap<Class, u8> = FxHashMap::default(); // 1 = on path, 2 = done
        let mut lemmas: Vec<TermId> = Vec::new();
        for root in sources {
            if state.contains_key(&root) {
                continue;
            }
            // (class, next edge index), and the edge taken into each path entry.
            let mut stack: Vec<(Class, usize)> = vec![(root, 0)];
            let mut taken: Vec<Edge> = Vec::new();
            state.insert(root, 1);
            while let Some(top) = stack.last_mut() {
                let (class, index) = *top;
                top.1 += 1;
                let Some(edge) = edges.get(&class).and_then(|out| out.get(index)).copied() else {
                    state.insert(class, 2);
                    stack.pop();
                    taken.pop();
                    continue;
                };
                match state.get(&edge.target).copied() {
                    Some(1) => {
                        // Back edge: the cycle is the path from `edge.target`
                        // to `class`, closed by `edge`.
                        let start = stack.iter().position(|&(c, _)| c == edge.target)?;
                        let path = taken.get(start..)?;
                        work = work.checked_add(path.len() + 1)?;
                        if work > 1_000_000 {
                            return None;
                        }
                        let mut cycle: Vec<Edge> = path.to_vec();
                        cycle.push(edge);
                        lemmas.push(self.cycle_lemma(&cycle, manager)?);
                        if lemmas.len() > 100_000 {
                            return None;
                        }
                    }
                    Some(_) => {}
                    None => {
                        state.insert(edge.target, 1);
                        stack.push((edge.target, 0));
                        taken.push(edge);
                    }
                }
            }
        }
        Some(lemmas)
    }

    /// `¬E` for one cycle: `E` merges each edge's argument with the
    /// application the next edge leaves from (the last edge's with the first
    /// edge's application).
    fn cycle_lemma(&mut self, cycle: &[Edge], manager: &mut TermManager) -> Option<TermId> {
        let mut hypotheses: Vec<TermId> = Vec::new();
        for (index, edge) in cycle.iter().enumerate() {
            let next = cycle.get(index + 1).or_else(|| cycle.first())?;
            if edge.argument == next.application {
                continue;
            }
            let argument = edge.argument;
            let application = next.application;
            if manager.get(argument)?.sort != manager.get(application)?.sort {
                return None;
            }
            hypotheses.push(
                manager.intern_term(TermKind::Eq(argument, application), manager.sorts.bool_sort),
            );
        }
        hypotheses.sort_unstable_by_key(|term| term.raw());
        hypotheses.dedup();
        let negated: Vec<TermId> = hypotheses.iter().map(|&h| manager.mk_not(h)).collect();
        Some(manager.mk_or(negated))
    }
}
