//! Candidate-driven functional congruence. Every emitted clause is the valid
//! Ackermann implication, never an unconditional equality of model collisions.
use super::{Model, Solver};
use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::interner::Spur;
use nixie_core::sort::{SortId, SortKind};
use rustc_hash::{FxHashMap, FxHashSet};

const MAX_WORK: usize = 100_000;
const MAX_LEMMAS: usize = 256;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum ValueKey {
    Closed(SortId, TermId),
    Class(SortId, u32),
}

fn spend(work: &mut usize) -> Option<()> {
    *work = work.checked_sub(1)?;
    Some(())
}

struct Values {
    members: FxHashMap<u32, Vec<TermId>>,
    memo: FxHashMap<TermId, Option<ValueKey>>,
    closed: FxHashMap<TermId, Option<TermId>>,
    work: usize,
}

impl Values {
    fn new(solver: &Solver) -> Option<Self> {
        let euf = solver.model_euf();
        if euf.all_node_indices().len() > MAX_WORK {
            return None;
        }
        let mut members: FxHashMap<u32, Vec<TermId>> = FxHashMap::default();
        for node in euf.all_node_indices() {
            if let Some(term) = euf.node_term(node) {
                members
                    .entry(euf.find_immutable(node))
                    .or_default()
                    .push(term);
            }
        }
        for terms in members.values_mut() {
            terms.sort_unstable();
            terms.dedup();
        }
        Some(Self {
            members,
            memo: FxHashMap::default(),
            closed: FxHashMap::default(),
            work: MAX_WORK - euf.all_node_indices().len(),
        })
    }

    fn key(
        &mut self,
        solver: &Solver,
        term: TermId,
        model: &Model,
        manager: &mut TermManager,
    ) -> Option<ValueKey> {
        spend(&mut self.work)?;
        if let Some(value) = self.memo.get(&term) {
            return *value;
        }
        let value = self.read_key(solver, term, model, manager);
        self.memo.insert(term, value);
        value
    }

    fn read_key(
        &mut self,
        solver: &Solver,
        term: TermId,
        model: &Model,
        manager: &mut TermManager,
    ) -> Option<ValueKey> {
        let sort = manager.get(term)?.sort;
        let representative = solver.euf_class_representative(term);
        if matches!(manager.sorts.get(sort)?.kind, SortKind::Uninterpreted(_))
            || (matches!(manager.sorts.get(sort)?.kind, SortKind::Array { .. })
                && contains_value_sort(sort, manager, &mut self.work))
        {
            return representative.map(|rep| ValueKey::Class(sort, rep));
        }
        let members = representative
            .and_then(|rep| self.members.get(&rep).cloned())
            .unwrap_or_else(|| vec![term]);
        for member in members {
            spend(&mut self.work)?;
            if let Some(value) = model.get(member)
                && !model.is_defaulted(member)
                && let Some(value) = self.closed_value(solver, value, manager)
                && manager.get(value)?.sort == sort
            {
                return Some(ValueKey::Closed(sort, value));
            }
            if let Some(value) = self.closed_value(solver, member, manager)
                && manager.get(value)?.sort == sort
            {
                return Some(ValueKey::Closed(sort, value));
            }
        }
        if model.is_defaulted(term) {
            return None;
        }
        let value = solver.model_value_in(term, model, manager)?;
        self.closed_value(solver, value, manager)
            .map(|value| ValueKey::Closed(sort, value))
    }

    /// A certificate cannot treat missing/defaulted values as evidence, or
    /// let an EUF assignment override the semantics of a literal/compound.
    fn certificate_key(
        &mut self,
        solver: &Solver,
        term: TermId,
        model: &Model,
        manager: &mut TermManager,
    ) -> Option<ValueKey> {
        spend(&mut self.work)?;
        let sort = manager.get(term)?.sort;
        if let Some(value) = self.closed_value(solver, term, manager) {
            return Some(ValueKey::Closed(sort, value));
        }
        if matches!(manager.sorts.get(sort)?.kind, SortKind::Uninterpreted(_)) {
            return solver
                .euf_class_representative(term)
                .map(|r| ValueKey::Class(sort, r));
        }
        if model.is_defaulted(term) {
            return None;
        }
        // The value-only reader recomputes compounds; it has no live-theory
        // fallback and preserves exact wide integers, rationals and BVs.
        let value = solver.model_value_in(term, model, manager)?;
        let value = self.closed_value(solver, value, manager)?;
        (manager.get(value)?.sort == sort).then_some(ValueKey::Closed(sort, value))
    }

    /// Normalize scalar leaves exactly before hash-consing a constructor DAG.
    /// A shared subtree is visited once, and no recursive equality/hash/drop of
    /// a nested Rust value is needed even for very deep datatype values.
    fn closed_value(
        &mut self,
        solver: &Solver,
        term: TermId,
        manager: &mut TermManager,
    ) -> Option<TermId> {
        enum Frame {
            Visit(TermId),
            Finish(TermId, Spur, SortId, Vec<TermId>),
        }
        let mut stack = vec![Frame::Visit(term)];
        let empty = Model::new();
        while let Some(frame) = stack.pop() {
            spend(&mut self.work)?;
            match frame {
                Frame::Visit(term) => {
                    if self.closed.contains_key(&term) {
                        continue;
                    }
                    let node = manager.get(term)?;
                    if let TermKind::DtConstructor { constructor, args } = &node.kind {
                        let args = args.to_vec();
                        stack.push(Frame::Finish(term, *constructor, node.sort, args.clone()));
                        stack.extend(args.into_iter().rev().map(Frame::Visit));
                    } else {
                        let value = solver.model_value_in(term, &empty, manager);
                        self.closed.insert(term, value);
                    }
                }
                Frame::Finish(term, constructor, sort, args) => {
                    let values: Option<Vec<_>> = args
                        .iter()
                        .map(|arg| self.closed.get(arg).copied().flatten())
                        .collect();
                    let value = values.map(|args| {
                        let name = manager.resolve_str(constructor).to_string();
                        manager.mk_dt_constructor(&name, args, sort)
                    });
                    self.closed.insert(term, value);
                }
            }
        }
        self.closed.get(&term).copied().flatten()
    }
}

fn contains_value_sort(sort: SortId, manager: &TermManager, work: &mut usize) -> bool {
    let mut stack = vec![sort];
    let mut seen = FxHashSet::default();
    while let Some(sort) = stack.pop() {
        if spend(work).is_none() {
            return false;
        }
        if !seen.insert(sort) {
            continue;
        }
        match manager.sorts.get(sort).map(|sort| &sort.kind) {
            Some(SortKind::Datatype(_) | SortKind::Uninterpreted(_)) => return true,
            Some(SortKind::Array { domain, range }) => {
                stack.push(*domain);
                stack.push(*range);
            }
            _ => {}
        }
    }
    false
}

impl Solver {
    /// Removing eager numeric UF pins may leave an arithmetic/EUF candidate
    /// whose concrete function points collide. Check the interpretation before
    /// accepting Sat. Unlike the refinement helper below, every missing value
    /// or exhausted budget fails closed, and no clauses/search are added.
    ///
    /// Z3's model_generator::mk_func_interps builds entries from argument
    /// *values*. The same function must have one result at each such tuple.
    pub(super) fn unpinned_function_model_is_consistent(&self, manager: &mut TermManager) -> bool {
        self.check_unpinned_function_model(manager).is_some()
    }

    fn check_unpinned_function_model(&self, manager: &mut TermManager) -> Option<()> {
        let euf = self.model_euf();
        let mut work = MAX_WORK;
        let mut functions = FxHashSet::default();
        // Only obligations created by omission of an encoder pin trigger
        // this certificate. EUF also contains interpreted arrays, transient
        // witnesses, and model-only terms that never had such an obligation.
        for &term in &self.unpinned_uf_apps {
            spend(&mut work)?;
            let TermKind::Apply { func, args } = &manager.get(term)?.kind else {
                return None;
            };
            for &arg in args.iter() {
                spend(&mut work)?;
                if !self.interface_const_pins.contains_key(&arg)
                    && self.interface_constant_value(arg, manager).is_some()
                {
                    functions.insert(*func);
                }
            }
        }
        if functions.is_empty() {
            return Some(());
        }
        // Include every point of each affected function, not just its
        // literal-argument point; otherwise f(4) and f(x), x = 4, can collide.
        let mut apps: Vec<_> = self.unpinned_uf_apps.iter().copied().collect();
        for node in euf.all_node_indices() {
            spend(&mut work)?;
            let term = euf.node_term(node)?;
            if matches!(&manager.get(term)?.kind, TermKind::Apply { func, .. }
                if functions.contains(func))
            {
                apps.push(term);
            }
        }
        let model = self.model.as_ref()?;
        let mut values = Values::new(self)?;
        values.work = values.work.min(work);
        type Point = (Spur, SortId, Vec<ValueKey>);
        let mut points: FxHashMap<Point, ValueKey> = FxHashMap::default();
        apps.sort_unstable();
        apps.dedup();
        for term in apps {
            spend(&mut values.work)?;
            let node = manager.get(term)?;
            let sort = node.sort;
            let TermKind::Apply { func, args } = node.kind.clone() else {
                return None;
            };
            if !functions.contains(&func) {
                continue;
            }
            let keys: Option<Vec<_>> = args
                .iter()
                .map(|&arg| values.certificate_key(self, arg, model, manager))
                .collect();
            let result = values.certificate_key(self, term, model, manager)?;
            let point = (func, sort, keys?);
            if let Some(previous) = points.insert(point, result)
                && previous != result
            {
                return None;
            }
        }
        Some(())
    }

    /// Produce valid guarded congruence obligations for concrete collisions.
    /// The final-result guard rejects such a candidate without retrying search.
    /// This is a refutation helper, not a certificate: missing values may be
    /// skipped here, while the unpinned-interface certificate fails closed.
    pub(super) fn functional_collision_lemmas(
        &self,
        manager: &mut TermManager,
        non_numeric_only: bool,
    ) -> Vec<TermId> {
        let Some(model) = self.model.as_ref() else {
            return Vec::new();
        };
        let Some(mut values) = Values::new(self) else {
            return Vec::new();
        };
        let mut apps: Vec<_> = self
            .model_euf()
            .all_node_indices()
            .filter_map(|node| self.model_euf().node_term(node))
            .filter(|&term| {
                manager
                    .get(term)
                    .is_some_and(|node| matches!(node.kind, TermKind::Apply { .. }))
            })
            .collect();
        apps.sort_unstable();
        apps.dedup();
        type Point = (Spur, SortId, Vec<ValueKey>);
        let mut points: FxHashMap<Point, (TermId, ValueKey, Vec<TermId>)> = FxHashMap::default();
        let mut lemmas = Vec::new();
        for term in apps {
            if values.work == 0 || lemmas.len() >= MAX_LEMMAS {
                break;
            }
            let Some(node) = manager.get(term) else {
                continue;
            };
            let sort = node.sort;
            if non_numeric_only
                && (sort == manager.sorts.int_sort || sort == manager.sorts.real_sort)
            {
                continue;
            }
            let TermKind::Apply { func, args } = node.kind.clone() else {
                continue;
            };
            // The injective-distinct encoding owns these auxiliary functions
            // and reconstructs their witnesses from the original operands.
            // Their transient EUF classes are not published function values.
            // Treating each class as a distinct result here competes with that
            // reconstruction, particularly when the distinct atom is false.
            let name = manager.resolve_str(func);
            if nixie_core::reserved::is_reserved_tag(name, "dist-f")
                || nixie_core::reserved::is_reserved_tag(name, "dist-g")
            {
                continue;
            }
            if args.is_empty() {
                continue;
            }
            let keys: Option<Vec<_>> = args
                .iter()
                .map(|&arg| values.key(self, arg, model, manager))
                .collect();
            let Some(keys) = keys else {
                continue;
            };
            let Some(result) = values.key(self, term, model, manager) else {
                continue;
            };
            let point = (func, sort, keys);
            let Some((first, prior, previous_args)) = points.get(&point) else {
                points.insert(point, (term, result, args.to_vec()));
                continue;
            };
            if result == *prior
                || self
                    .euf_class_representative(*first)
                    .zip(self.euf_class_representative(term))
                    .is_some_and(|(a, b)| a == b)
            {
                continue;
            }
            // The key includes every argument's sort and position, as well as
            // result sort. Check arity explicitly before forming all premises.
            if args.len() != previous_args.len() {
                continue;
            }
            let premises: Vec<_> = previous_args
                .iter()
                .zip(args.iter())
                .filter(|(a, b)| a != b)
                .map(|(&a, &b)| manager.mk_eq(a, b))
                .collect();
            let premise = manager.mk_and(premises);
            let conclusion = manager.mk_eq(*first, term);
            let lemma = manager.mk_implies(premise, conclusion);
            if !self.dt_axiom_instances.contains(&lemma) {
                lemmas.push(lemma);
            }
        }
        lemmas
    }
}

impl Solver {
    pub(super) fn assert_functional_consistency(
        &mut self,
        manager: &mut TermManager,
        non_numeric_only: bool,
    ) -> bool {
        let lemmas = self.functional_collision_lemmas(manager, non_numeric_only);
        let added = !lemmas.is_empty();
        for lemma in lemmas {
            self.assert_dt_lemma(lemma, manager);
        }
        added
    }
}

#[cfg(test)]
mod tests;
