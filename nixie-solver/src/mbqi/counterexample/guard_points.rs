//! Extra MBQI witnesses at literal guard boundaries. These are proposals, never
//! a coverage certificate. As in Z3's `add_mono_exceptions`, integer and BV
//! exceptions contribute their immediate neighbours (modulo the exact width).

use super::*;

const MAX_GUARD_POINTS: usize = 12;
const MAX_GUARD_COMBINATIONS: usize = 64;
const MAX_GUARD_WORK: usize = 20_000;
const MAX_GUARD_VARIABLES: usize = 64;

impl CounterExampleGenerator {
    pub(super) fn guard_point_counterexamples(
        &mut self,
        quantifier: &QuantifiedFormula,
        candidates: &[Vec<TermId>],
        model: &CompletedModel,
        manager: &mut TermManager,
    ) -> Vec<CounterExample> {
        if quantifier.bound_vars.is_empty()
            || quantifier.bound_vars.len() > MAX_GUARD_VARIABLES
            || self.max_cex_per_quantifier == 0
        {
            return Vec::new();
        }
        let mut lists = Vec::new();
        let mut fresh = Vec::new();
        let mut work = MAX_GUARD_WORK;
        for (index, &(name, sort)) in quantifier.bound_vars.iter().enumerate() {
            let mut list: Vec<_> = candidates
                .get(index)
                .into_iter()
                .flatten()
                .copied()
                .take(self.max_candidates_per_var.min(MAX_GUARD_COMBINATIONS))
                .collect();
            let mut new = Vec::new();
            for point in guard_points(quantifier.body, name, sort, manager, &mut work) {
                if !list.contains(&point) {
                    new.push(point);
                    list.push(point);
                    if new.len() == MAX_GUARD_POINTS {
                        break;
                    }
                }
            }
            if list.is_empty() {
                return Vec::new();
            }
            lists.push(list);
            fresh.push(new);
        }

        // Fix one fresh point as a pivot and enumerate the other axes. Every
        // visited tuple is charged, including duplicates; unlike an odometer
        // over old values first, this cannot skip exponentially many tuples
        // without spending its budget. Cycle pivots between evaluations so a
        // large product on the first axis cannot starve later guard variables.
        let mut pivots: Vec<_> = fresh
            .into_iter()
            .enumerate()
            .flat_map(|(axis, points)| points.into_iter().map(move |point| (axis, point)))
            .collect();
        let mut cursors = vec![vec![0usize; lists.len()]; pivots.len()];
        let mut found = Vec::new();
        let mut visited = FxHashSet::default();
        let mut attempts = 0;
        let mut pivot = 0;
        while !pivots.is_empty() && attempts < MAX_GUARD_COMBINATIONS {
            attempts += 1;
            let (axis, point) = pivots[pivot];
            let mut witnesses: Vec<_> = lists
                .iter()
                .zip(&cursors[pivot])
                .map(|(list, &slot)| list[slot])
                .collect();
            witnesses[axis] = point;
            if visited.insert(witnesses.clone()) {
                self.stats.num_combinations_tried += 1;
                let assignment = quantifier
                    .bound_vars
                    .iter()
                    .zip(&witnesses)
                    .map(|(&(name, _), &value)| (name, value))
                    .collect();
                let substituted = self.apply_substitution(quantifier.body, &assignment, manager);
                let value = self.evaluate_under_model(substituted, model, manager);
                if self.is_counterexample(value, quantifier.is_universal, manager) {
                    let mut cex = CounterExample::new(
                        quantifier.term,
                        assignment,
                        witnesses,
                        model.generation,
                    );
                    cex.body_value = Some(value);
                    cex.calculate_quality(manager);
                    found.push(cex);
                    if found.len() >= self.max_cex_per_quantifier {
                        break;
                    }
                }
            }
            let mut advanced = false;
            for (index, slot) in cursors[pivot].iter_mut().enumerate() {
                if index == axis {
                    continue;
                }
                *slot += 1;
                if *slot < lists[index].len() {
                    advanced = true;
                    break;
                }
                *slot = 0;
            }
            if !advanced {
                pivots.remove(pivot);
                cursors.remove(pivot);
            } else {
                pivot += 1;
            }
            if pivot == pivots.len() {
                pivot = 0;
            }
        }
        found
    }
}

fn guard_points(
    body: TermId,
    name: Spur,
    sort: SortId,
    manager: &mut TermManager,
    work: &mut usize,
) -> Vec<TermId> {
    if !matches!(
        manager.sorts.get(sort).map(|s| &s.kind),
        Some(SortKind::Int | SortKind::BitVec(_))
    ) {
        return Vec::new();
    }
    let bound = |term| {
        manager.get(term).is_some_and(|data| {
            data.sort == sort && matches!(data.kind, TermKind::Var(n) if n == name)
        })
    };
    let mut literals = FxHashSet::default();
    let mut pending = vec![body];
    let mut seen = FxHashSet::default();
    while let Some(term) = pending.pop() {
        if *work == 0 {
            break;
        }
        *work -= 1;
        if !seen.insert(term) {
            continue;
        }
        let Some(data) = manager.get(term) else {
            continue;
        };
        let mut record = |left, right| {
            let literal = if bound(left) {
                right
            } else if bound(right) {
                left
            } else {
                return;
            };
            if manager.get(literal).is_some_and(|n| {
                n.sort == sort
                    && matches!(n.kind, TermKind::IntConst(_) | TermKind::BitVecConst { .. })
            }) {
                literals.insert(literal);
            }
        };
        match &data.kind {
            TermKind::Forall { .. } | TermKind::Exists { .. } => continue,
            TermKind::Eq(a, b)
            | TermKind::BvUlt(a, b)
            | TermKind::BvUle(a, b)
            | TermKind::BvSlt(a, b)
            | TermKind::BvSle(a, b)
            | TermKind::Lt(a, b)
            | TermKind::Le(a, b)
            | TermKind::Gt(a, b)
            | TermKind::Ge(a, b) => record(*a, *b),
            TermKind::Distinct(args) => {
                // Only pairs involving this variable matter: no quadratic
                // materialization of all pairs of a user-controlled n-ary AST.
                if args.iter().take(*work).any(|&arg| bound(arg)) {
                    for &arg in args.iter().take(*work) {
                        if manager.get(arg).is_some_and(|n| {
                            n.sort == sort
                                && matches!(
                                    n.kind,
                                    TermKind::IntConst(_) | TermKind::BitVecConst { .. }
                                )
                        }) {
                            literals.insert(arg);
                        }
                    }
                }
                *work = work.saturating_sub(args.len());
            }
            TermKind::Select(array, index) => {
                let mut level = *array;
                while *work > 0 {
                    *work -= 1;
                    let Some(TermKind::Store(inner, written, _)) =
                        manager.get(level).map(|n| &n.kind)
                    else {
                        break;
                    };
                    record(*written, *index);
                    level = *inner;
                }
            }
            _ => {}
        }
        // A very wide child list can itself consume the remaining scan budget.
        let children = nixie_core::ast::traversal::get_children(&data.kind);
        pending.extend(children.into_iter().take(*work));
    }
    let mut keyed = Vec::new();
    let mut seen = FxHashSet::default();
    let mut literals: Vec<_> = literals.into_iter().collect();
    literals.sort_unstable();
    for literal in literals {
        for point in neighbourhood(literal, manager) {
            if seen.insert(point)
                && let Some(key) = literal_value(point, manager)
            {
                keyed.push((key, point));
            }
        }
    }
    keyed.sort_unstable_by(|a, b| a.0.cmp(&b.0));
    keyed.into_iter().map(|(_, term)| term).collect()
}

fn literal_value(term: TermId, manager: &TermManager) -> Option<BigInt> {
    match &manager.get(term)?.kind {
        TermKind::BitVecConst { value, .. } | TermKind::IntConst(value) => Some(value.clone()),
        _ => None,
    }
}

fn neighbourhood(literal: TermId, manager: &mut TermManager) -> Vec<TermId> {
    match manager.get(literal).map(|data| data.kind.clone()) {
        Some(TermKind::BitVecConst { value, width }) => {
            let modulus = BigInt::from(1u8) << width;
            vec![
                literal,
                manager.mk_bitvec((&value + 1u8) % &modulus, width),
                manager.mk_bitvec((&value + &modulus - 1u8) % &modulus, width),
            ]
        }
        Some(TermKind::IntConst(value)) => vec![
            literal,
            manager.mk_int(&value + 1u8),
            manager.mk_int(&value - 1u8),
        ],
        _ => Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tracked(
        manager: &mut TermManager,
        vars: &[(&str, SortId)],
        body: TermId,
    ) -> QuantifiedFormula {
        let term = manager.mk_forall(vars.iter().copied(), body);
        let names = vars
            .iter()
            .map(|&(name, sort)| (manager.intern_str(name), sort))
            .collect();
        QuantifiedFormula::new(term, names, body, true)
    }

    #[test]
    fn integer_guard_finds_a_point_absent_from_the_model() {
        let mut m = TermManager::new();
        let int = m.sorts.int_sort;
        let x = m.mk_var("x", int);
        let seven = m.mk_int(7);
        let zero = m.mk_int(0);
        let body = m.mk_le(x, seven);
        let q = tracked(&mut m, &[("x", int)], body);
        let mut generator = CounterExampleGenerator::new();
        let found = generator.guard_point_counterexamples(
            &q,
            &[vec![zero]],
            &CompletedModel::new(),
            &mut m,
        );
        assert_eq!(found.len(), 1);
        assert_eq!(
            literal_value(found[0].witnesses[0], &m),
            Some(BigInt::from(8))
        );
        assert!(generator.exhaustive_candidates.is_empty());
        assert!(generator.candidate_cache.is_empty());
    }

    #[test]
    fn wide_bv_neighbours_wrap_exactly_and_refute_signed_guard() {
        let mut m = TermManager::new();
        let sort = m.sorts.bitvec(129);
        let x = m.mk_var("x", sort);
        let zero = m.mk_bitvec(0, 129);
        let maximum: BigInt = (BigInt::from(1u8) << 129u32) - 1u8;
        let points = neighbourhood(zero, &mut m);
        assert!(
            points
                .iter()
                .any(|&p| literal_value(p, &m) == Some(maximum.clone()))
        );
        let body = m.mk_bv_sle(zero, x);
        let q = tracked(&mut m, &[("x", sort)], body);
        let mut generator = CounterExampleGenerator::new();
        let found = generator.guard_point_counterexamples(
            &q,
            &[vec![zero]],
            &CompletedModel::new(),
            &mut m,
        );
        assert_eq!(found.len(), 1);
        assert_eq!(literal_value(found[0].witnesses[0], &m), Some(maximum));
    }

    #[test]
    fn nested_binders_do_not_contribute_shadowed_boundaries() {
        let mut m = TermManager::new();
        let int = m.sorts.int_sort;
        let x = m.mk_var("x", int);
        let n = m.mk_int(99);
        let body = m.mk_lt(x, n);
        let inner = m.mk_forall([("x", int)], body);
        let name = m.intern_str("x");
        let mut work = MAX_GUARD_WORK;
        assert!(guard_points(inner, name, int, &mut m, &mut work).is_empty());
    }

    #[test]
    fn array_write_indices_supply_guard_points() {
        let mut m = TermManager::new();
        let int = m.sorts.int_sort;
        let sort = m.sorts.array(int, int);
        let a = m.mk_var("a", sort);
        let x = m.mk_var("x", int);
        let n = m.mk_int(57);
        let one = m.mk_int(1);
        let store = m.mk_store(a, n, one);
        let read = m.mk_select(store, x);
        let name = m.intern_str("x");
        let mut work = MAX_GUARD_WORK;
        let points = guard_points(read, name, int, &mut m, &mut work);
        assert_eq!(
            points
                .iter()
                .filter_map(|&p| literal_value(p, &m))
                .collect::<Vec<_>>(),
            vec![56.into(), 57.into(), 58.into()]
        );
    }

    #[test]
    fn many_old_axes_cannot_hide_a_new_point_behind_an_exponential_prefix() {
        let mut m = TermManager::new();
        let int = m.sorts.int_sort;
        let names: Vec<_> = (0..24).map(|i| format!("x{i}")).collect();
        let vars: Vec<_> = names.iter().map(|s| (s.as_str(), int)).collect();
        let x = m.mk_var("x23", int);
        let n = m.mk_int(100);
        let body = m.mk_le(x, n);
        let q = tracked(&mut m, &vars, body);
        let candidates = vec![(0..10).map(|i| m.mk_int(i)).collect::<Vec<_>>(); 24];
        let mut generator = CounterExampleGenerator::new();
        let found =
            generator.guard_point_counterexamples(&q, &candidates, &CompletedModel::new(), &mut m);
        assert!(!found.is_empty());
        assert!(generator.stats.num_combinations_tried <= MAX_GUARD_COMBINATIONS);
        assert!(
            found
                .iter()
                .all(|c| literal_value(c.witnesses[23], &m) == Some(101.into()))
        );
    }
}
