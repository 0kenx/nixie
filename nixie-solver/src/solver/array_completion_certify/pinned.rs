//! Finite counterexample points used only to explain or reject a model.
use super::{Goal, is_literal};
use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::sort::{SortId, SortKind};
use num_bigint::BigInt;
use rustc_hash::{FxHashMap, FxHashSet};
const MAX_PINS_PER_SORT: usize = 16;
impl Goal {
    pub(super) fn points_by_sort(&self, manager: &TermManager) -> FxHashMap<SortId, Vec<TermId>> {
        let mut found: Vec<TermId> = Vec::new();
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut stack: Vec<TermId> = self.assertions.clone();
        let mut children: Vec<TermId> = Vec::new();
        while let Some(current) = stack.pop() {
            if !visited.insert(current) {
                continue;
            }
            let Some(data) = manager.get(current) else {
                continue;
            };
            if is_literal(current, manager) {
                found.push(current);
            }
            children.clear();
            children.extend(nixie_core::ast::traversal::get_children(&data.kind));
            stack.extend(children.iter().copied());
        }
        found.extend(
            self.scalar_pins
                .values()
                .copied()
                .filter(|&v| is_literal(v, manager)),
        );

        let mut by_sort: FxHashMap<SortId, Vec<TermId>> = FxHashMap::default();
        for term in found {
            let Some(sort) = manager.get(term).map(|d| d.sort) else {
                continue;
            };
            by_sort.entry(sort).or_default().push(term);
        }
        for points in by_sort.values_mut() {
            points.sort_by_key(|point| literal_key(*point, manager));
            points.dedup();
            points.truncate(MAX_PINS_PER_SORT);
        }
        by_sort
    }
}
pub(super) fn unnamed_point(
    sort: SortId,
    named: &[TermId],
    manager: &mut TermManager,
) -> Option<TermId> {
    let kind = manager.sorts.get(sort).map(|s| s.kind.clone())?;
    let taken: FxHashSet<(u8, BigInt)> = named
        .iter()
        .filter_map(|&t| literal_key(t, manager))
        .collect();
    match kind {
        SortKind::BitVec(width) => {
            let limit = BigInt::from(1u8) << width;
            let mut value = BigInt::from(0u8);
            while value < limit {
                if !taken.contains(&(0, value.clone())) {
                    return Some(manager.mk_bitvec(value, width));
                }
                value += 1u8;
            }
            None
        }
        SortKind::Int => {
            let mut value = BigInt::from(0u8);
            loop {
                if !taken.contains(&(1, value.clone())) {
                    return Some(manager.mk_int(value));
                }
                value += 1u8;
            }
        }
        SortKind::Bool => {
            if !taken.contains(&(2, BigInt::from(0u8))) {
                Some(manager.mk_false())
            } else if !taken.contains(&(2, BigInt::from(1u8))) {
                Some(manager.mk_true())
            } else {
                None
            }
        }
        _ => None,
    }
}

pub(super) fn gap_representatives(
    sort: SortId,
    named: &[TermId],
    manager: &mut TermManager,
) -> Vec<TermId> {
    let Some(kind) = manager.sorts.get(sort).map(|s| s.kind.clone()) else {
        return Vec::new();
    };
    let taken: FxHashSet<BigInt> = named
        .iter()
        .filter_map(|&t| literal_key(t, manager).map(|(_, value)| value))
        .collect();
    match kind {
        SortKind::BitVec(width) => {
            let modulus = BigInt::from(1u8) << width;
            let half = BigInt::from(1u8) << width.saturating_sub(1);
            let mut candidates: Vec<BigInt> =
                vec![BigInt::from(0u8), &modulus - 1u8, half.clone(), &half - 1u8];
            for r in &taken {
                candidates.push((r + 1u8 + &modulus) % &modulus);
                candidates.push((r - 1u8 + &modulus) % &modulus);
            }
            candidates.retain(|value| *value >= BigInt::from(0u8) && *value < modulus);
            candidates.retain(|value| !taken.contains(value));
            candidates.sort();
            candidates.dedup();
            candidates
                .into_iter()
                .map(|value| manager.mk_bitvec(value, width))
                .collect()
        }
        SortKind::Int => {
            let mut candidates: Vec<BigInt> = if taken.is_empty() {
                vec![BigInt::from(0u8)]
            } else {
                taken
                    .iter()
                    .flat_map(|r| [r + 1u8, r - 1u8])
                    .filter(|value| !taken.contains(value))
                    .collect()
            };
            candidates.sort();
            candidates.dedup();
            candidates
                .into_iter()
                .map(|value| manager.mk_int(value))
                .collect()
        }
        _ => unnamed_point(sort, named, manager).into_iter().collect(),
    }
}

fn literal_key(term: TermId, manager: &TermManager) -> Option<(u8, BigInt)> {
    match &manager.get(term)?.kind {
        TermKind::BitVecConst { value, .. } => Some((0, value.clone())),
        TermKind::IntConst(value) => Some((1, value.clone())),
        TermKind::False => Some((2, BigInt::from(0u8))),
        TermKind::True => Some((2, BigInt::from(1u8))),
        _ => Some((3, BigInt::from(term.raw()))),
    }
}
