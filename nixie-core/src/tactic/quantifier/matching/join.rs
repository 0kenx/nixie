//! The multi-trigger join of [`super::PatternMatcher::match_against`].
//!
//! A multi-trigger (`:pattern ((f x) (g x))`) matches when every one of its
//! triggers matches some ground term *consistently*: the partial
//! substitutions are merged, and two that bind a shared variable to
//! different terms do not go together.  The merge used to be a cross
//! product – every partial substitution of the accumulated merge against
//! every one of the next trigger's, a consistency test per pair – so n
//! matches per trigger were n² tests to produce n bindings: 43.2 ms at
//! 4,000 values per trigger, against 2.2 ms now, for the same 4,000
//! bindings in the same order.
//!
//! Two changes, both invisible in the result:
//!
//! * **The join is indexed.**  A trigger whose matches all bind the same
//!   variables (the ordinary case: the trigger's own free variables) and
//!   share some of them with the merge so far is bucketed by the values of
//!   exactly those shared variables, so each accumulated substitution meets
//!   only the partial substitutions that agree with it: the join is expected
//!   linear in its input plus its output.  A level whose matches bind
//!   differing variables is joined by the pairwise test as before.
//! * **The join is streamed.**  The consistent merges are enumerated in the
//!   order the cross product visited them (first trigger outermost, last
//!   innermost) by an explicit-stack descent, and the consumer can stop it.
//!   Two triggers over disjoint variables have no shared variable to index
//!   on and a cross product for their answer, but the tactic only wants its
//!   budget's worth: with 256 matches per side, 65,536 bindings were
//!   materialized for the tactic to instantiate 100 of them (9.7 ms for
//!   the list, against 0.13 ms for the prefix).
//!
//! The order is load-bearing: the tactic instantiates its bindings in the
//! order produced, up to its budget, so a reordered join would instantiate
//! a different subset.  A bucket holds its substitutions' positions in
//!   increasing order, which is the order the pairwise test visited them in.

use crate::ast::TermId;
use crate::interner::Spur;
use crate::prelude::*;

/// A partial substitution: bound variable → ground term.
type Subst = FxHashMap<Spur, TermId>;

/// Whether `next` is consistent with `merged`: no shared variable is bound
/// to two different terms. The test the pairwise cross product ran per pair.
fn consistent(merged: &Subst, next: &Subst) -> bool {
    next.iter()
        .all(|(&var, &term)| merged.get(&var).is_none_or(|bound| *bound == term))
}

/// `merged` extended with `next`; the two are consistent.
fn merge(merged: &Subst, next: &Subst) -> Subst {
    let mut merged = merged.clone();
    merged.extend(next.iter().map(|(&var, &term)| (var, term)));
    merged
}

/// The variables every substitution of `level` binds, when they all bind
/// the same set; `None` when they do not.
fn uniform_vars(level: &[Subst]) -> Option<FxHashSet<Spur>> {
    let first = level.first()?;
    let vars: FxHashSet<Spur> = first.keys().copied().collect();
    level
        .iter()
        .all(|subst| subst.len() == vars.len() && subst.keys().all(|var| vars.contains(var)))
        .then_some(vars)
}

/// One trigger's partial substitutions bucketed by their values for a fixed
/// set of variables: every substitution binds all of them, so a lookup by a
/// merge's values for the same variables finds exactly the substitutions
/// consistent with that merge.
struct Buckets {
    /// The variables bucketed on, in key order.
    key_vars: Vec<Spur>,
    /// Values for `key_vars`, in that order → the positions of the
    /// substitutions binding them, ascending.
    buckets: FxHashMap<Vec<TermId>, Vec<u32>>,
}

impl Buckets {
    fn build(level: &[Subst], key_vars: Vec<Spur>) -> Self {
        let mut buckets: FxHashMap<Vec<TermId>, Vec<u32>> = FxHashMap::default();
        for (position, subst) in level.iter().enumerate() {
            let key: Vec<TermId> = key_vars.iter().map(|var| subst[var]).collect();
            buckets.entry(key).or_default().push(position as u32);
        }
        Self { key_vars, buckets }
    }

    /// The positions of the substitutions consistent with `merged`, when
    /// `merged` binds every key variable (otherwise the index does not
    /// apply and the caller scans).
    fn lookup(&self, merged: &Subst) -> Option<&[u32]> {
        let mut key = Vec::with_capacity(self.key_vars.len());
        for var in &self.key_vars {
            key.push(*merged.get(var)?);
        }
        Some(self.buckets.get(&key).map_or(&[], Vec::as_slice))
    }
}

/// Where a frame of the descent is in the next level's substitutions.
enum Cursor<'i> {
    /// Every substitution of the level, in order, each tested for
    /// consistency with the merge – the pairwise form, for a level that
    /// binds varying variables or shares none with the merge so far.
    Scan { substs: &'i [Subst], next: usize },
    /// The substitutions of one bucket, in order – consistent with the
    /// merge by construction, so untested.
    Bucket {
        substs: &'i [Subst],
        positions: &'i [u32],
        next: usize,
    },
}

impl Cursor<'_> {
    /// The next substitution of the level to merge with `merged`.
    fn next(&mut self, merged: &Subst) -> Option<&Subst> {
        match self {
            Cursor::Scan { substs, next } => loop {
                let subst = substs.get(*next)?;
                *next += 1;
                if consistent(merged, subst) {
                    return Some(subst);
                }
            },
            Cursor::Bucket {
                substs,
                positions,
                next,
            } => {
                let position = positions.get(*next)?;
                *next += 1;
                substs.get(*position as usize)
            }
        }
    }
}

/// One frame of the descent: the merge of the levels above it, and where
/// it is in the level below.
struct Frame<'i> {
    merged: Subst,
    cursor: Cursor<'i>,
}

/// The join of `levels` – one list of partial substitutions per trigger –
/// built to be enumerated by [`Join::for_each`].  The index borrows the
/// lists; the enumeration borrows the index.
struct Join<'a> {
    /// The first trigger's substitutions.
    first: &'a [Subst],
    /// Every later trigger's substitutions.
    rest: &'a [Vec<Subst>],
    /// Per later trigger: its buckets on the variables it shares with the
    /// merge so far, when it binds a uniform variable set and so did every
    /// trigger before it. `None` means the level is scanned and tested.
    buckets: Vec<Option<Buckets>>,
}

impl<'a> Join<'a> {
    fn new(levels: &'a [Vec<Subst>]) -> Self {
        let (first, rest): (&[Subst], &[Vec<Subst>]) = match levels.split_first() {
            Some((first, rest)) => (first, rest),
            None => (&[], &[]),
        };
        // The variables the merge has after the triggers so far, while every
        // one of them bound a uniform set; `None` once one did not.
        let mut bound_so_far = uniform_vars(first);
        let mut buckets = Vec::with_capacity(rest.len());
        for level in rest {
            let index = match (&bound_so_far, uniform_vars(level)) {
                (Some(so_far), Some(vars)) => {
                    let mut key_vars: Vec<Spur> = vars
                        .iter()
                        .filter(|var| so_far.contains(*var))
                        .copied()
                        .collect();
                    key_vars.sort_by_key(|var| var.into_inner());
                    bound_so_far = Some(so_far.union(&vars).copied().collect());
                    (!key_vars.is_empty()).then(|| Buckets::build(level, key_vars))
                }
                _ => {
                    bound_so_far = None;
                    None
                }
            };
            buckets.push(index);
        }
        Self {
            first,
            rest,
            buckets,
        }
    }

    /// The cursor into level `depth` of [`Self::rest`] for the merge
    /// `merged` of the levels above it.
    fn cursor<'i>(&'i self, depth: usize, merged: &Subst) -> Cursor<'i> {
        let substs = self.rest[depth].as_slice();
        match self.buckets[depth]
            .as_ref()
            .and_then(|index| index.lookup(merged))
        {
            Some(positions) => Cursor::Bucket {
                substs,
                positions,
                next: 0,
            },
            None => Cursor::Scan { substs, next: 0 },
        }
    }

    /// Visit every consistent merge in cross-product order until `visit`
    /// returns `false`, which stops the enumeration.
    fn for_each(&self, mut visit: impl FnMut(Subst) -> bool) {
        let mut next_first = 0usize;
        let mut stack: Vec<Frame> = Vec::new();
        loop {
            // At the top of the descent, take the next first-level
            // substitution; with a single level it is itself the merge.
            if stack.is_empty() {
                let Some(first) = self.first.get(next_first) else {
                    return;
                };
                next_first += 1;
                if self.rest.is_empty() {
                    if !visit(first.clone()) {
                        return;
                    }
                    continue;
                }
                let merged = first.clone();
                let cursor = self.cursor(0, &merged);
                stack.push(Frame { merged, cursor });
            }
            // Advance the deepest frame by one consistent substitution.
            let advanced = match stack.last_mut() {
                None => return,
                Some(frame) => frame
                    .cursor
                    .next(&frame.merged)
                    .map(|next| merge(&frame.merged, next)),
            };
            let Some(merged) = advanced else {
                stack.pop();
                continue;
            };
            let depth = stack.len();
            if depth == self.rest.len() {
                // Every level merged: one complete binding.
                if !visit(merged) {
                    return;
                }
            } else {
                let cursor = self.cursor(depth, &merged);
                stack.push(Frame { merged, cursor });
            }
        }
    }
}

/// Visit every consistent merge of `levels` – one list of partial
/// substitutions per trigger – in the order the pairwise cross product
/// visited them (first trigger outermost), until `visit` returns `false`,
/// which stops the enumeration.
pub(super) fn for_each_merge(levels: &[Vec<Subst>], visit: impl FnMut(Subst) -> bool) {
    Join::new(levels).for_each(visit);
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]
    use super::*;
    use crate::ast::TermManager;

    /// The variable names the tests bind, by index.
    const NAMES: [&str; 4] = ["w", "x", "y", "z"];

    /// `NAMES`, interned.
    fn spurs(tm: &mut TermManager) -> [Spur; 4] {
        NAMES
            .iter()
            .map(|name| tm.intern_str(name))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap()
    }

    fn subst(spurs: &[Spur; 4], pairs: &[(&str, u32)]) -> Subst {
        pairs
            .iter()
            .map(|&(name, value)| {
                let index = NAMES.iter().position(|&n| n == name).unwrap();
                (spurs[index], TermId::new(value))
            })
            .collect()
    }

    /// A level's substitutions from `(name, value)` pairs.
    fn level(spurs: &[Spur; 4], rows: &[&[(&str, u32)]]) -> Vec<Subst> {
        rows.iter().map(|row| subst(spurs, row)).collect()
    }

    /// `subst` as sorted `(name, term id)` pairs.
    fn spelled<'m>(tm: &'m TermManager, subst: &Subst) -> Vec<(&'m str, u32)> {
        let mut pairs: Vec<(&str, u32)> = subst
            .iter()
            .map(|(name, term)| (tm.resolve_str(*name), term.raw()))
            .collect();
        pairs.sort();
        pairs
    }

    fn spelled_all<'m>(tm: &'m TermManager, substs: &[Subst]) -> Vec<Vec<(&'m str, u32)>> {
        substs.iter().map(|s| spelled(tm, s)).collect()
    }

    /// The retired cross product, kept as the oracle: the pairwise merge
    /// of the accumulated substitutions with each next level's, in order.
    fn cross_product(levels: &[Vec<Subst>]) -> Vec<Subst> {
        let mut combined = levels.first().cloned().unwrap_or_default();
        for next in levels.iter().skip(1) {
            let mut merged = Vec::new();
            for s1 in &combined {
                for s2 in next {
                    if consistent(s1, s2) {
                        merged.push(merge(s1, s2));
                    }
                }
            }
            combined = merged;
        }
        combined
    }

    fn joined(levels: &[Vec<Subst>]) -> Vec<Subst> {
        let mut out = Vec::new();
        for_each_merge(levels, |subst| {
            out.push(subst);
            true
        });
        out
    }

    /// Two triggers sharing their one variable: n values on each side give
    /// n bindings, each in the other side's order.
    #[test]
    fn shared_variable_joins_in_output_order() {
        let mut tm = TermManager::new();
        let spurs = spurs(&mut tm);
        let n = 50u32;
        let f: Vec<Subst> = (0..n).rev().map(|i| subst(&spurs, &[("x", i)])).collect();
        let g: Vec<Subst> = (0..n).map(|i| subst(&spurs, &[("x", i)])).collect();
        let levels = vec![f, g];
        let result = joined(&levels);
        assert_eq!(result.len(), n as usize);
        assert_eq!(spelled(&tm, &result[0]), [("x", n - 1)]);
        assert_eq!(spelled(&tm, &result[n as usize - 1]), [("x", 0)]);
        assert_eq!(
            spelled_all(&tm, &result),
            spelled_all(&tm, &cross_product(&levels))
        );
    }

    /// The indexed join agrees with the cross product, binding for binding
    /// in order, on three triggers: one sharing a variable with the first,
    /// one disjoint, one sharing both – and on a level whose matches bind
    /// differing variables, which is scanned.
    #[test]
    fn indexed_join_matches_the_cross_product_in_order() {
        let mut tm = TermManager::new();
        let spurs = spurs(&mut tm);
        let a = level(&spurs, &[&[("x", 1), ("y", 10)], &[("x", 2), ("y", 20)]]);
        let b = level(
            &spurs,
            &[
                &[("x", 2), ("z", 30)],
                &[("x", 1), ("z", 31)],
                &[("x", 1), ("z", 32)],
            ],
        );
        let disjoint = level(&spurs, &[&[("w", 40)], &[("w", 41)]]);
        let varying = level(&spurs, &[&[("x", 1)], &[("y", 10)], &[]]);
        for levels in [
            vec![a.clone(), b.clone()],
            vec![a.clone(), disjoint.clone()],
            vec![a.clone(), b.clone(), disjoint.clone()],
            vec![a.clone(), varying.clone()],
            vec![a.clone(), b.clone(), varying.clone(), disjoint.clone()],
            vec![a.clone()],
            vec![Vec::new()],
            vec![a.clone(), Vec::new()],
            Vec::new(),
        ] {
            assert_eq!(
                spelled_all(&tm, &joined(&levels)),
                spelled_all(&tm, &cross_product(&levels)),
                "levels {levels:?}"
            );
        }
    }

    /// The enumeration stops when the visitor declines: a disjoint pair with
    /// 256 matches a side yields its first 100 merges and no more.
    #[test]
    fn visitor_can_stop_the_enumeration() {
        let mut tm = TermManager::new();
        let spurs = spurs(&mut tm);
        let f: Vec<Subst> = (0..256).map(|i| subst(&spurs, &[("x", i)])).collect();
        let g: Vec<Subst> = (0..256).map(|i| subst(&spurs, &[("y", i)])).collect();
        let levels = vec![f, g];
        assert_eq!(cross_product(&levels).len(), 65_536);
        let mut count = 0usize;
        for_each_merge(&levels, |_| {
            count += 1;
            count < 100
        });
        assert_eq!(count, 100);
        // ...and the first 100 are the cross product's first 100.
        let mut head = Vec::new();
        for_each_merge(&levels, |subst| {
            head.push(subst);
            head.len() < 100
        });
        assert_eq!(
            spelled_all(&tm, &head),
            spelled_all(&tm, &cross_product(&levels)[..100])
        );
    }
}
