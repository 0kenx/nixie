//! The store-congruence family of lazy array axioms, and the pair enumeration
//! that feeds it.
//!
//! One instance of the store congruence axiom per pair of distinct `store`
//! applications: `(= b1 b2) ∧ (= i1 i2) ∧ (= v1 v2) → (= S1 S2)`.  Only a pair
//! the formula already relates can matter (the emission filter in
//! [`build_store_congruence`]), and those are a small, structurally
//! identifiable subset of the `C(n, 2)` pairs of n stores: on the input terms
//! of the depth-50 `storecomm` benchmark, 2 of 4,950.
//!
//! The pairs used to be found by visiting every pair and testing it – with a
//! clone of both stores' terms per pair, and again per pair that passed.  They
//! are indexed now: the stores are grouped by their base array, the explicit
//! store equalities are attached to the store at the lower term id, and each
//! store's two lists are walked in term-id order.  The pairs thereby arrive in
//! exactly the order the all-pairs filter produced them, so the lemma sequence
//! and the point at which [`MAX_STORE_PAIRS`] cuts it are unchanged (the tests
//! hold the two enumerations to each other), at a cost of n + eligible pairs
//! per refinement round instead of n².
//!
//! `NIXIE_ARRAY_PAIR_LOG` prints that census once per refinement round:
//! stores seen, all pairs, pairs the walk visited, pairs instantiated, and
//! whether the cap cut the sequence.

use crate::prelude::OnceLock;
use core::cmp::Ordering;

use crate::prelude::*;
use nixie_core::ast::{TermId, TermKind, TermManager};

use super::ArrayStructure;

/// Safety cap on the store-congruence pairs one refinement round
/// instantiates.  It counts pairs that pass the emission filter; see that
/// filter for why the unrestricted family is not wanted.
const MAX_STORE_PAIRS: usize = 512;

/// Build one store congruence instance per pair of distinct `store`
/// applications the formula already relates.
///
/// Emission filter (measured 2026-08-29: the unrestricted O(n^2) family
/// cost the differential canary 12 net solves – deep `storecomm`/`pp_sf`
/// chains carry dozens of stores and saturated the refinement loop with
/// hundreds of pairwise implications).  A pair can matter only when the
/// formula already relates the two stores: either their bases are the
/// SAME term (the permutation shape), or the pair's own equality atom is
/// present as an input equality (the goal compares the chains directly).
/// Both are O(n) in practice and cover the store-commutativity shapes
/// exactly; cross-level pairs with distinct bases and no equality atom
/// never close a refutation the other families do not already carry.
///
/// Pairs are visited in `(lower term id, higher term id)` order over the
/// stores sorted by term id, a pair related both ways once.  That is the
/// order the all-pairs loop visited them in, which is what keeps the emitted
/// sequence – and where the cap falls – identical to it.
pub(super) fn build_store_congruence(
    manager: &mut TermManager,
    collected: &ArrayStructure,
    candidates: &mut Vec<TermId>,
    numeric_premise_pairs: &mut Vec<(TermId, TermId)>,
) {
    let mut apps = collected.store_apps.clone();
    apps.sort_unstable_by_key(|t| t.raw());
    apps.dedup();
    let all_pairs = apps.len().saturating_sub(1) * apps.len() / 2;

    // The two relations, as indices: every store's position, the stores over
    // each base in term-id order (each store's rank within its group), and
    // per store the later stores an equality atom relates it to.  The
    // position map also keeps non-store operands of an equality – an array
    // variable aliased to a store – out of the pair list.
    let mut position_of: FxHashMap<TermId, usize> = FxHashMap::default();
    let mut bases: Vec<Option<TermId>> = Vec::with_capacity(apps.len());
    let mut by_base: FxHashMap<TermId, Vec<usize>> = FxHashMap::default();
    for (position, &store) in apps.iter().enumerate() {
        position_of.insert(store, position);
        if let Some(TermKind::Store(base, _, _)) = manager.get(store).map(|node| &node.kind) {
            by_base.entry(*base).or_default().push(position);
            bases.push(Some(*base));
        } else {
            bases.push(None);
        }
    }
    let rank_in_base: Vec<usize> = {
        let mut ranks = vec![usize::MAX; apps.len()];
        for group in by_base.values() {
            for (rank, &position) in group.iter().enumerate() {
                ranks[position] = rank;
            }
        }
        ranks
    };
    let mut by_equality: Vec<Vec<usize>> = vec![Vec::new(); apps.len()];
    for &(a, b) in &collected.eq_pairs {
        let (Some(&lower), Some(&higher)) = (position_of.get(&a), position_of.get(&b)) else {
            continue;
        };
        let (lower, higher) = if lower < higher {
            (lower, higher)
        } else {
            (higher, lower)
        };
        if lower != higher {
            by_equality[lower].push(higher);
        }
    }
    for partners in &mut by_equality {
        partners.sort_unstable();
        partners.dedup();
    }

    let none: [usize; 0] = [];
    let mut pairs = 0usize;
    let mut visited = 0usize;
    let mut capped = false;
    'stores: for (lower, &store) in apps.iter().enumerate() {
        let same_base = bases[lower]
            .and_then(|base| by_base.get(&base))
            .map_or(&none[..], |group| &group[rank_in_base[lower] + 1..]);
        let related = &by_equality[lower];
        let (mut i, mut j) = (0, 0);
        while i < same_base.len() || j < related.len() {
            // The next related store in term-id order; one that stands in
            // both lists (same base AND an explicit equality) is visited once.
            let higher = match (same_base.get(i), related.get(j)) {
                (Some(&a), Some(&b)) => match a.cmp(&b) {
                    Ordering::Less => {
                        i += 1;
                        a
                    }
                    Ordering::Greater => {
                        j += 1;
                        b
                    }
                    Ordering::Equal => {
                        i += 1;
                        j += 1;
                        a
                    }
                },
                (Some(&a), None) => {
                    i += 1;
                    a
                }
                (None, Some(&b)) => {
                    j += 1;
                    b
                }
                (None, None) => break,
            };
            if pairs >= MAX_STORE_PAIRS {
                capped = true;
                break 'stores;
            }
            visited += 1;
            pairs += 1;
            instance(
                manager,
                store,
                apps[higher],
                candidates,
                numeric_premise_pairs,
            );
        }
    }

    if pair_log_enabled() {
        eprintln!(
            "ARRAY-STORE-PAIRS: stores={} all_pairs={} visited={} instantiated={} capped={capped}",
            apps.len(),
            all_pairs,
            visited,
            pairs,
        );
    }
}

/// `(= b1 b2) ∧ (= i1 i2) ∧ (= v1 v2) → (= S1 S2)` for two stores, appended
/// to `candidates`; a pair whose premises are all trivial adds nothing.
///
/// Numeric premise pairs are reported so the caller emits their trichotomy:
/// when the core commits such a premise FALSE, the arithmetic solver owes a
/// strict split it never learns otherwise, and the model collides the two
/// sides (the store-commutativity candidates kept `x = y` for exactly this
/// reason).
fn instance(
    manager: &mut TermManager,
    s1: TermId,
    s2: TermId,
    candidates: &mut Vec<TermId>,
    numeric_premise_pairs: &mut Vec<(TermId, TermId)>,
) {
    let (Some(TermKind::Store(b1, i1, v1)), Some(TermKind::Store(b2, i2, v2))) = (
        manager.get(s1).map(|node| &node.kind),
        manager.get(s2).map(|node| &node.kind),
    ) else {
        return;
    };
    let mut eqs: Vec<TermId> = Vec::new();
    for (l, r) in [(*b1, *b2), (*i1, *i2), (*v1, *v2)] {
        let numeric_pair = |t: &TermId| {
            manager.get(*t).is_some_and(|n| {
                n.sort == manager.sorts.int_sort || n.sort == manager.sorts.real_sort
            })
        };
        if numeric_pair(&l) && numeric_pair(&r) && l != r {
            let key = if l < r { (l, r) } else { (r, l) };
            if !numeric_premise_pairs.contains(&key) {
                numeric_premise_pairs.push(key);
            }
        }
        let e = manager.mk_eq(l, r);
        let trivial = manager
            .get(e)
            .is_some_and(|n| matches!(n.kind, TermKind::True));
        if !trivial {
            eqs.push(e);
        }
    }
    if eqs.is_empty() {
        return;
    }
    let antecedent = manager.mk_and(eqs);
    let conclusion = manager.mk_eq(s1, s2);
    candidates.push(manager.mk_implies(antecedent, conclusion));
}

/// `NIXIE_ARRAY_PAIR_LOG` – the per-round pair census of
/// [`build_store_congruence`].  Read once per process (the site is once per
/// refinement round).
fn pair_log_enabled() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| crate::env::var("NIXIE_ARRAY_PAIR_LOG").is_ok())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The all-pairs loop this module replaced, as the oracle: every pair of
    /// stores visited, each tested for a shared base or an explicit equality.
    /// Its candidate list is the sequence the indexed walk must reproduce.
    fn filtered_store_congruence(
        manager: &mut TermManager,
        collected: &ArrayStructure,
        candidates: &mut Vec<TermId>,
        numeric_premise_pairs: &mut Vec<(TermId, TermId)>,
    ) {
        let mut apps = collected.store_apps.clone();
        apps.sort_unstable_by_key(|t| t.raw());
        apps.dedup();
        let input_pairs: FxHashSet<(TermId, TermId)> = collected
            .eq_pairs
            .iter()
            .map(|(a, b)| if a < b { (*a, *b) } else { (*b, *a) })
            .collect();
        let mut pairs = 0usize;
        for w in 0..apps.len() {
            for v in (w + 1)..apps.len() {
                if pairs >= MAX_STORE_PAIRS {
                    return;
                }
                let (s1, s2) = (apps[w], apps[v]);
                let same_base = |x: TermId, y: TermId| match (
                    manager.get(x).map(|n| n.kind.clone()),
                    manager.get(y).map(|n| n.kind.clone()),
                ) {
                    (Some(TermKind::Store(bx, _, _)), Some(TermKind::Store(by, _, _))) => bx == by,
                    _ => false,
                };
                let key = if s1 < s2 { (s1, s2) } else { (s2, s1) };
                if !same_base(s1, s2) && !input_pairs.contains(&key) {
                    continue;
                }
                pairs += 1;
                instance(manager, s1, s2, candidates, numeric_premise_pairs);
            }
        }
    }

    /// One enumeration's output: the candidate lemmas, then the numeric premise pairs.
    type Family = (Vec<TermId>, Vec<(TermId, TermId)>);

    /// Both enumerations over `roots`: the oracle's and the indexed walk's.
    fn both(roots: &[TermId], manager: &mut TermManager) -> (Family, Family) {
        let mut structure = ArrayStructure::default();
        let mut visited = FxHashSet::default();
        for &root in roots {
            super::super::collect_array_structure(
                root,
                true,
                manager,
                &mut visited,
                &mut structure,
            );
        }
        let (mut expected, mut expected_premises) = (Vec::new(), Vec::new());
        filtered_store_congruence(manager, &structure, &mut expected, &mut expected_premises);
        let (mut found, mut found_premises) = (Vec::new(), Vec::new());
        build_store_congruence(manager, &structure, &mut found, &mut found_premises);
        ((expected, expected_premises), (found, found_premises))
    }

    fn assert_same(roots: &[TermId], manager: &mut TermManager, what: &str) -> usize {
        let ((expected, expected_premises), (found, found_premises)) = both(roots, manager);
        assert_eq!(
            found, expected,
            "{what}: the indexed walk's lemma sequence differs"
        );
        assert_eq!(
            found_premises, expected_premises,
            "{what}: the numeric premise pairs differ"
        );
        found.len()
    }

    /// `store(base, i_1, v_1) … store(·, i_n, v_n)`: a chain of writes.
    fn chain(manager: &mut TermManager, base: TermId, writes: &[(TermId, TermId)]) -> TermId {
        writes.iter().fold(base, |inner, &(index, value)| {
            manager.mk_store(inner, index, value)
        })
    }

    fn setup(depth: usize) -> (TermManager, TermId, Vec<(TermId, TermId)>) {
        let mut manager = TermManager::new();
        let int = manager.sorts.int_sort;
        let array = manager.sorts.array(int, int);
        let base = manager.mk_var("a1", array);
        let writes = (0..depth)
            .map(|k| {
                (
                    manager.mk_var(&format!("i{k}"), int),
                    manager.mk_var(&format!("e{k}"), int),
                )
            })
            .collect();
        (manager, base, writes)
    }

    /// The `storecomm` shape at depth 50: two chains over one base with the
    /// writes in opposite orders, compared by one equality.  100 stores, so
    /// 4,950 pairs – of which two are eligible: the innermost writes (same
    /// base `a1`) and the outermost (the asserted equality).
    #[test]
    fn the_depth_50_storecomm_shape_yields_the_same_two_instances() {
        let (mut manager, base, writes) = setup(50);
        let forward = chain(&mut manager, base, &writes);
        let backward = chain(
            &mut manager,
            base,
            &writes.iter().rev().copied().collect::<Vec<_>>(),
        );
        let equality = manager.mk_eq(forward, backward);
        let roots = [equality, forward, backward];
        let mut structure = ArrayStructure::default();
        let mut visited = FxHashSet::default();
        for &root in &roots {
            super::super::collect_array_structure(
                root,
                true,
                &manager,
                &mut visited,
                &mut structure,
            );
        }
        assert_eq!(structure.store_apps.len(), 100, "two chains of 50 writes");
        assert_eq!(structure.eq_pairs, vec![(forward, backward)]);
        // Sanity on the oracle's count: 2 of C(100, 2).
        assert_eq!(assert_same(&roots, &mut manager, "storecomm depth 50"), 2);
    }

    /// Stores over several bases, equalities recorded in either operand
    /// order and more than once, equalities to non-store arrays, and a pair
    /// that is related both ways: the sequence is the filtered loop's.
    #[test]
    fn mixed_bases_equalities_and_duplicates_keep_the_filtered_sequence() {
        let mut manager = TermManager::new();
        let int = manager.sorts.int_sort;
        let array = manager.sorts.array(int, int);
        let bases: Vec<TermId> = (0..4)
            .map(|b| manager.mk_var(&format!("a{b}"), array))
            .collect();
        let mut stores = Vec::new();
        for (position, &base) in bases.iter().enumerate() {
            for k in 0..7 {
                let index = manager.mk_var(&format!("i{position}-{k}"), int);
                let value = manager.mk_var(&format!("v{position}-{k}"), int);
                stores.push(manager.mk_store(base, index, value));
            }
        }
        let alias = manager.mk_var("alias", array);
        let mut roots: Vec<TermId> = stores.clone();
        // Explicit equalities, each spelled once in each operand order.
        for &(x, y) in &[
            (2usize, 9usize),
            (9, 2),
            (20, 27),
            (27, 20),
            (0, 21),
            (5, 6),
            (6, 5),
        ] {
            roots.push(manager.mk_eq(stores[x], stores[y]));
        }
        // An equality between a store and a plain variable: no pair.
        roots.push(manager.mk_eq(alias, stores[3]));
        roots.push(manager.mk_eq(stores[3], alias));
        let count = assert_same(&roots, &mut manager, "mixed bases");
        // 4 bases × C(7, 2) same-base pairs, plus the cross-base equalities
        // (2, 9), (20, 27), (0, 21); (5, 6) shares base 0 and is related once.
        assert_eq!(count, 4 * 21 + 3);
    }

    /// More same-base pairs than the cap allows – 40 writes straight over one
    /// array, the permutation shape, `C(40, 2) = 780` pairs: both walks stop
    /// after `MAX_STORE_PAIRS` instances, on the same pair.
    #[test]
    fn the_cap_cuts_both_sequences_at_the_same_pair() {
        let (mut manager, base, writes) = setup(40);
        let stores: Vec<TermId> = writes
            .iter()
            .map(|&(index, value)| manager.mk_store(base, index, value))
            .collect();
        assert_eq!(
            assert_same(&stores, &mut manager, "capped"),
            MAX_STORE_PAIRS
        );
    }

    /// Pseudo-random structures over a few bases with scattered equalities
    /// (duplicated and reversed), at several sizes past and short of the cap.
    #[test]
    fn random_structures_match_the_filtered_sequence() {
        for seed in 1u64..=12 {
            let mut rng = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15);
            let mut next = move |bound: usize| {
                rng ^= rng << 13;
                rng ^= rng >> 7;
                rng ^= rng << 17;
                (rng % bound as u64) as usize
            };
            let mut manager = TermManager::new();
            let int = manager.sorts.int_sort;
            let array = manager.sorts.array(int, int);
            let bases: Vec<TermId> = (0..1 + next(4))
                .map(|b| manager.mk_var(&format!("a{b}"), array))
                .collect();
            let stores: Vec<TermId> = (0..20 + next(45))
                .map(|k| {
                    let base = bases[next(bases.len())];
                    let index = manager.mk_var(&format!("i{k}"), int);
                    let value = manager.mk_var(&format!("v{k}"), int);
                    manager.mk_store(base, index, value)
                })
                .collect();
            let mut roots = stores.clone();
            for _ in 0..next(30) {
                let (x, y) = (next(stores.len()), next(stores.len()));
                let (x, y) = if x <= y { (x, y) } else { (y, x) };
                roots.push(manager.mk_eq(stores[x], stores[y]));
                if next(3) == 0 {
                    roots.push(manager.mk_eq(stores[y], stores[x]));
                }
            }
            assert_same(&roots, &mut manager, &format!("seed {seed}"));
        }
    }
}
