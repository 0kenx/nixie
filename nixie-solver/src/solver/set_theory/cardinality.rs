//! Cardinality of finite sets: the Venn-region encoding, done eagerly.
//!
//! # What this decides
//!
//! `|s| = n`, `|s| ≤ n`, `|s ∪ t| = |s| + |t|` with `s ∩ t = ∅`,
//! pigeonhole (`|s| ≥ k` with fewer than `k` elements available),
//! `s ⊆ t` coupled to sizes, and `set.choose`. This is the fragment
//! Dafny/Why3-style specifications actually need: `x ∈ s`, `s ∪ t`,
//! `|s| = n` over *opaque* set variables, which the previous reduction
//! declined (honestly, with `Unknown`) whenever the members were not
//! statically confined to a known list.
//!
//! # How
//!
//! CVC5 solves this lazily (`cardinality_extension.cpp`): a Venn-region
//! partition maintained under the equality engine, with regions materialized
//! as the search needs them. Z3 (2025) runs a *sub-solver* over a Boolean
//! abstraction of set terms plus slack integers, enumerating propositional
//! models of the abstraction and asserting one counting lemma per model
//! (`theory_finite_set_size.cpp`). Neither shape fits an eager reduction, but
//! the mathematics both exploit is the same, and it axiomatizes finitely:
//!
//! For a **cone** of set terms — every set under `set.card`/`set.choose`,
//! closed under the operands of `∪`/`∩`/`\`/`ite`/`~`, their *twins* (the
//! `a ∩ b` of every `a ∪ b` and vice versa), and set-equality/subset
//! neighbours:
//!
//! 1. **Counting equation.** `|s| = Σ_e ite(e ∈ s ∧ e is first of its
//!    equivalence class in s, 1, 0) + slack_s`, with `slack_s ≥ 0`. The sum
//!    runs over the ground elements of the element sort (the same list the
//!    membership definitions use, witnesses included); the "first of its
//!    class" guard is the de-duplication that keeps two *terms* denoting one
//!    *element* from counting twice. `slack_s` is the elements no ground term
//!    mentions. When the members are statically confined to a known list
//!    ([`super::support`] is `Some`), the sum is exact and the slack is
//!    omitted — `{x} ∪ {y}` cannot secretly contain a third element.
//! 2. **Inclusion–exclusion.** `|a ∪ b| + |a ∩ b| = |a| + |b|` and
//!    `|a \ b| + |a ∩ b| = |a|`: the twins exist so these are always
//!    statable. `|ite c a b| = ite c |a| |b|` (exact — no counting equation
//!    of its own), `|∅| = 0`, `|{x}| = 1`.
//! 3. **Slack lattice.** For the *implicit* subset relations among cone
//!    terms (`a ∩ b ⊆ a`, `a ⊆ a ∪ b`, `a \ b ⊆ a`, …) the **slacks** are
//!    monotone: `slack(a ∩ b) ≤ slack(a)`, `slack(a) ≤ slack(a ∪ b)`, …
//!    This, not cardinality monotonicity, is the load-bearing constraint:
//!    the ground parts of the counts are already monotone pointwise (the
//!    membership definitions make `e ∈ a ∩ b` imply `e ∈ a`), so without
//!    tying the *slacks* the same way, a model can populate `a ∩ b` with an
//!    element that is in neither `a` nor `b` — a wrong `sat` (two distinct
//!    members with `|a ∪ b| = 1`).
//! 4. **Subset rules** for the *asserted* `set.subset` atoms in the cone:
//!    the atom implies `|a| ≤ |b|`, and with equal cardinalities forces
//!    `a = b` (a subset of the same size is the whole set).
//! 5. **Non-negativity** `|s| ≥ 0` for every cone set, and, when the element
//!    sort is *finite* with known size `|U|` (Bool, bit-vectors, floats,
//!    finite fields, `RoundingMode`, non-recursive datatypes), the chain
//!    union bound `|s₁ ∪ … ∪ sₖ| ≤ |U|`, which by inclusion–exclusion is
//!    exactly the statement that the region counts sum within the universe.
//! 6. **Complement**, over a finite element sort only:
//!    `|~s| + |s| = |U|`. Over an infinite element sort a complement inside
//!    the cone has no integer cardinality at all (every constraint on it is
//!    unsatisfiable), which this encoding cannot derive, so it raises the
//!    honesty gate instead of guessing.
//! 7. **Choose**: `choose(s) ∈ s ↔ |s| ≥ 1` — CVC5's `SET_CHOOSE` axiom.
//!
//! # Why that is enough (and not too much)
//!
//! Every clause above is a *valid* consequence of the theory of finite sets,
//! so conjoining them preserves both `sat` and `unsat`. The converse — that
//! any assignment satisfying the encoding realizes an actual set family —
//! holds because the constraints are exactly the characterization of
//! *measures on a distributive lattice*: a monotone, modular, non-negative
//! function on a `∪`/`∩`-closed family of sets is the restriction of a
//! measure over the Venn regions (each region contributing one integer).
//! The counting equations pin the regions inhabited by ground elements, the
//! slacks are the regions empty of ground elements, and over an infinite
//! element sort every assignment of non-negative region counts is realizable
//! by distinct fresh elements. Over a finite sort, clause 5 is what keeps the
//! realization inside the universe.
//!
//! # Caps
//!
//! The cone is capped ([`MAX_CONE_SETS`]), and so is the element list that
//! the counting sums run over ([`MAX_COUNT_ELEMENTS`]) because the
//! de-duplication guards are quadratic in it. Overflowing a cap raises the
//! honesty gate — the price of the bound is `Unknown`, never a silently
//! weaker encoding.

use crate::prelude::*;
use nixie_core::{SortId, TermId, TermManager};
use num_bigint::BigInt;

use super::{Shape, Survey, element_sort, shape_of, support};

/// Cap on the number of set terms in one element sort's counting cone.
fn max_cone_sets() -> usize {
    crate::solver::caps::cap("set_cone_sets", 40)
}

/// Cap on the number of ground elements the counting sums run over; the
/// de-duplication guards are quadratic in this. Env-overridable and
/// reported on firing — see [`crate::solver::caps`].
fn max_count_elements() -> usize {
    crate::solver::caps::cap("set_count_elements", 24)
}

/// The outcome of the cardinality reduction.
pub(super) struct CardOutcome {
    /// Whether a construct outside this encoding was seen; the caller must
    /// keep the honesty gate raised.
    pub(super) incomplete: bool,
    /// Set terms created here (twins, chain unions) that the caller's
    /// membership-definition loop must cover.
    pub(super) extra_sets: Vec<TermId>,
}

/// The element universe of a sort, as far as cardinality needs it.
#[derive(Debug, Clone)]
enum Universe {
    /// Exactly known, finite inhabitant count.
    Finite(BigInt),
    /// Genuinely infinite (or an uninterpreted sort, whose cardinality the
    /// theory never bounds above): slack regions are always realizable.
    Infinite,
    /// Cannot be classified (a sort parameter, or a kind added since); the
    /// caller gates rather than assuming.
    Unknown,
}

/// Classify an element sort's universe.
fn universe_of(sort: SortId, manager: &TermManager) -> Universe {
    let Some(data) = manager.sorts.get(sort) else {
        return Universe::Unknown;
    };
    match &data.kind {
        nixie_core::SortKind::Bool => Universe::Finite(BigInt::from(2)),
        nixie_core::SortKind::BitVec(w) => {
            // 2^w exactly: an 8 KiB number at the parser's width cap.
            Universe::Finite(BigInt::from(2).pow(*w))
        }
        nixie_core::SortKind::FloatingPoint { eb, sb } => {
            // 2^(eb+sb) exactly — every bit pattern is one value.
            match u32::try_from(u64::from(*eb) + u64::from(*sb)) {
                Ok(bits) => Universe::Finite(BigInt::from(2).pow(bits)),
                Err(_) => Universe::Unknown,
            }
        }
        nixie_core::SortKind::FiniteField(id) => match manager.sorts.field_desc(*id) {
            Some(desc) => Universe::Finite(BigInt::from(desc.modulus().clone())),
            None => Universe::Unknown,
        },
        // The five rounding modes are exactly the five named values.
        nixie_core::SortKind::RoundingMode => Universe::Finite(BigInt::from(5)),
        nixie_core::SortKind::Int
        | nixie_core::SortKind::Real
        | nixie_core::SortKind::String
        | nixie_core::SortKind::Set(_)
        | nixie_core::SortKind::Bag(_)
        | nixie_core::SortKind::Array { .. }
        | nixie_core::SortKind::Uninterpreted(_) => Universe::Infinite,
        // A non-recursive datatype has a computable finite size; a recursive
        // one is infinite (unbounded construction depth). Both are decided by
        // the cycle-aware walk below.
        nixie_core::SortKind::Datatype(_) => match manager.sorts.datatype_name(sort) {
            Some(name) => datatype_universe(name, manager, &mut Vec::new()),
            None => Universe::Unknown,
        },
        nixie_core::SortKind::Parameter(_) | nixie_core::SortKind::Parametric { .. } => {
            Universe::Unknown
        }
    }
}

/// Size of a datatype: the sum over constructors of the products of their
/// argument sorts' sizes. A recursive reference (found through the active
/// chain) makes the sort infinite; an argument whose own size is unknown or
/// infinite makes this one infinite-or-unknown, never a fabricated finite
/// number.
fn datatype_universe(name: &str, manager: &TermManager, chain: &mut Vec<String>) -> Universe {
    if chain.iter().any(|n| n == name) {
        return Universe::Infinite;
    }
    let Some(def) = manager.sorts.get_datatype(name) else {
        return Universe::Unknown;
    };
    chain.push(name.to_string());
    let mut total = BigInt::from(0);
    for ctor in &def.constructors {
        let mut product = BigInt::from(1);
        for (_, arg_sort) in &ctor.selectors {
            match universe_of(*arg_sort, manager) {
                Universe::Finite(n) => product *= n,
                Universe::Infinite => {
                    chain.pop();
                    return Universe::Infinite;
                }
                Universe::Unknown => {
                    chain.pop();
                    return Universe::Unknown;
                }
            }
        }
        total += product;
    }
    chain.pop();
    Universe::Finite(total)
}

/// Per-sort working state for the emission phase.
struct Cone {
    /// The cone's set terms.
    sets: Vec<TermId>,
    /// Membership test.
    in_cone: FxHashSet<TermId>,
    /// Card term per cone set (surveyed when present, fresh otherwise).
    card_of: FxHashMap<TermId, TermId>,
    /// Slack variable per cone set that has one (support-unknown sets).
    slack_of: FxHashMap<TermId, TermId>,
}

impl Cone {
    /// `|x| ≤ |y|` for two cone sets.
    fn card_le(&self, x: TermId, y: TermId, manager: &mut TermManager, axioms: &mut Vec<TermId>) {
        if let (Some(cx), Some(cy)) = (self.card_of.get(&x), self.card_of.get(&y)) {
            axioms.push(manager.mk_le(*cx, *cy));
        }
    }

    /// `slack(x) ≤ slack(y)` — the lattice constraint on the
    /// no-ground-element regions, which is what keeps an element of `x` (as a
    /// subset of `y`) counted in `y`'s slack as well. Emitted only when both
    /// sides have a slack; an exact-count set has no region the constraint
    /// could talk about, and its count is already monotone pointwise.
    fn slack_le(&self, x: TermId, y: TermId, manager: &mut TermManager, axioms: &mut Vec<TermId>) {
        if let (Some(sx), Some(sy)) = (self.slack_of.get(&x), self.slack_of.get(&y)) {
            axioms.push(manager.mk_le(*sx, *sy));
        }
    }
}

/// Emit the cardinality encoding for the whole survey.
///
/// `elements` is the element map after the disequality witnesses were added
/// (they are ground elements of their sort like any other, and the counting
/// sums must see them).
pub(super) fn reduce(
    s: &Survey,
    elements: &FxHashMap<SortId, Vec<TermId>>,
    relations: &[(TermId, TermId)],
    eq_pairs: &[(TermId, TermId)],
    manager: &mut TermManager,
    axioms: &mut Vec<TermId>,
) -> CardOutcome {
    let mut incomplete = false;
    let mut extra_sets: Vec<TermId> = Vec::new();

    // Group the seeds by element sort; sorts with no cardinality or choose
    // seed have no cone at all.
    let mut seeds_by_sort: FxHashMap<SortId, Vec<TermId>> = FxHashMap::default();
    for &(_, set) in s.cardinalities.iter().chain(s.chooses.iter()) {
        if let Some(es) = element_sort(set, manager) {
            seeds_by_sort.entry(es).or_default().push(set);
        }
    }

    for (elem_sort, seeds) in seeds_by_sort {
        let universe = universe_of(elem_sort, manager);
        if matches!(universe, Universe::Unknown) {
            incomplete = true;
        }

        // ---- the cone ----
        let mut cone = Cone {
            sets: Vec::new(),
            in_cone: FxHashSet::default(),
            card_of: FxHashMap::default(),
            slack_of: FxHashMap::default(),
        };
        let mut worklist: Vec<TermId> = seeds;
        let mut capped = false;
        while let Some(t) = worklist.pop() {
            if !cone.in_cone.insert(t) {
                continue;
            }
            cone.sets.push(t);
            let cap = max_cone_sets();
            if cone.sets.len() > cap {
                crate::solver::caps::report_fired("set_cone_sets", cone.sets.len(), cap);
                capped = true;
                break;
            }
            match shape_of(t, manager) {
                // The relation operators: leaves of the cone. Their
                // operands live in *other element sorts* (the joined,
                // paired or transposed tuple sorts), so same-sort
                // inclusion-exclusion does not cross them; each sort's
                // counting equations cover the ground elements the
                // reduction derives, and `iden`'s diagonal count is
                // stated directly below.
                Shape::Join(_, _) | Shape::Product(_, _) | Shape::Transpose(_) | Shape::Iden(_) => {
                }
                Shape::Union(a, b) | Shape::Inter(a, b) => {
                    worklist.push(a);
                    worklist.push(b);
                    // The twin: the other half of the inclusion–exclusion
                    // pair, created (hash-consed, so call-stable) if the
                    // formula has no such term of its own.
                    let twin = if matches!(shape_of(t, manager), Shape::Union(_, _)) {
                        manager.mk_set_inter(a, b)
                    } else {
                        manager.mk_set_union(a, b)
                    };
                    extra_sets.push(twin);
                    worklist.push(twin);
                }
                Shape::Minus(a, b) => {
                    worklist.push(a);
                    worklist.push(b);
                    let twin = manager.mk_set_inter(a, b);
                    extra_sets.push(twin);
                    worklist.push(twin);
                }
                Shape::Complement(a) => {
                    worklist.push(a);
                }
                Shape::Ite(_, a, b) => {
                    worklist.push(a);
                    worklist.push(b);
                }
                Shape::Empty | Shape::Univ | Shape::Singleton(_) | Shape::Opaque => {}
            }
            // Relation neighbours: a set joined to the cone by an asserted
            // equality or subset — or by one of the implicit opaque pairs
            // [`super::reduce`] relates — carries cardinality information
            // across the relation, so it joins the cone (Z3's
            // `collect_subexpressions` walks eq/diseq watch lists for the
            // same reason). The implicit pairs matter as much as the
            // asserted ones: a *derived* equality (`x = y` merging
            // `f x`/`f y`, an array `select` collapsing onto a stored set)
            // constrains the two sizes just as hard, and the equality⇒card
            // rule below needs both sides in the cone to state it.
            for &(a, b) in relations {
                if a == t {
                    worklist.push(b);
                } else if b == t {
                    worklist.push(a);
                }
            }
        }
        if capped {
            incomplete = true;
            continue;
        }

        // ---- card and slack terms ----
        for &set in &cone.sets {
            let existing = s
                .cardinalities
                .iter()
                .find(|&&(_, x)| x == set)
                .map(|&(c, _)| c);
            let card = match existing {
                Some(c) => c,
                None => manager.mk_set_card(set),
            };
            cone.card_of.insert(set, card);
        }

        // ---- equality ⇒ equal cardinality ----
        //
        // Z3's `theory_finite_set_size::add_eq_axioms` ties the Boolean
        // abstractions of every asserted-equal pair together, which
        // equalizes their sizes through the sub-solver. The eager analogue
        // is one implication per equality relation with both sides in the
        // cone. Without it the two card terms of one set were unrelated
        // Booleans-and-integers, and each of these answered `Sat`:
        //
        // ```text
        // S = T  ∧  |S| = 5  ∧  |T| = 3          (equal sets, unequal sizes)
        // S = ∅  ∧  |S| ≥ 1                    (the empty set is not empty)
        // x = y  ∧  |f x| = 5  ∧  |f y| = 3      (EUF-derived, implicit pair)
        // S = {1} ∪ {2}  ∧  |S| = 5              (compound operand, asserted)
        // ```
        //
        // `subset` needs no analogue here: `atom → |a| ≤ |b|` below is the
        // one-directional rule, and the same-size forcing goes through this
        // rule once `|a| = |b|` yields `a = b` (also below).
        for &(a, b) in eq_pairs {
            if let (Some(ca), Some(cb)) =
                (cone.card_of.get(&a).copied(), cone.card_of.get(&b).copied())
            {
                let atom = manager.mk_eq(a, b);
                let same = manager.mk_eq(ca, cb);
                axioms.push(manager.mk_implies(atom, same));
            }
        }

        // ---- the ground elements the sums run over ----
        let empty_list: Vec<TermId> = Vec::new();
        let ground_elements: &[TermId] = elements.get(&elem_sort).unwrap_or(&empty_list);
        let cap = max_count_elements();
        if ground_elements.len() > cap {
            // The de-duplication guards are quadratic; decline honestly
            // rather than emit a quadratic blowup or (worse) an
            // under-constrained sum.
            crate::solver::caps::report_fired("set_count_elements", ground_elements.len(), cap);
            incomplete = true;
            continue;
        }

        // The slack variables, one per support-unknown cone set, keyed by the
        // **element list of this pass**. `reduce` re-runs on every `assert`
        // over the whole stack, and the list grows as new assertions (and the
        // previous passes' own conjoined axioms) are surveyed; two counting
        // equations over different lists must not share a slack, or their
        // conjunction degenerates into "the newer elements contribute
        // nothing" — a false `unsat` on the most ordinary input
        // (`|s| = 2` asserted before `1 \in s`).
        for &set in &cone.sets {
            if support(set, manager, 0).is_none()
                && !matches!(
                    shape_of(set, manager),
                    Shape::Empty | Shape::Singleton(_) | Shape::Univ | Shape::Ite(_, _, _)
                )
            {
                let slack = list_keyed_slack(set, ground_elements, manager);
                cone.slack_of.insert(set, slack);
            }
        }

        let zero = manager.mk_int(0);
        for &set in &cone.sets {
            let card = cone.card_of[&set];
            // Non-negativity: valid, and load-bearing (the complement
            // identity and the subset rules can otherwise drive a
            // cardinality negative, which no set has).
            axioms.push(manager.mk_ge(card, zero));
            // slack ≥ 0: the no-ground-element regions are sets of elements.
            if let Some(&slack) = cone.slack_of.get(&set) {
                axioms.push(manager.mk_ge(slack, zero));
            }

            match shape_of(set, manager) {
                Shape::Empty => {
                    axioms.push(manager.mk_eq(card, zero));
                }
                Shape::Singleton(_) => {
                    let one = manager.mk_int(1);
                    axioms.push(manager.mk_eq(card, one));
                }
                Shape::Univ => match &universe {
                    Universe::Finite(n) => {
                        let bound = manager.mk_int(n.clone());
                        axioms.push(manager.mk_eq(card, bound));
                    }
                    Universe::Infinite | Universe::Unknown => {
                        // An infinite universe has no integer cardinality;
                        // any constraint on |U| is unsatisfiable, which this
                        // encoding cannot derive — gate.
                        incomplete = true;
                    }
                },
                Shape::Complement(inner) => {
                    let Some(inner_card) = cone.card_of.get(&inner).copied() else {
                        continue;
                    };
                    match &universe {
                        Universe::Finite(n) => {
                            let total = manager.mk_int(n.clone());
                            let sum = manager.mk_add([card, inner_card]);
                            axioms.push(manager.mk_eq(sum, total));
                            // ~s ⊆ U, as a cardinality bound.
                            axioms.push(manager.mk_le(card, total));
                        }
                        Universe::Infinite | Universe::Unknown => {
                            // |~s| has no finite value over an infinite
                            // universe; every constraint on it is
                            // unsatisfiable, which this encoding cannot
                            // derive — gate.
                            incomplete = true;
                        }
                    }
                }
                Shape::Union(a, b) => {
                    let (Some(ca), Some(cb)) =
                        (cone.card_of.get(&a).copied(), cone.card_of.get(&b).copied())
                    else {
                        continue;
                    };
                    let m = manager.mk_set_inter(a, b);
                    let Some(cm) = cone.card_of.get(&m).copied() else {
                        continue;
                    };
                    // |a| + |b| = |a ∪ b| + |a ∩ b|
                    let lhs = manager.mk_add([ca, cb]);
                    let rhs = manager.mk_add([card, cm]);
                    axioms.push(manager.mk_eq(lhs, rhs));
                    // a, b ⊆ a ∪ b, on the slacks and (redundantly but
                    // robustly, covering support-exact operands) the cards.
                    cone.slack_le(a, set, manager, axioms);
                    cone.slack_le(b, set, manager, axioms);
                    cone.card_le(a, set, manager, axioms);
                    cone.card_le(b, set, manager, axioms);
                    counting_equation(&cone, set, card, ground_elements, manager, axioms);
                }
                Shape::Inter(a, b) => {
                    let (Some(ca), Some(cb)) =
                        (cone.card_of.get(&a).copied(), cone.card_of.get(&b).copied())
                    else {
                        continue;
                    };
                    let u = manager.mk_set_union(a, b);
                    let Some(cu) = cone.card_of.get(&u).copied() else {
                        continue;
                    };
                    // |a| + |b| = |a ∪ b| + |a ∩ b| — the same formula the
                    // union arm states; hash-consing makes the duplicate
                    // harmless and the final dedup removes it.
                    let lhs = manager.mk_add([ca, cb]);
                    let rhs = manager.mk_add([cu, card]);
                    axioms.push(manager.mk_eq(lhs, rhs));
                    // a ∩ b ⊆ a, a ∩ b ⊆ b
                    cone.slack_le(set, a, manager, axioms);
                    cone.slack_le(set, b, manager, axioms);
                    cone.card_le(set, a, manager, axioms);
                    cone.card_le(set, b, manager, axioms);
                    counting_equation(&cone, set, card, ground_elements, manager, axioms);
                }
                Shape::Minus(a, b) => {
                    let Some(ca) = cone.card_of.get(&a).copied() else {
                        continue;
                    };
                    let m = manager.mk_set_inter(a, b);
                    let Some(cm) = cone.card_of.get(&m).copied() else {
                        continue;
                    };
                    // |a \ b| + |a ∩ b| = |a|
                    let lhs = manager.mk_add([card, cm]);
                    axioms.push(manager.mk_eq(lhs, ca));
                    // a \ b ⊆ a; a ∩ b ⊆ a, a ∩ b ⊆ b
                    cone.slack_le(set, a, manager, axioms);
                    cone.slack_le(m, a, manager, axioms);
                    cone.slack_le(m, b, manager, axioms);
                    cone.card_le(set, a, manager, axioms);
                    counting_equation(&cone, set, card, ground_elements, manager, axioms);
                }
                Shape::Ite(c, a, b) => {
                    let (Some(ca), Some(cb)) =
                        (cone.card_of.get(&a).copied(), cone.card_of.get(&b).copied())
                    else {
                        continue;
                    };
                    // Exact: |ite c a b| = ite c |a| |b|. No counting equation
                    // and no slack — the set *is* one of the branches.
                    let picked = manager.mk_ite(c, ca, cb);
                    axioms.push(manager.mk_eq(card, picked));
                }
                Shape::Opaque => {
                    counting_equation(&cone, set, card, ground_elements, manager, axioms);
                }
                // `|transpose r| = |r|`: the converse is a bijection.
                Shape::Transpose(r) => {
                    let r_card = manager.mk_set_card(r);
                    axioms.push(manager.mk_eq(card, r_card));
                    counting_equation(&cone, set, card, ground_elements, manager, axioms);
                }
                // `|a × b| = |a| · |b|`: the product pairs members exactly.
                // Emitted only when the product's own support is not exact
                // — an exact support's counting equation already pins the
                // count, and the (nonlinear) multiplication would route the
                // constraint through the arithmetic honesty gate for
                // nothing. Where it IS emitted, that gate is the honest
                // price of the rule (a wrong bound would be worse).
                Shape::Product(a, b) => {
                    if support(set, manager, 0).is_none() {
                        let ca = manager.mk_set_card(a);
                        let cb = manager.mk_set_card(b);
                        let prod = manager.mk_mul([ca, cb]);
                        axioms.push(manager.mk_eq(card, prod));
                    }
                    counting_equation(&cone, set, card, ground_elements, manager, axioms);
                }
                // `|r ⨝ s| ≤ |r| · |s|`: every joined member consumes a
                // connecting pair. Without this bound the join's slack was
                // unconstrained above and `|J| = 2` with `|r| = |s| = 1`
                // answered `sat` — a false `sat`, since `J` is determined
                // by its operands.
                Shape::Join(r1, r2) => {
                    let c1 = manager.mk_set_card(r1);
                    let c2 = manager.mk_set_card(r2);
                    let prod = manager.mk_mul([c1, c2]);
                    axioms.push(manager.mk_le(card, prod));
                    counting_equation(&cone, set, card, ground_elements, manager, axioms);
                }
                // `|iden s| = |s|`: the diagonal is in bijection with the
                // operand. The operand lives in another element sort, so
                // its card term is minted here (hash-consed: a formula that
                // constrains it shares the term).
                Shape::Iden(x) => {
                    let x_card = manager.mk_set_card(x);
                    axioms.push(manager.mk_eq(card, x_card));
                }
            }
        }

        // ---- asserted subset rules ----
        for &(atom, a, b) in &s.subsets {
            if cone.in_cone.contains(&a) && cone.in_cone.contains(&b) {
                let (Some(ca), Some(cb)) =
                    (cone.card_of.get(&a).copied(), cone.card_of.get(&b).copied())
                else {
                    continue;
                };
                // atom → |a| ≤ |b|
                let le = manager.mk_le(ca, cb);
                axioms.push(manager.mk_implies(atom, le));
                // atom ∧ |a| = |b| → a = b: a subset of the same size is the
                // whole set. This is the completeness half of subset +
                // cardinality reasoning (CVC5's `checkCardinality`).
                let same = manager.mk_eq(ca, cb);
                let prem = manager.mk_and([atom, same]);
                let eq = manager.mk_eq(a, b);
                axioms.push(manager.mk_implies(prem, eq));
                // The slack of the smaller set is available to the larger.
                cone.slack_le(a, b, manager, axioms);
            }
        }

        // ---- the finite-universe bound ----
        // |s₁ ∪ … ∪ sₖ| ≤ |U| over the chain union: by inclusion–exclusion
        // the chain's cardinality is the sum over exactly the non-empty Venn
        // regions, so this one bound is the whole "region counts fit the
        // universe" constraint.
        if let (Universe::Finite(n), Some(&first)) = (&universe, cone.sets.first()) {
            let mut chain = first;
            for &set in cone.sets.iter().skip(1) {
                let next = manager.mk_set_union(chain, set);
                let twin = manager.mk_set_inter(chain, set);
                let (Some(c_chain), Some(c_set)) = (
                    cone.card_of.get(&chain).copied(),
                    cone.card_of.get(&set).copied(),
                ) else {
                    chain = next;
                    extra_sets.push(next);
                    extra_sets.push(twin);
                    continue;
                };
                let c_next = manager.mk_set_card(next);
                let c_twin = manager.mk_set_card(twin);
                let zero = manager.mk_int(0);
                axioms.push(manager.mk_ge(c_next, zero));
                let lhs = manager.mk_add([c_chain, c_set]);
                let rhs = manager.mk_add([c_next, c_twin]);
                axioms.push(manager.mk_eq(lhs, rhs));
                axioms.push(manager.mk_le(c_chain, c_next));
                axioms.push(manager.mk_le(c_set, c_next));
                extra_sets.push(next);
                extra_sets.push(twin);
                chain = next;
            }
            let total = manager.mk_int(n.clone());
            let chain_card = manager.mk_set_card(chain);
            axioms.push(manager.mk_le(chain_card, total));
        }

        // ---- choose ----
        for &(choose, set) in &s.chooses {
            let Some(&card) = cone.card_of.get(&set) else {
                continue;
            };
            let member = manager.mk_set_member(choose, set);
            let one = manager.mk_int(1);
            let nonempty = manager.mk_ge(card, one);
            // choose(s) ∈ s ↔ |s| ≥ 1: the forward direction is "a member
            // exists", the backward is "choose picks one". Congruence
            // (s = t → choose s = choose t) comes from EUF.
            axioms.push(manager.mk_eq(member, nonempty));
        }
    }

    CardOutcome {
        incomplete,
        extra_sets,
    }
}

/// The counting equation for one set: `|s| = Σ_e ite(e counts, 1, 0) +
/// slack_s`, where the sum runs over the support list when the members are
/// statically confined ([`super::support`]) and over the ground elements
/// otherwise.
///
/// `e` contributes `1` exactly when `e ∈ s` and no *earlier* element of the
/// list that is equal to `e` is also in `s`: one representative per
/// equivalence class, so two terms denoting one value count once. The guard
/// is an equality *atom*, which the SAT/EUF layer decides, so classes merge
/// dynamically rather than syntactically.
fn counting_equation(
    cone: &Cone,
    set: TermId,
    card: TermId,
    ground_elements: &[TermId],
    manager: &mut TermManager,
    axioms: &mut Vec<TermId>,
) {
    let support_list = support(set, manager, 0);
    let list: &[TermId] = match &support_list {
        Some(sup) => sup,
        None => ground_elements,
    };
    let zero = manager.mk_int(0);
    let one = manager.mk_int(1);
    let mut terms: Vec<TermId> = Vec::with_capacity(list.len());
    for (i, &e) in list.iter().enumerate() {
        let present = manager.mk_set_member(e, set);
        let mut counts = vec![present];
        for &earlier in &list[..i] {
            let earlier_in = manager.mk_set_member(earlier, set);
            let same = manager.mk_eq(e, earlier);
            let dup = manager.mk_and([earlier_in, same]);
            counts.push(manager.mk_not(dup));
        }
        let fresh = manager.mk_and(counts);
        terms.push(manager.mk_ite(fresh, one, zero));
    }
    let total = if terms.is_empty() {
        zero
    } else {
        manager.mk_add(terms)
    };
    match cone.slack_of.get(&set).copied() {
        Some(slack) => {
            let sum = manager.mk_add([total, slack]);
            axioms.push(manager.mk_eq(card, sum));
        }
        None => {
            axioms.push(manager.mk_eq(card, total));
        }
    }
}

/// The slack variable for one (set, element-list) pair.
///
/// The list is part of the variable's identity because `reduce` re-runs on
/// every `assert` over the whole stack, and the element list grows as new
/// assertions (and the previous passes' own conjoined axioms) are surveyed.
/// Two counting equations over *different* lists must not share a slack:
/// each equation says `|s| = Σ_list + slack`, and sharing would conjoin them
/// into "the new elements contribute nothing" — a false `unsat` on the most
/// ordinary input (`|s| = 2` then `1 ∈ s`).
fn list_keyed_slack(set: TermId, list: &[TermId], manager: &mut TermManager) -> TermId {
    let mut name = format!("@set_card_slack_{}", set.0);
    for e in list {
        name.push_str(&format!("_{}", e.0));
    }
    manager.mk_var(&name, manager.sorts.int_sort)
}
