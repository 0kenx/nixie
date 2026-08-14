//! Lazy array-theory axiom instantiation for the CDCL(T) loop.
//!
//! The syntactic pre-checks in [`super::check_array`] recognise a fixed set of
//! definite array conflicts, but they cannot decide the general case — e.g. a
//! read-over-write at a *provably different* index (`i != j` forcing
//! `select(store(a,i,v),j) = select(a,j)`), or extensionality on a disequality
//! between two array variables.  Left to the raw SAT core those atoms are free
//! Booleans, which risks a spurious `Sat`.
//!
//! This module supplies the missing decision power as a *lazy* refinement loop
//! driven from [`super::Solver::check`]: whenever the CDCL(T) core proposes a
//! candidate model, [`Solver::instantiate_array_axioms`] inspects the array
//! terms in that model and, for every array axiom instance the candidate does
//! not already satisfy, asserts the corresponding ground lemma and asks the
//! core to re-solve.  The three axiom families are:
//!
//!   * **Read-over-write** — for every `select(store(b,i,v), j)` (directly or
//!     through an asserted `B = store(b,i,v)` alias):
//!     `select(store(b,i,v),j) = ite(i = j, v, select(b,j))`.
//!   * **Extensionality** — for every array-sorted equality atom `a = b`, a
//!     witness index `k` (fresh but *deterministic* per unordered pair) with
//!     `a = b  ∨  select(a,k) != select(b,k)`.  When `a != b` is asserted this
//!     forces a concrete differing index.
//!   * **Select congruence** — for every array-sorted equality atom `a = b`
//!     and every index `j` read on either side:
//!     `a = b  ⇒  select(a,j) = select(b,j)`.
//!
//! Every asserted instance is a theorem of the (extensional) array theory, so
//! adding it never changes satisfiability — it only removes models that violate
//! array semantics.  Instances are deduplicated by their interned lemma term
//! id, and the reachable instance set is finite (bounded by the store-subterm ×
//! index-set product plus one witness per array pair), so the refinement loop
//! in `check` terminates: each round either asserts a strictly new instance or
//! reports that the candidate model is a genuine array model.
//!
//! Reference: Z3's `smt/theory_array.cpp` semantics (read-over-write and
//! extensionality axiom instantiation).

#[allow(unused_imports)]
use crate::prelude::*;
use oxiz_core::SortKind;
use oxiz_core::ast::{TermId, TermKind, TermManager, get_children};
use oxiz_core::sort::SortId;

use super::{EvalVal, Solver};

/// Safety valve on the number of distinct array-axiom instances asserted across
/// a single `check`.  Deduplication is the real termination mechanism; this cap
/// only guards against pathological growth (deeply nested store chains crossed
/// with many array pairs) so a malformed input cannot make the refinement loop
/// consume unbounded memory.  Realistic array benchmarks add a handful of
/// instances.
const MAX_ARRAY_AXIOM_INSTANCES: usize = 20_000;

impl Solver {
    /// One round of lazy array-axiom instantiation against the current candidate
    /// model.  Returns `true` when at least one new ground array lemma was
    /// asserted to the SAT core — in which case the caller must re-solve — and
    /// `false` when the candidate model already satisfies every applicable
    /// axiom instance (so the reported `Sat` is trustworthy for the array
    /// atoms).
    pub(super) fn instantiate_array_axioms(&mut self, manager: &mut TermManager) -> bool {
        if self.array_axiom_instances.len() >= MAX_ARRAY_AXIOM_INSTANCES {
            return false;
        }

        // ---- Phase 1: collect array structure ---------------------------
        // Walk both the user assertions and every axiom instance asserted so
        // far, so selects introduced by earlier read-over-write / extensionality
        // lemmas seed further instantiation (saturation).
        let roots: Vec<TermId> = self
            .assertions
            .iter()
            .copied()
            .chain(self.array_axiom_instances.iter().copied())
            .collect();

        let mut collected = ArrayStructure::default();
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        for &root in &roots {
            collect_array_structure(root, manager, &mut visited, &mut collected);
        }

        if collected.selects.is_empty() && collected.eq_pairs.is_empty() {
            return false;
        }

        // ---- Phase 2: build candidate ground axiom instances ------------
        // Build extensionality first so its *complete* finite-disjunction
        // clauses can tell `build_read_over_write` which arrays need no eager
        // chain unfolding (the lever for deep `storecomm` chains).
        let mut candidates: Vec<TermId> = Vec::new();
        let no_eager = build_extensionality_and_congruence(manager, &collected, &mut candidates);
        build_read_over_write(manager, &collected, &no_eager, &mut candidates);
        // Array-congruence at store-chain write indices: for an inline array
        // equality `(= A B)` whose store chain exposes write indices, assert
        // the theorem `(= A B) ⇒ (= (select A i) (select B i))` per write index.
        // This is entailed by the array theory (it can change no verdict), but
        // it materialises `select(var, store_idx)` atoms the lazy
        // read-over-write pass never creates when the variable is unread at the
        // store index -- the ingredient a conditional `(= (store…) var)` inside
        // an `ite` needs to propagate its read-over-write consequences (the
        // `cvc/read8` shape).
        build_equality_read_congruence(manager, &collected, &mut candidates);

        // ---- Phase 3: filter (dedup + model) and assert -----------------
        // Only instances the candidate model does not already *definitely*
        // satisfy are added.  A `None` evaluation (opaque/undetermined) is
        // treated as unsatisfied so completeness never depends on the model
        // being able to evaluate a select — worst case this degenerates to
        // eager instantiation, which is still sound and complete.
        let mut to_add: Vec<TermId> = Vec::new();
        {
            let model = self.model.as_ref();
            for &inst in &candidates {
                if self.array_axiom_instances.contains(&inst) {
                    continue;
                }
                let already_satisfied = match model {
                    Some(m) => matches!(
                        self.eval_in_model(inst, m, manager, 0),
                        Some(EvalVal::Bool(true))
                    ),
                    None => false,
                };
                if already_satisfied {
                    continue;
                }
                to_add.push(inst);
            }
        }

        let mut added = false;
        for inst in to_add {
            if self.array_axiom_instances.len() >= MAX_ARRAY_AXIOM_INSTANCES {
                break;
            }
            // `insert` returns false if this exact instance is already tracked
            // (it may appear twice within one candidate batch).
            if !self.array_axiom_instances.insert(inst) {
                continue;
            }
            // Journal the instance so a `pop` retracts the dedup entry together
            // with the lemma clause the SAT core drops: keeping the entry would
            // silently suppress an axiom a later scope still needs.
            self.trail
                .push(super::trail::TrailOp::ArrayAxiomInstanceAdded { term: inst });
            let lit = self.encode(inst, manager);
            let _ = self.sat.add_clause([lit]);
            added = true;
        }

        added
    }
}

/// A resolved (direct- or alias-chain) store write map: `(base_array,
/// entries, guard_aliases)`.  `entries` is the outermost-write-wins
/// `{index -> value}` map; `guard_aliases` is the list of `(var, store_term)`
/// equalities traversed to resolve an aliased variable (empty for a direct
/// chain).  Factored into a type alias to keep [`aliased_store_map`]'s
/// signature under `clippy::type_complexity`.
type StoreMap = (TermId, Vec<(TermId, TermId)>, Vec<(TermId, TermId)>);

/// Array terms and (dis)equalities gathered from a term-graph walk.
#[derive(Default)]
struct ArrayStructure {
    /// `(select_term, array_operand, index)` for every `select` encountered.
    selects: Vec<(TermId, TermId, TermId)>,
    /// Unordered array-sorted equality atoms `(a, b)` (`a != b` syntactically).
    eq_pairs: Vec<(TermId, TermId)>,
    /// `array_variable -> store_term`s for every asserted `var = store(...)`.
    /// A variable may appear in several such assertions, so this is a list per
    /// variable — see [`record_alias`] for why dropping the second alias is
    /// unsound.
    aliases: FxHashMap<TermId, Vec<TermId>>,
    /// `(base, store_result)` for every `store` term, used to seed
    /// base↔store extensionality (see [`collect_array_structure`]).
    store_base_pairs: Vec<(TermId, TermId)>,
    /// Distinct indices read on each array operand (for select congruence).
    read_indices: FxHashMap<TermId, Vec<TermId>>,
}

/// Gather array structure from `term`.  `visited` prevents re-descending
/// shared sub-terms of the interned DAG.
///
/// Iterative (explicit work stack), so nesting depth is bounded by memory
/// rather than by the native call stack — this walk has no error channel, so a
/// depth cap could only silently drop array structure and with it the
/// read-over-write / extensionality lemmas that make the answer sound.
/// Children are pushed in reverse, which reproduces the recursive pre-order
/// exactly and with it the order of `selects`, `eq_pairs` and `read_indices`.
fn collect_array_structure(
    term: TermId,
    manager: &TermManager,
    visited: &mut FxHashSet<TermId>,
    out: &mut ArrayStructure,
) {
    // The stack carries a polarity flag (`true` = positive).  It flips under
    // `Not`, so a top-level disequality `(not (= var store))` reaches its
    // inner `Eq` at *negative* polarity.  That matters for `record_alias`:
    // an alias is a *positive* `var = store` fact, and recording one from a
    // disequality's inner equality would (a) make `is_self_alias` skip the
    // fresh-witness extensionality that a disequality *needs*, and (b) feed
    // alias-aware read-over-write a `var = store` premise that is actually
    // false — both producing a spurious `sat` on an UNSAT goal (e.g.
    // `store_noop_disequality_is_unsat`: `select(a,i) = v` with
    // `a != store(a,i,v)` is UNSAT, but a phantom `a = store(a,i,v)` alias
    // suppresses the witness and the contradiction is never derived).
    // `eq_pairs` is recorded for either polarity: the extensionality /
    // congruence lemmas are valid regardless, and a disequality *requires*
    // the witness lemma.
    let mut stack: Vec<(TermId, bool)> = vec![(term, true)];
    while let Some((term, positive)) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        let Some(data) = manager.get(term) else {
            continue;
        };
        match &data.kind {
            TermKind::Not(inner) => {
                stack.push((*inner, !positive));
            }
            TermKind::Select(array, index) => {
                out.selects.push((term, *array, *index));
                let entry = out.read_indices.entry(*array).or_default();
                if !entry.contains(index) {
                    entry.push(*index);
                }
                stack.push((*index, positive));
                stack.push((*array, positive));
            }
            TermKind::Store(base, index, value) => {
                // Record the (base, store_result) pair for every store so
                // extensionality can be generated between an array and its
                // write when the write is *named by a variable* (see the
                // aliased-result gate in `build_extensionality_and_congruence`,
                // which is what keeps deep non-aliased chains like `storecomm`
                // from exploding).  Without base-extensionality a
                // contradiction that lives in whether `b = store(a, …)` forces
                // `a = b` (Stump-Barrett-Dill-Levitt `array_incompleteness1`,
                // or the deep-aliased writes in `cvc/read8`) is never explored,
                // because `(a, b)` is not an *asserted* equality atom.
                if *base != term {
                    out.store_base_pairs.push((*base, term));
                }
                stack.push((*value, positive));
                stack.push((*index, positive));
                stack.push((*base, positive));
            }
            TermKind::Eq(lhs, rhs) => {
                // Record an array-sorted equality atom (either polarity: the
                // extensionality / congruence lemmas are valid regardless).
                if lhs != rhs && is_array_sorted(*lhs, manager) && is_array_sorted(*rhs, manager) {
                    out.eq_pairs.push((*lhs, *rhs));
                }
                // Record a `var = store(...)` alias for alias-aware
                // read-over-write — POSITIVE equalities only.  A disequality
                // `(not (= var store))` is not an alias; its inner `Eq` reaches
                // here at `positive == false`.
                if positive {
                    record_alias(*lhs, *rhs, manager, &mut out.aliases);
                    record_alias(*rhs, *lhs, manager, &mut out.aliases);
                }
                stack.push((*rhs, positive));
                stack.push((*lhs, positive));
            }
            _ => {
                for child in get_children(&data.kind).into_iter().rev() {
                    stack.push((child, positive));
                }
            }
        }
    }
}

/// If `var_term` is a plain variable and `store_term` is a `store` expression,
/// record `var_term -> store_term`.
///
/// A variable may be equated to SEVERAL stores in one formula (e.g.
/// `(= b (store a x v))` and `(= b (store a y w))`), and the array decision
/// procedure must honour ALL of them: dropping the second alias silently
/// loses the read-over-write lemma through it, and the two stores then never
/// get reconciled — a spurious `sat` for an UNSAT goal (Stump-Barrett-Dill-
/// Levitt `array_incompleteness1` shape).  De-duplicate by `store_term` so a
/// repeated identical assertion does not double-instantiate.
fn record_alias(
    var_term: TermId,
    store_term: TermId,
    manager: &TermManager,
    aliases: &mut FxHashMap<TermId, Vec<TermId>>,
) {
    let (Some(var_data), Some(store_data)) = (manager.get(var_term), manager.get(store_term))
    else {
        return;
    };
    if matches!(var_data.kind, TermKind::Var(_)) && matches!(store_data.kind, TermKind::Store(..)) {
        let entry = aliases.entry(var_term).or_default();
        if !entry.contains(&store_term) {
            entry.push(store_term);
        }
    }
}

/// Build read-over-write instances for every collected `select`.
///
/// The axiom is emitted as its two case-split implications rather than a single
/// `ite`-valued equality, because the arithmetic / EUF theory solvers reduce a
/// guarded equality (`cond ⇒ x = y`) directly, whereas a term-level `ite`
/// operand of an equality would be handed to them opaque.
///
///   * RoW-1: `store_idx = index  ⇒  select_term = stored_val`
///   * RoW-2: `store_idx != index ⇒  select_term = select(base, index)`
fn build_read_over_write(
    manager: &mut TermManager,
    collected: &ArrayStructure,
    no_eager: &FxHashSet<TermId>,
    candidates: &mut Vec<TermId>,
) {
    for &(select_term, array, index) in &collected.selects {
        if let Some((base, store_idx, stored_val)) = as_store(array, manager) {
            // Direct read over a syntactic store chain.  Two paths:
            //
            //  * `no_eager` (the array is settled by a *complete* finite-
            //    disjunction clause): emit one level of read-over-write only.
            //  * otherwise: a FLAT encoding of the whole chain \u{2014 for every
            //    store index `ki`, the read-over-write-SAME implication
            //    `(index = ki) \u{21d2} select = vi`, PLUS a single "else" clause
            //    `select = select(base, index) \u{2228} \u{2228}_i (index = ki)`.
            //    This replaces the previous O(depth) nested RoW-DIFFERENT
            //    chain, which created an O(depth) cascade of intermediate
            //    `select(base_level, index)` atoms that ballooned the SAT
            //    search on deep `storecomm` reads (shape-2 goals).
            if no_eager.contains(&array) {
                let (row1, row2) =
                    row_implications(manager, select_term, store_idx, stored_val, base, index);
                candidates.push(row1);
                candidates.push(row2);
            } else if let Some((ultimate_base, entries)) = direct_store_map(array, manager) {
                let mut idx_eqs: Vec<TermId> = Vec::with_capacity(entries.len());
                for (ki, vi) in &entries {
                    let idx_eq = manager.mk_eq(*ki, index);
                    let same = manager.mk_eq(select_term, *vi);
                    candidates.push(manager.mk_implies(idx_eq, same));
                    idx_eqs.push(idx_eq);
                }
                let base_read = manager.mk_select(ultimate_base, index);
                let mut else_disj: Vec<TermId> = Vec::with_capacity(entries.len() + 1);
                else_disj.push(manager.mk_eq(select_term, base_read));
                else_disj.extend(idx_eqs);
                candidates.push(manager.mk_or(else_disj));
            }
        } else if let Some(store_terms) = collected.aliases.get(&array) {
            // Aliased read: an asserted `array = store(...)` makes the same
            // axiom apply.  TWO paths:
            //
            //  * a *single* unambiguous alias chain (`var = store(var' = store(...))`):
            //    resolve the WHOLE chain via [`aliased_store_map`] and emit a
            //    flat, guarded read-over-write encoding (one clause per store
            //    index + an else clause, all guarded by the conjunction of alias
            //    equalities).  This unfolds a depth-N alias chain in ONE
            //    refinement round instead of N — which collapses the timeout on
            //    deep `swap` UNSAT goals (e.g. `swap_t3_pp_sf_ai_00004`,
            //    30 s -> 0.01 s): the read resolves to a concrete value (or a
            //    base read) in the first round and the contradiction is found
            //    immediately.
            //  * an ambiguous (multi-)alias variable, or a chain that does not
            //    resolve: fall back to the original one-level-per-alias lemma so
            //    two stores equated through the same variable are still
            //    reconciled (see [`record_alias`]).
            if let Some((base, entries, guard_pairs)) =
                aliased_store_map(array, &collected.aliases, manager)
                && !entries.is_empty()
            {
                let guard_term: Option<TermId> = if guard_pairs.is_empty() {
                    None
                } else {
                    let conj: Vec<TermId> = guard_pairs
                        .iter()
                        .map(|(v, s)| manager.mk_eq(*v, *s))
                        .collect();
                    Some(if conj.len() == 1 {
                        conj[0]
                    } else {
                        manager.mk_and(conj)
                    })
                };
                let mut idx_eqs: Vec<TermId> = Vec::with_capacity(entries.len());
                for (ki, vi) in &entries {
                    let idx_eq = manager.mk_eq(*ki, index);
                    // RoW-SAME (guarded): (alias ∧ idx = ki) ⇒ select = vi.
                    let same = manager.mk_eq(select_term, *vi);
                    let imp = manager.mk_implies(idx_eq, same);
                    candidates.push(match guard_term {
                        Some(g) => manager.mk_implies(g, imp),
                        None => imp,
                    });
                    idx_eqs.push(idx_eq);
                }
                // Else (guarded): select = select(base, index) ∨ ∨_i (index = ki).
                let base_read = manager.mk_select(base, index);
                let mut else_disj: Vec<TermId> = Vec::with_capacity(entries.len() + 1);
                else_disj.push(manager.mk_eq(select_term, base_read));
                else_disj.extend(idx_eqs);
                let else_clause = manager.mk_or(else_disj);
                candidates.push(match guard_term {
                    Some(g) => manager.mk_implies(g, else_clause),
                    None => else_clause,
                });
            } else {
                for &store_term in store_terms {
                    if let Some((base, store_idx, stored_val)) = as_store(store_term, manager) {
                        let alias_eq = manager.mk_eq(array, store_term);
                        let (row1, row2) = row_implications(
                            manager,
                            select_term,
                            store_idx,
                            stored_val,
                            base,
                            index,
                        );
                        let g1 = manager.mk_implies(alias_eq, row1);
                        let g2 = manager.mk_implies(alias_eq, row2);
                        candidates.push(g1);
                        candidates.push(g2);
                    }
                }
            }
        } else if let Some((c, a, b)) = as_array_ite(array, manager) {
            // select-over-ite:  select(ite(c, a, b), i) = ite(c, select(a, i),
            // select(b, i)).  Without this, a read of an array-valued `ite`
            // (ubiquitous in translated CVC processor-verification benchmarks,
            // e.g. `(= (ite cond (store …) b) b)`) is an opaque leaf and the
            // extensionality / read-over-write lemmas never reach the `store`.
            // Emitted as two implications (an `ite`-valued equality is opaque
            // to the arithmetic/EUF solvers — see the RoW note above); the new
            // `select(a, i)` / `select(b, i)` terms seed further instantiation
            // in the next refinement round.
            let read_a = manager.mk_select(a, index);
            let read_b = manager.mk_select(b, index);
            let hit = manager.mk_eq(select_term, read_a);
            let miss = manager.mk_eq(select_term, read_b);
            let not_c = manager.mk_not(c);
            candidates.push(manager.mk_implies(c, hit));
            candidates.push(manager.mk_implies(not_c, miss));
        }
    }
}

/// Array-congruence at store-chain write indices for every collected
/// array-sorted equality.
///
/// For an equality `(= A B)` where at least one side is a (nested) store chain,
/// this asserts the array-congruence theorem `(= A B) ⇒ (= (select A i)
/// (select B i))` at each write index `i` of either chain.  The clause is
/// *entailed* by the theory of arrays, so adding it changes no verdict -- it
/// can only help the search derive a contradiction.  Its value is that it
/// materialises `select(var, store_idx)` atoms the lazy `build_read_over_write`
/// pass never creates when an array variable is unread at a store-chain write
/// index: that is exactly the ingredient a *conditional* inline equality
/// `(= (store…) var)` (e.g. one sitting inside an `ite` condition, as in
/// `cvc/read8`) needs to propagate its read-over-write consequences once the
/// SAT core commits to the branch that makes the equality hold.
///
/// Free-variable / non-store equalities contribute no write index, so they are
/// left to the witness extensionality (`build_extensionality_and_congruence`).
/// An unconditional `var = store(...)` alias is skipped only when the variable
/// has one unambiguous store definition: alias-aware RoW already unfolds every
/// observed read through that chain, so manufacturing otherwise-unobserved
/// reads is redundant.  A variable equated to *multiple* stores is different:
/// the stores must be reconciled at one another's write indices even when the
/// input contains no read.  Those congruence instances are the propagation
/// bridge required by the Stump-Barrett-Dill-Levitt array-incompleteness case.
fn build_equality_read_congruence(
    manager: &mut TermManager,
    collected: &ArrayStructure,
    candidates: &mut Vec<TermId>,
) {
    for &(a, b) in &collected.eq_pairs {
        if is_unambiguous_alias_pair(a, b, &collected.aliases)
            || is_unambiguous_alias_pair(b, a, &collected.aliases)
        {
            continue;
        }
        // Gather the write indices exposed by either side's store chain.
        let mut idx_terms: Vec<TermId> = Vec::new();
        if let Some((_, entries)) = direct_store_map(a, manager) {
            for (idx, _val) in &entries {
                idx_terms.push(*idx);
            }
        }
        if let Some((_, entries)) = direct_store_map(b, manager) {
            for (idx, _val) in &entries {
                idx_terms.push(*idx);
            }
        }
        if idx_terms.is_empty() {
            continue;
        }
        let eq_ab = manager.mk_eq(a, b);
        for (pos, &idx) in idx_terms.iter().enumerate() {
            // Dedup (small vec -> linear scan): a shared index on both sides
            // needs only one congruence clause.
            if idx_terms[..pos].contains(&idx) {
                continue;
            }
            let sa = manager.mk_select(a, idx);
            let sb = manager.mk_select(b, idx);
            let reads_eq = manager.mk_eq(sa, sb);
            candidates.push(manager.mk_implies(eq_ab, reads_eq));
        }
    }
}

/// Build the two read-over-write case-split implications for a
/// `select(store(base, store_idx, stored_val), index)` read.
fn row_implications(
    manager: &mut TermManager,
    select_term: TermId,
    store_idx: TermId,
    stored_val: TermId,
    base: TermId,
    index: TermId,
) -> (TermId, TermId) {
    let idx_eq = manager.mk_eq(store_idx, index);
    // RoW-1: (store_idx = index) ⇒ (select_term = stored_val)
    let hit = manager.mk_eq(select_term, stored_val);
    let row1 = manager.mk_implies(idx_eq, hit);
    // RoW-2: (store_idx != index) ⇒ (select_term = select(base, index))
    let idx_neq = manager.mk_not(idx_eq);
    let base_read = manager.mk_select(base, index);
    let miss = manager.mk_eq(select_term, base_read);
    let row2 = manager.mk_implies(idx_neq, miss);
    (row1, row2)
}

/// Build extensionality and select-congruence instances for every collected
/// array-sorted equality atom.  Returns the candidate lemmas and the set of
/// arrays that a *complete* finite-disjunction clause settles — reads on those
/// arrays need not be eagerly unfolded (the clause decides them), which is the
/// lever that makes a depth-60 `storecomm` chain one flat clause instead of a
/// 60-deep unfolding.
fn build_extensionality_and_congruence(
    manager: &mut TermManager,
    collected: &ArrayStructure,
    candidates: &mut Vec<TermId>,
) -> FxHashSet<TermId> {
    let mut finite_decided: FxHashSet<TermId> = FxHashSet::default();
    // Extensionality candidate pairs: the asserted array equalities, PLUS
    // every (base, store_result) pair for a store that is *named by a
    // variable* (asserted `var = store(...)`), so an array and its write are
    // compared even when their (in)equality is only implied.
    //
    // Gated to aliased stores: base-extensionality is the ingredient that
    // decides the Stump-Barrett-Dill-Levitt `array_incompleteness1` /
    // `storeinv` shape (a variable equated to a write over a base array, where
    // the contradiction is whether the write forces `base = var`).  Applying
    // it to EVERY store — including the innermost write of a deep `storecomm`
    // chain — spawns extensionality pairs whose witness reads unfold the whole
    // chain, turning a sub-millisecond SAT into a multi-second solve or a
    // timeout.  Deep chains never need it: their (in)equality is already an
    // asserted atom whose own extensionality lemma decides them.
    // Set of store terms that some array variable is asserted equal to
    // (`var = store(...)`).  A store in this set is "named" by a variable, so
    // reconciling it against its own base array may be required to decide the
    // goal; a store that is NOT named (e.g. an internal link of a deep
    // `storecomm` chain) is already decided by the extensionality lemma on its
    // asserted (dis)equality atom and needs no base-extensionality.
    let aliased_stores: FxHashSet<TermId> = collected.aliases.values().flatten().copied().collect();
    let mut pairs: Vec<(TermId, TermId)> = collected.eq_pairs.clone();
    for &(base, result) in &collected.store_base_pairs {
        if aliased_stores.contains(&result)
            && !pairs.contains(&(base, result))
            && !pairs.contains(&(result, base))
        {
            pairs.push((base, result));
        }
    }
    for &(a, b) in &pairs {
        let mut pair_complete = false;
        // Fast path: finite-disjunction extensionality for two store chains
        // over a common (non-store) base.  This adds a flat clause (value-term
        // comparisons, no `select` / unfolding) that settles `storecomm`-style
        // pairs in one round.  It is generated IN ADDITION to (not instead of)
        // the fresh-witness extensionality below: that witness's `select(a,k)`
        // / `select(b,k)` terms can link this pair to other constraints a pure
        // value-disjunction misses (e.g. `cvc/read8`), so skipping it would
        // lose completeness.  The clause is cheap, and on the deep-chain goals
        // it dominates the search so the witness path adds little.
        if let Some((lemma, is_complete)) = finite_disjunction_extensionality(manager, a, b) {
            candidates.push(lemma);
            pair_complete = is_complete;
            if is_complete {
                // The clause decides `a = b` with no array-read unfolding.
                // Record both operands so `build_read_over_write` can skip the
                // eager full-chain unfold for reads on them (lazy one-level RoW
                // is sound and, since the search finishes once the clause fires,
                // never actually needs the deeper levels).
                finite_decided.insert(a);
                finite_decided.insert(b);
            }
        }
        // Extensionality: a = b ∨ select(a,k) != select(b,k), with a fresh but
        // deterministic witness index per unordered pair.  SKIPPED for a
        // *self-alias* pair — one whose `a = b` IS an asserted alias equality
        // (`(= var store...)` collected in [`ArrayStructure::aliases`]).  There
        // `a = b` is a level-0 fact, so the witness clause `a = b ∨ ...` is
        // trivially satisfied and adds nothing; its only effect was to create
        // the fresh-witness reads `select(a,k)` / `select(b,k)`, whose
        // read-over-write unfolding drove the ~10-round cascade on `swap` /
        // `storeinv` goals.  SOUND: the skipped clause is a tautology under the
        // level-0 alias, and the witness could never fire (`a ≠ b` is
        // impossible while the alias holds); the lemmas are retracted on `pop`
        // with the alias.
        let is_self_alias =
            is_alias_pair(a, b, &collected.aliases) || is_alias_pair(b, a, &collected.aliases);
        // A complete finite-disjunction clause also makes the witness redundant
        // (see [`finite_disjunction_extensionality`]: the flat value-disjunction
        // already decides `a = b`, and a fresh witness outside both store sets
        // can never witness `a \u{2260} b` over a shared base).
        if !(is_self_alias || pair_complete)
            && let Some(domain) = array_domain(a, manager)
        {
            let witness = extensionality_witness(manager, a, b, domain);
            let read_a = manager.mk_select(a, witness);
            let read_b = manager.mk_select(b, witness);
            let reads_eq = manager.mk_eq(read_a, read_b);
            let reads_diff = manager.mk_not(reads_eq);
            let eq_ab = manager.mk_eq(a, b);
            let ext = manager.mk_or([eq_ab, reads_diff]);
            candidates.push(ext);
        }

        // Both cases above already provide a complete path for every relevant
        // read without materialising the same read across this pair:
        //
        // * a level-0 alias is handled directly by alias-aware RoW, guarded by
        //   that asserted equality;
        // * a complete finite store-map clause characterises `a = b` at every
        //   index where the arrays can differ, while ordinary RoW handles any
        //   observed read on either operand.
        //
        // Generating select congruence here recursively copies every observed
        // index across an alias chain.  Those copied selects then seed more
        // RoW and congruence instances, creating the full array×index closure
        // even though none of the extra reads occurs in the input.  Conditional
        // inline equalities still take the congruence path below (and the
        // write-index path in `build_equality_read_congruence`).
        if is_self_alias || pair_complete {
            continue;
        }

        // Select congruence: a = b ⇒ select(a,j) = select(b,j) for every index
        // read on either side.
        let mut indices: Vec<TermId> = Vec::new();
        if let Some(idxs) = collected.read_indices.get(&a) {
            for &idx in idxs {
                if !indices.contains(&idx) {
                    indices.push(idx);
                }
            }
        }
        if let Some(idxs) = collected.read_indices.get(&b) {
            for &idx in idxs {
                if !indices.contains(&idx) {
                    indices.push(idx);
                }
            }
        }
        for idx in indices {
            let read_a = manager.mk_select(a, idx);
            let read_b = manager.mk_select(b, idx);
            let reads_eq = manager.mk_eq(read_a, read_b);
            let eq_ab = manager.mk_eq(a, b);
            let cong = manager.mk_implies(eq_ab, reads_eq);
            candidates.push(cong);
        }
    }
    finite_decided
}

/// Materialise (interning is idempotent) a deterministic extensionality witness
/// index variable for the unordered array pair `{a, b}`.  Using a name derived
/// from the two term ids keeps the witness stable across refinement rounds, so
/// the extensionality lemma for a given pair is asserted exactly once instead of
/// spawning a fresh variable each round.
fn extensionality_witness(
    manager: &mut TermManager,
    a: TermId,
    b: TermId,
    domain: SortId,
) -> TermId {
    let (lo, hi) = if a.raw() <= b.raw() {
        (a.raw(), b.raw())
    } else {
        (b.raw(), a.raw())
    };
    // The `!oxiz!ext!` prefix cannot collide with an SMT-LIB source symbol.
    let name = format!("!oxiz!ext!{lo}!{hi}");
    manager.mk_var(&name, domain)
}

/// If `term` is a `store`, return `(base, index, value)`.
fn as_store(term: TermId, manager: &TermManager) -> Option<(TermId, TermId, TermId)> {
    match manager.get(term)?.kind {
        TermKind::Store(base, index, value) => Some((base, index, value)),
        _ => None,
    }
}

/// Whether `(a, b)` is a recorded `var = store` alias: `a` is a variable and
/// `b` is one of its asserted alias stores.  Used to detect *self-alias*
/// extensionality pairs whose `a = b` is a level-0 fact (so the fresh-witness
/// extensionality is a no-op tautology and can be skipped).
fn is_alias_pair(a: TermId, b: TermId, aliases: &FxHashMap<TermId, Vec<TermId>>) -> bool {
    aliases.get(&a).is_some_and(|stores| stores.contains(&b))
}

/// Whether `(a, b)` is the sole asserted store definition of `a`.
///
/// Only this unambiguous form may omit synthetic write-index congruence: with
/// two definitions `a = store(..i..)` and `a = store(..j..)`, each definition
/// has to be observed at the other definition's index to reconcile them.
fn is_unambiguous_alias_pair(
    a: TermId,
    b: TermId,
    aliases: &FxHashMap<TermId, Vec<TermId>>,
) -> bool {
    aliases
        .get(&a)
        .is_some_and(|stores| stores.len() == 1 && stores[0] == b)
}

/// If `term` is an array-sorted `ite`, return `(cond, then, else)`.
fn as_array_ite(term: TermId, manager: &TermManager) -> Option<(TermId, TermId, TermId)> {
    match manager.get(term)?.kind {
        TermKind::Ite(c, t, e) => Some((c, t, e)),
        _ => None,
    }
}

/// Normalise a direct (non-aliased) store chain `store(store(... store(base)
/// ...))` into `(base, entries)` with `entries` the outermost-write-wins
/// `{idx -> val}` map.  Returns `None` if `term` is not a `Store`-rooted
/// chain (a plain variable / select / UF normalises to itself with an empty
/// map, which is not useful here — callers gate on a non-empty map).
fn direct_store_map(
    term: TermId,
    manager: &TermManager,
) -> Option<(TermId, Vec<(TermId, TermId)>)> {
    let mut entries: Vec<(TermId, TermId)> = Vec::new();
    let mut cur = term;
    loop {
        match manager.get(cur)?.kind {
            TermKind::Store(base, idx, val) => {
                if !entries.iter().any(|(i, _)| *i == idx) {
                    entries.push((idx, val));
                }
                cur = base;
            }
            _ => return Some((cur, entries)),
        }
    }
}

/// Alias-aware store-map resolution: like [`direct_store_map`] but also follows
/// `var = store(...)` aliases so an array *variable* asserted equal to a store
/// chain resolves to that chain's write map.  Returns
/// `(base, entries, guard_pairs)` where `guard_pairs` is the list of
/// `(var, store_term)` alias equalities traversed (empty for a direct chain).
/// A variable with zero or more than one alias stops the walk (ambiguous).
/// Cycle-safe via a `visited` set.
fn aliased_store_map(
    term: TermId,
    aliases: &FxHashMap<TermId, Vec<TermId>>,
    manager: &TermManager,
) -> Option<StoreMap> {
    let mut entries: Vec<(TermId, TermId)> = Vec::new();
    let mut guard: Vec<(TermId, TermId)> = Vec::new();
    let mut cur = term;
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    loop {
        if !visited.insert(cur) {
            return None;
        }
        let Some(data) = manager.get(cur) else {
            return if entries.is_empty() {
                None
            } else {
                Some((cur, entries, guard))
            };
        };
        match data.kind {
            TermKind::Store(base, idx, val) => {
                if !entries.iter().any(|(i, _)| *i == idx) {
                    entries.push((idx, val));
                }
                cur = base;
            }
            TermKind::Var(_) => {
                if let Some(store_terms) = aliases.get(&cur)
                    && store_terms.len() == 1
                    && let Some((base2, idx2, val2)) = as_store(store_terms[0], manager)
                {
                    guard.push((cur, store_terms[0]));
                    if !entries.iter().any(|(i, _)| *i == idx2) {
                        entries.push((idx2, val2));
                    }
                    cur = base2;
                    continue;
                }
                return if entries.is_empty() {
                    None
                } else {
                    Some((cur, entries, guard))
                };
            }
            _ => {
                return if entries.is_empty() {
                    None
                } else {
                    Some((cur, entries, guard))
                };
            }
        }
    }
}

/// Whether `term` is a value the SAT + arithmetic + EUF core can decide
/// directly, without an array `select` unfolding — anything that is not a
/// `Select`, array-sorted `Ite`, or `Store`.  Used to tell when a
/// finite-disjunction clause is *complete* (decides the pair with no unfolding).
fn is_scalar_value(term: TermId, manager: &TermManager) -> bool {
    !matches!(
        manager.get(term).map(|d| &d.kind),
        Some(TermKind::Select(..) | TermKind::Ite(..) | TermKind::Store(..))
    )
}

/// Finite-disjunction extensionality for two store chains over a *common base*
/// that write the *same index set*: returns the valid lemma
/// `a = b ∨ ∨_{k∈K} val_a(k) ≠ val_b(k)`, where each `val_·(k)` is the chain's
/// value TERM at `k`.  Because the operands share a base and an index set, the
/// two arrays can differ only at `K`, so this single clause fully decides the
/// pair — and it compares value terms directly (no `select`, no
/// read-over-write unfolding), so a depth-60 `storecomm` chain becomes one flat
/// clause instead of a 60-deep unfolding that costs seconds per refinement
/// round.  Returns `None` when the precondition (common base + same index set +
/// at least one store) does not hold, so the caller falls back to the
/// fresh-witness extensionality.
fn finite_disjunction_extensionality(
    manager: &mut TermManager,
    a: TermId,
    b: TermId,
) -> Option<(TermId, bool)> {
    // Returns `(lemma, is_complete)`.  `is_complete` is true only when the
    // clause decides `a = b` with no array-select unfolding — a common
    // free-variable base whose every compared value is scalar (variable /
    // constant / arithmetic / UF).  `storecomm` qualifies (base `a1`, values
    // are free `e_i`); `swap`/`read8` do not (values are `select`s), so their
    // reads must still be unfolded and the caller keeps the eager path.
    let (ba, ma) = direct_store_map(a, manager)?;
    let (bb, mb) = direct_store_map(b, manager)?;
    if ma.is_empty() || ba != bb {
        return None;
    }
    // The base must not itself be a `Store`: the one-sided disjuncts below read
    // `select(base, idx)`, and if `base` were a store chain those reads would
    // unfold (the very cost this lemma exists to avoid).  For the `storecomm`
    // family the base is a free array variable, so the reads stay opaque.
    if as_store(ba, manager).is_some() {
        return None;
    }
    let base = ba;
    // `is_complete`: the clause decides `a = b` with no array-read unfolding.
    // Requires (1) a free-variable base, (2) every compared value scalar, and
    // (3) the SAME index set on both sides — a differing index set forces a
    // one-sided `select(base, idx)` disjunct whose opaque read the SAT core
    // cannot settle instantly, so the eager chain unfold is still needed there.
    let is_complete = matches!(manager.get(base).map(|d| &d.kind), Some(TermKind::Var(_)))
        && ma
            .iter()
            .chain(mb.iter())
            .all(|&(_, v)| is_scalar_value(v, manager));
    // Over a common base the two arrays can differ only at K = idx_a ∪ idx_b.
    // At a shared index they compare value-term to value-term; at a one-sided
    // index the writer's value compares to `select(base, idx)` (the unwritten
    // side).  All comparisons are on value terms / opaque base reads — no
    // read-over-write unfolding — so this is a flat clause regardless of chain
    // depth.
    let mut disjuncts: Vec<TermId> = vec![manager.mk_eq(a, b)];
    for (idx, va) in &ma {
        match mb.iter().find(|(i, _)| *i == *idx) {
            Some((_, vb)) if vb != va => {
                let eq = manager.mk_eq(*va, *vb);
                disjuncts.push(manager.mk_not(eq));
            }
            Some(_) => {} // shared index, equal value terms — cannot witness a diff
            None => {
                // a-only:  a writes va, b reads select(base, idx).
                let br = manager.mk_select(base, *idx);
                let eq = manager.mk_eq(*va, br);
                disjuncts.push(manager.mk_not(eq));
            }
        }
    }
    for (idx, vb) in &mb {
        if !ma.iter().any(|(i, _)| *i == *idx) {
            // b-only:  b writes vb, a reads select(base, idx).
            let br = manager.mk_select(base, *idx);
            let eq = manager.mk_eq(br, *vb);
            disjuncts.push(manager.mk_not(eq));
        }
    }
    // A single-disjunct lemma is just `a = b`, which is valid precisely when
    // the two chains write identical values to identical indices over an
    // identical base — sound to assert, and it forces a conflict with any
    // `not(= a b)`.
    Some(if disjuncts.len() == 1 {
        (disjuncts[0], is_complete)
    } else {
        (manager.mk_or(disjuncts), is_complete)
    })
}

/// Whether `term` has an array sort.
fn is_array_sorted(term: TermId, manager: &TermManager) -> bool {
    manager
        .get(term)
        .and_then(|d| manager.sorts.get(d.sort))
        .is_some_and(|s| matches!(s.kind, SortKind::Array { .. }))
}

/// The domain (index) sort of `term`'s array sort, if `term` is array-sorted.
fn array_domain(term: TermId, manager: &TermManager) -> Option<SortId> {
    let sort = manager.get(term)?.sort;
    match manager.sorts.get(sort)?.kind {
        SortKind::Array { domain, .. } => Some(domain),
        _ => None,
    }
}

#[cfg(test)]
mod s8_iterative_tests {
    use super::*;
    use oxiz_core::ast::TermManager;

    /// Nesting depth that would overflow the native stack under the previous
    /// recursive walk; the assertion is simply that the call **returns**.
    ///
    /// This depth and [`SMALL_STACK`] were scaled down together by a factor
    /// of 8 (from 60 000 on 1 MiB).  What the test pins is the ~17 bytes of
    /// stack available per level — far under any native frame — not the
    /// absolute depth, and the smaller pair costs a fraction of the memory
    /// the interner has to keep live.  Never raise one without the other.
    const DEEP: usize = 7_500;

    /// Worker stack for the deep-nesting test; see [`DEEP`].
    const SMALL_STACK: usize = 1 << 17;

    /// Build `store(store(...store(a, i, v)..., i, v), i, v)`, `depth` levels.
    fn deep_store_chain(tm: &mut TermManager, depth: usize) -> (TermId, TermId) {
        let int_sort = tm.sorts.int_sort;
        let array_sort = tm.sorts.array(int_sort, int_sort);
        let base = tm.mk_var("a", array_sort);
        let idx = tm.mk_int(num_bigint::BigInt::from(1));
        let val = tm.mk_int(num_bigint::BigInt::from(7));
        let mut current = base;
        for _ in 0..depth {
            current = tm.mk_store(current, idx, val);
        }
        (current, idx)
    }

    #[test]
    fn s8_collect_array_structure_deep_store_chain_returns() {
        // A 128 KiB stack: the recursive version could not survive `DEEP`
        // frames, so returning at all is the proof of the conversion.
        let handle = std::thread::Builder::new()
            .stack_size(SMALL_STACK)
            .spawn(|| {
                let mut tm = TermManager::new();
                let (deep, idx) = deep_store_chain(&mut tm, DEEP);
                let select = tm.mk_select(deep, idx);
                let mut visited = FxHashSet::default();
                let mut out = ArrayStructure::default();
                collect_array_structure(select, &tm, &mut visited, &mut out);
                out.selects.len()
            })
            .expect("spawn deep-nesting worker");
        assert_eq!(handle.join().ok(), Some(1));
    }

    /// A doubling DAG: without the `visited` set this would expand
    /// exponentially instead of completing immediately.
    #[test]
    fn s8_collect_array_structure_shared_dag_completes() {
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let mut current = tm.mk_var("x", int_sort);
        for _ in 0..55 {
            current = tm.mk_add(vec![current, current]);
        }
        let mut visited = FxHashSet::default();
        let mut out = ArrayStructure::default();
        collect_array_structure(current, &tm, &mut visited, &mut out);
        assert!(out.selects.is_empty());
    }

    /// Semantic pin: the walk still records selects, read indices, array
    /// equalities and `var = store(..)` aliases, in the recursive order.
    #[test]
    fn s8_collect_array_structure_records_same_structure() {
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let array_sort = tm.sorts.array(int_sort, int_sort);
        let a = tm.mk_var("a", array_sort);
        let b = tm.mk_var("b", array_sort);
        let i = tm.mk_int(num_bigint::BigInt::from(1));
        let j = tm.mk_int(num_bigint::BigInt::from(2));
        let v = tm.mk_int(num_bigint::BigInt::from(9));
        let store_a = tm.mk_store(a, i, v);
        let alias = tm.mk_eq(b, store_a);
        let sel_i = tm.mk_select(a, i);
        let sel_j = tm.mk_select(a, j);
        let sel_eq = tm.mk_eq(sel_i, sel_j);
        let both = tm.mk_and(vec![alias, sel_eq]);

        let mut visited = FxHashSet::default();
        let mut out = ArrayStructure::default();
        collect_array_structure(both, &tm, &mut visited, &mut out);

        // `b = store(a, i, v)` is recorded as an alias and as an array-sorted
        // equality pair; the two selects are recorded left to right.
        assert_eq!(out.aliases.get(&b), Some(&vec![store_a]));
        assert_eq!(out.eq_pairs, vec![(b, store_a)]);
        assert_eq!(
            out.selects,
            vec![(sel_i, a, i), (sel_j, a, j)],
            "select order must match the recursive pre-order"
        );
        assert_eq!(out.read_indices.get(&a), Some(&vec![i, j]));
    }
}
