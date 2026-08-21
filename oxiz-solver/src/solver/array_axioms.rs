//! Lazy array-theory axiom instantiation for the CDCL(T) loop.
//!
//! The syntactic pre-checks in [`super::check_array`] recognise a fixed set of
//! definite array conflicts, but they cannot decide the general case – e.g. a
//! read-over-write at a *provably different* index (`i != j` forcing
//! `select(store(a,i,v),j) = select(a,j)`), or extensionality on a disequality
//! between two array variables.  Left to the raw SAT core those atoms are free
//! Booleans, which risks a spurious `Sat`.
//!
//! This module supplies the missing decision power as a *lazy* refinement loop
//! driven from [`super::Solver::check`]: whenever the CDCL(T) core proposes a
//! candidate model, [`Solver::instantiate_array_axioms`] inspects the array
//! terms in that model and asserts every axiom instance the candidate needs,
//! then asks the core to re-solve.  The families and – crucially – *when each
//! fires* (mirroring Z3's `theory_array` / `theory_array_full`):
//!
//!   * **Read-over-write** – for every observed `select(store(b,i,v), j)`
//!     (directly or through an asserted `B = store(b,i,v)` alias):
//!     `select(store(b,i,v),j) = ite(i = j, v, select(b,j))`, flat-encoded.
//!     Observed reads are instantiated eagerly (bounded by the input);
//!     synthetic reads of the upward closure below are model-filtered.
//!   * **Upward read-over-write** (Z3 `set_prop_upward` + `instantiate_axiom2b`)
//!     – for a *connected* store chain (one an input array equality compares),
//!     every index read anywhere below a link is lifted one level at a time
//!     through the whole chain, as unguarded facts where the alias is a
//!     level-0 unit.  This is what refutes the `storeinv` family: the asserted
//!     chain equality must agree with the base reads pointwise.
//!   * **Extensionality** – a witness index `k` (fresh but *deterministic* per
//!     unordered pair) with `a = b ∨ select(a,k) != select(b,k)`, minted ONLY
//!     for a *separated* pair (Z3 `new_diseq_eh`): an input-asserted array
//!     disequality, a pair the finished search proved disequal in EUF, or a
//!     pair whose equality atom the candidate model assigned false.  A pair
//!     nothing separates is free to be equal in the model; minting its
//!     witness anyway used to unfold whole store chains per chain link per
//!     round (the deep `swap` / `storecomm` timeouts).
//!   * **Interface equality atoms** (Z3 `mk_interface_eqs`) – for arrays that
//!     appear in a cross-theory position (arguments of uninterpreted
//!     applications like `g(a)` / `sk(a1,a2)`, or `select` indices), the pair's
//!     equality atom is encoded so CDCL must decide the arrangement; a false
//!     decision lands the pair in the separation set above next round.  This
//!     is how a disequality derived through congruence (`g(a) != g(b)` forcing
//!     `a != b` with no equality atom in the input) reaches its witness – the
//!     Stump-Barrett-Dill-Levitt `array_incompleteness1` case.
//!   * **Select congruence / write-index congruence** – `a = b ⇒
//!     select(a,j) = select(b,j)` for INPUT equality atoms only: lemmas this
//!     module asserts re-contain the same `Eq` atoms, and re-firing off those
//!     copies multiplies reads without bound.  EUF congruence closure already
//!     carries the consequence for every asserted equality whose select terms
//!     exist; these clauses exist to materialise the reads that do not.
//!
//! Every asserted instance is a theorem of the (extensional) array theory, so
//! adding it never changes satisfiability – it only removes models that violate
//! array semantics.  Instances are deduplicated by their interned lemma term
//! id and each family's candidate set is finite, so the refinement loop in
//! `check` terminates: each round either asserts/encodes something new or
//! reports that the candidate model is a genuine array model (recorded as
//! [`Solver::array_axioms_saturated`] for the Context-level honesty gate).
//!
//! Reference: Z3's `src/smt/theory_array.cpp`, `theory_array_full.cpp`, and
//! `theory_array_base.cpp` (`mk_interface_eqs`, `new_diseq_eh`,
//! `set_prop_upward`).

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
    /// asserted to the SAT core – in which case the caller must re-solve – and
    /// `false` when the candidate model already satisfies every applicable
    /// axiom instance (so the reported `Sat` is trustworthy for the array
    /// atoms).
    pub(super) fn instantiate_array_axioms(&mut self, manager: &mut TermManager) -> bool {
        if self.array_axiom_instances.len() >= MAX_ARRAY_AXIOM_INSTANCES {
            // Budget exhausted: NOT a fixpoint.  The caller must not mark the
            // refinement saturated (`array_axioms_saturated` stays `false` so
            // the Context honesty gate keeps guarding a `Sat` verdict).
            return false;
        }

        // ======== Phase 1: collect array structure ========
        // Walk both the user assertions and every axiom instance asserted so
        // far, so selects introduced by earlier read-over-write / extensionality
        // lemmas seed further instantiation (saturation).
        let mut collected = ArrayStructure::default();
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        for &root in &self.assertions {
            collect_array_structure(root, true, manager, &mut visited, &mut collected);
        }
        for &root in self.array_axiom_instances.iter() {
            collect_array_structure(root, false, manager, &mut visited, &mut collected);
        }

        if collected.selects.is_empty() && collected.eq_pairs.is_empty() {
            return false;
        }

        // ======== Phase 1.5: array-pair separation (the Z3 `new_diseq_eh`
        // analogue) ========
        // A pair of arrays needs an extensionality witness exactly when they
        // are *separated* – asserted disequal by the input, proven disequal in
        // the live EUF state of the search that just finished, or assigned a
        // `false` equality atom by the candidate model.  This MUST be computed
        // before any `encode` / `add_clause` below: asserting clauses
        // backtracks the SAT core to root, which invalidates the saved model
        // the query reads.
        //
        // The separation universe is the `Eq` atoms seen anywhere (input or
        // lemma – a lemma-borne atom the model falsified still names a pair
        // the search cares about) PLUS the interface pairs.  Base `(array,
        // store-of-that-array)` pairs are deliberately NOT queried: the
        // select-congruence clauses over those pairs re-contain their `Eq`
        // atom, SAT satisfies the implication by deciding the atom false, and
        // reading that free decision back as a *demanded* separation mints
        // witnesses for every chain link of every store chain – the cascade
        // this rework exists to kill.
        let mut interface_pairs: Vec<(TermId, TermId)> = Vec::new();
        {
            let mut interface_arrays = collected.interface_arrays.clone();
            interface_arrays.sort_by_key(|t| t.raw());
            interface_arrays.dedup();
            let mut i = 0;
            while i < interface_arrays.len() {
                let mut j = i + 1;
                while j < interface_arrays.len() {
                    let (a, b) = (interface_arrays[i], interface_arrays[j]);
                    j += 1;
                    if let (Some(da), Some(db)) = (manager.get(a), manager.get(b))
                        && da.sort == db.sort
                    {
                        interface_pairs.push((a, b));
                    }
                }
                i += 1;
            }
        }
        let mut separated_pairs: FxHashSet<(TermId, TermId)> =
            collected.asserted_diseq_pairs.clone();
        for &(a, b) in collected.eq_pairs.iter().chain(interface_pairs.iter()) {
            let key = unordered_pair(a, b);
            if separated_pairs.contains(&key) {
                continue;
            }
            if self.array_pair_separation(a, b, manager) != PairSeparation::None {
                separated_pairs.insert(key);
            }
        }

        // ======== Phase 2: build candidate ground axiom instances ========
        // Build extensionality first so its *complete* finite-disjunction
        // clauses can tell `build_read_over_write` which arrays need no eager
        // chain unfolding (the lever for deep `storecomm` chains).
        let mut candidates: Vec<TermId> = Vec::new();
        let no_eager = build_extensionality_and_congruence(
            manager,
            &collected,
            &separated_pairs,
            &interface_pairs,
            &mut candidates,
        );
        // The upward closure runs FIRST: it defines synthetic reads one
        // chain level at a time, and the reads it defines must not also pay a
        // full flat chain-unfold in `build_read_over_write` (that duplication
        // is what made deep `storeinv` sat goals re-solve a formula several
        // times the size of the input).  Its candidates are a SEPARATE list:
        // they are model-filtered in Phase 3 (see the note there), unlike the
        // observed-read families.
        let mut upward_candidates: Vec<TermId> = Vec::new();
        let upward_defined =
            build_connected_upward_read_over_write(manager, &collected, &mut upward_candidates);
        build_read_over_write(
            manager,
            &collected,
            &no_eager,
            &upward_defined,
            &mut candidates,
        );
        // Array-congruence at store-chain write indices: for an inline array
        // equality `(= A B)` whose store chain exposes write indices, assert
        // the theorem `(= A B) => (= (select A i) (select B i))` per write index.
        // This is entailed by the array theory (it can change no verdict), but
        // it materialises `select(var, store_idx)` atoms the lazy
        // read-over-write pass never creates when the array variable is
        // unread at the store index -- the ingredient a conditional
        // `(= (store...) var)` inside an `ite` needs to propagate its
        // read-over-write consequences (the `cvc/read8` shape).  Gated to
        // INPUT atoms only: lemmas this module asserted (an extensionality
        // witness clause, a congruence implication) carry the same `Eq`
        // syntactically, and re-firing write-index congruence off those
        // copies multiplies reads without bound -- the closure growth that
        // stalled the refinement loop on deep `swap` / `storecomm` chains.
        build_equality_read_congruence(manager, &collected, &mut candidates);

        // ======== Phase 2.4: constant-array reads ========
        // `select((as const S) v, i) = v` for every observed read of a
        // constant-function array.  The axiom holds for every index, so a
        // unit per read is exact (no guard, no witness); it is what makes a
        // stored value visible when the model reads the array (Z3 rewrites
        // this select away entirely at internalization — see
        // `th_rewriter::mk_select`'s `is_const` folding — the unit here is
        // the lazy-lemma equivalent).  Reads of a variable EQUAL to a const
        // array chain through the eq-pair select-congruence lemmas, and
        // store-over-const bases through the read-over-write family.
        for &(sel_term, array, _index) in &collected.selects {
            let Some(&value) = collected.const_arrays.get(&array) else {
                continue;
            };
            let lemma = manager.mk_eq(sel_term, value);
            candidates.push(lemma);
        }

        // ======== Phase 2.5: interface-equality atoms (Z3
        // `mk_interface_eqs`) ========
        // For every pair of *interface* arrays (cross-theory arguments, ite
        // operands, select indices) whose equality atom is not yet encoded,
        // encode it so the next search must decide the pair's arrangement.  A
        // `true` decision merges the arrays in EUF (congruence then
        // propagates / conflicts as usual); a `false` decision records the
        // disequality, and the *next* refinement round's separation query
        // mints the extensionality witness the pair then requires.  Encoding
        // an atom adds no clause of its own, so this phase reports progress
        // through `interface_atoms_encoded` and forces the re-solve from
        // there -- without it the loop would accept a candidate model built
        // while the fresh atoms sat unassigned.
        let mut interface_atoms_encoded: usize = 0;
        for &(a, b) in &interface_pairs {
            let key = unordered_pair(a, b);
            if separated_pairs.contains(&key) {
                // Already separated: the witness clause covers the atom, and
                // Z3 skips `is_diseq` pairs here too.
                continue;
            }
            let atom = manager.mk_eq(a, b);
            if self.term_to_var.contains_key(&atom) {
                continue;
            }
            let _ = self.encode(atom, manager);
            debug_assert!(self.term_to_var.contains_key(&atom));
            interface_atoms_encoded += 1;
        }

        // ======== Phase 3: filter (dedup) and assert ========
        // Deduplication (by interned lemma term) is the real limiter: every
        // candidate below is a *theorem* of the array theory, so asserting it
        // never changes satisfiability, and the candidate set is bounded by
        // the input structure (observed reads × their store chains, plus the
        // gated families above).
        //
        // The previous per-candidate model-satisfaction filter ("skip an
        // instance the candidate model already evaluates to true") drip-fed
        // read-over-write clauses into the core: a flat clause whose guard
        // the model currently falsifies is `true` in the model, gets skipped,
        // and only re-appears – one or two at a time – in later rounds after
        // the search moves the offending index.  Deep chains paid one full
        // re-solve per store level (the depth-60 `storecomm` family needed 60
        // rounds and timed out); Z3 pays one *assertion* per level inside a
        // single search. Asserting the whole bounded batch at once matches
        // that cost shape.
        let mut to_add: Vec<TermId> = Vec::new();
        {
            let model = self.model.as_ref();
            for &inst in &candidates {
                if self.array_axiom_instances.contains(&inst) {
                    continue;
                }
                // Upward-closure instances keep the model filter: they are
                // SYNTHETIC reads (no input atom mentions them), their count
                // grows with chain depth x closed index set rather than with
                // the input, and on satisfiable deep-chain goals almost every
                // `i = j` guard is falsified by the model that eventually
                // survives – asserting them all up front costs a re-solve
                // over a formula many times the input (the depth-10
                // `storeinv` sat side went from milliseconds to 16 s).  The
                // drip-feeding risk that motivated removing the filter for
                // observed reads does not apply the same way here: a skipped
                // upward instance only re-appears when the model actually
                // puts `i = j`, which is exactly when it is needed.
                to_add.push(inst);
            }
            for &inst in &upward_candidates {
                if self.array_axiom_instances.contains(&inst) {
                    continue;
                }
                // Upward-closure instances keep the model filter: they are
                // SYNTHETIC reads (no input atom mentions them), their count
                // grows with chain depth x closed index set rather than with
                // the input, and on satisfiable deep-chain goals almost every
                // `i = j` guard is falsified by the model that eventually
                // survives – asserting them all up front costs a re-solve
                // over a formula many times the input (the depth-10
                // `storeinv` sat side went from milliseconds to 16 s).  A
                // skipped upward instance only re-appears when the model
                // actually commits `i = j` – exactly when it is needed.
                if let Some(m) = model
                    && matches!(
                        self.eval_in_model(inst, m, manager, 0),
                        Some(EvalVal::Bool(true))
                    )
                {
                    continue;
                }
                to_add.push(inst);
            }
        }

        let mut added = interface_atoms_encoded > 0;
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

    /// Whether the two array terms are separated in the search that just
    /// finished: PROVEN disequal in the live EUF state (an asserted-atom
    /// disequality or a congruence-derived one – Z3's `new_diseq_eh`), or
    /// assigned a `false` equality atom by the candidate model.  This is the
    /// demand signal for the extensionality witness: a pair that is separated
    /// *needs* a concrete differing index, which is exactly what the witness
    /// clause supplies.  A pair that is not separated is free to be equal in
    /// the model, so the witness adds nothing but cost.
    ///
    /// Must be called before this round asserts anything: `add_clause`
    /// backtracks the SAT core to root, which drops the saved model the
    /// atom-value query reads.
    fn array_pair_separation(
        &self,
        a: TermId,
        b: TermId,
        manager: &mut TermManager,
    ) -> PairSeparation {
        if let (Some(na), Some(nb)) = (self.euf.term_to_node(a), self.euf.term_to_node(b))
            && self.euf.are_proven_disequal(na, nb)
        {
            return PairSeparation::Euf;
        }
        let atom = manager.mk_eq(a, b);
        if let Some(&var) = self.term_to_var.get(&atom)
            && self.sat.model_value(var).is_false()
        {
            return PairSeparation::AtomFalse;
        }
        PairSeparation::None
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
    /// The subset of [`ArrayStructure::eq_pairs`] whose `Eq` atom occurs in
    /// the *user assertions* (as opposed to inside a lemma this module
    /// asserted earlier).  Instantiation families that exist to make a
    /// specific input shape decidable – write-index read congruence for
    /// conditional inline equalities – must not re-fire off lemma-borne
    /// copies of the same `Eq`, which only re-seeds the closure.
    input_eq_pairs: FxHashSet<(TermId, TermId)>,
    /// Unordered array pairs `(a, b)` for which a DISEQUALITY `a ≠ b` is a
    /// conjunct of the user assertions (`Not(Eq(a, b))` reached at negative
    /// polarity through a chain of `and`s from an assertion root).  These are
    /// the Z3 `new_diseq_eh` pairs: an extensionality witness is *required*
    /// for them unconditionally.
    asserted_diseq_pairs: FxHashSet<(TermId, TermId)>,
    /// Array-sorted terms that appear in a *cross-theory* position: as an
    /// argument of an uninterpreted application (`g(a)`, `sk(a1, a2)`), as an
    /// operand of an array-valued `ite`, or as a `select` index (nested
    /// arrays).  Mirrors Z3's `collect_shared_vars` (`is_shared` /
    /// `is_select_arg`): the equality arrangement of exactly these arrays can
    /// be forced apart by congruence without any read witnessing it, so their
    /// pairwise equality atoms must be decided and, when decided false, be
    /// given an extensionality witness.  Arrays NOT in this set never need a
    /// witness: any separation between them is forced by reads on them, and
    /// those reads' own axioms already carry it.
    interface_arrays: Vec<TermId>,
    /// `array_variable -> store_term`s for every asserted `var = store(...)`.
    /// A variable may appear in several such assertions, so this is a list per
    /// variable – see [`record_alias`] for why dropping the second alias is
    /// unsound.
    aliases: FxHashMap<TermId, Vec<TermId>>,
    /// The subset of [`ArrayStructure::aliases`] whose `var = store`
    /// equality is a *level-0 conjunct* of the user assertions (positive
    /// polarity under an `and`-spine from an assertion root).  Only these may
    /// carry UNGUARDED upward read-over-write facts: a conditional alias
    /// (inside an `ite` / `or` / `=>`) is not a fact, and reasoning as if it
    /// were would fabricate lemmas.
    asserted_aliases: FxHashSet<(TermId, TermId)>,
    /// `(base, store_result)` for every `store` term, used to seed
    /// base↔store extensionality (see [`collect_array_structure`]).
    store_base_pairs: Vec<(TermId, TermId)>,
    /// Distinct indices read on each array operand (for select congruence).
    read_indices: FxHashMap<TermId, Vec<TermId>>,
    /// Constant-function array terms: `((as const S) v)` parses as an
    /// `Apply` named `(as const)` (see the parser's `Head::Qualified` arm) —
    /// an opaque array term unless this module recognizes it.  Maps the
    /// const-array term to its value term.  The constant-array axiom
    /// `select(const v, i) = v` holds for EVERY index, so one unit lemma per
    /// observed read makes the value visible to the core (reads through
    /// equalities chain via select congruence; store-over-const chains via
    /// read-over-write).
    const_arrays: FxHashMap<TermId, TermId>,
}

/// Gather array structure from `term`.  `visited` prevents re-descending
/// shared sub-terms of the interned DAG.
///
/// Iterative (explicit work stack), so nesting depth is bounded by memory
/// rather than by the native call stack – this walk has no error channel, so a
/// depth cap could only silently drop array structure and with it the
/// read-over-write / extensionality lemmas that make the answer sound.
/// Children are pushed in reverse, which reproduces the recursive pre-order
/// exactly and with it the order of `selects`, `eq_pairs` and `read_indices`.
fn collect_array_structure(
    term: TermId,
    from_input: bool,
    manager: &TermManager,
    visited: &mut FxHashSet<TermId>,
    out: &mut ArrayStructure,
) {
    // The stack carries three flags alongside the term:
    //
    // * `positive` (polarity, `true` = positive).  It flips under `Not`, so a
    //   top-level disequality `(not (= var store))` reaches its inner `Eq` at
    //   *negative* polarity.  That matters for `record_alias`: an alias is a
    //   *positive* `var = store` fact, and recording one from a disequality's
    //   inner equality would (a) make `is_self_alias` skip the fresh-witness
    //   extensionality that a disequality *needs*, and (b) feed alias-aware
    //   read-over-write a `var = store` premise that is actually false – both
    //   producing a spurious `sat` on an UNSAT goal (e.g.
    //   `store_noop_disequality_is_unsat`: `select(a,i) = v` with
    //   `a != store(a,i,v)` is UNSAT, but a phantom `a = store(a,i,v)` alias
    //   suppresses the witness and the contradiction is never derived).
    // * `asserted`: the term is a conjunct of the walked root at this
    //   polarity (`root` itself, and `and`-spines descending from it, keep the
    //   flag; everything else – `or`, `=>`, `ite`, `not`-of-or, … – clears
    //   it).  Only `(not (= a b))` at *asserted* negative polarity is a real
    //   disequality fact; the same shape under an `or` is conditional and
    //   certifies nothing.
    // * `from_input`: the sub-term is reachable from a user assertion rather
    //   than from a lemma this module asserted earlier.
    //
    // `eq_pairs` is recorded for either polarity: the extensionality /
    // congruence lemmas are valid regardless, and a disequality *requires*
    // the witness lemma.
    let mut stack: Vec<WalkFrame> = vec![WalkFrame {
        term,
        positive: true,
        asserted: true,
        from_input,
    }];
    while let Some(WalkFrame {
        term,
        positive,
        asserted,
        from_input,
    }) = stack.pop()
    {
        if !visited.insert(term) {
            continue;
        }
        let Some(data) = manager.get(term) else {
            continue;
        };
        match &data.kind {
            TermKind::Not(inner) => {
                stack.push(WalkFrame {
                    term: *inner,
                    positive: !positive,
                    asserted,
                    from_input,
                });
            }
            TermKind::And(args) => {
                for &arg in args.iter().rev() {
                    stack.push(WalkFrame {
                        term: arg,
                        positive,
                        asserted,
                        from_input,
                    });
                }
            }
            TermKind::Select(array, index) => {
                out.selects.push((term, *array, *index));
                let entry = out.read_indices.entry(*array).or_default();
                if !entry.contains(index) {
                    entry.push(*index);
                }
                // An array used as a `select` INDEX is a shared (interface)
                // array in Z3's sense (`is_select_arg`): nested arrays whose
                // equality arrangement cross-theory code can observe.
                if is_array_sorted(*index, manager) {
                    out.interface_arrays.push(*index);
                }
                stack.push(WalkFrame {
                    term: *index,
                    positive,
                    asserted: false,
                    from_input,
                });
                stack.push(WalkFrame {
                    term: *array,
                    positive,
                    asserted: false,
                    from_input,
                });
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
                stack.push(WalkFrame {
                    term: *value,
                    positive,
                    asserted: false,
                    from_input,
                });
                stack.push(WalkFrame {
                    term: *index,
                    positive,
                    asserted: false,
                    from_input,
                });
                stack.push(WalkFrame {
                    term: *base,
                    positive,
                    asserted: false,
                    from_input,
                });
            }
            TermKind::Eq(lhs, rhs) => {
                // Record an array-sorted equality atom (either polarity: the
                // extensionality / congruence lemmas are valid regardless).
                if lhs != rhs && is_array_sorted(*lhs, manager) && is_array_sorted(*rhs, manager) {
                    out.eq_pairs.push((*lhs, *rhs));
                    let key = unordered_pair(*lhs, *rhs);
                    if from_input {
                        out.input_eq_pairs.insert(key);
                    }
                    // A conjunct-level `(not (= a b))` is an asserted array
                    // disequality – the Z3 `new_diseq_eh` trigger.
                    if asserted && !positive {
                        out.asserted_diseq_pairs.insert(key);
                    }
                }
                // Record a `var = store(...)` alias for alias-aware
                // read-over-write – POSITIVE equalities only.  A disequality
                // `(not (= var store))` is not an alias; its inner `Eq` reaches
                // here at `positive == false`.
                if positive {
                    record_alias(*lhs, *rhs, manager, &mut out.aliases);
                    record_alias(*rhs, *lhs, manager, &mut out.aliases);
                    // A level-0 `var = store(...)` conjunct is a fact: the
                    // unguarded upward read-over-write pass below may rely on
                    // it.  Conditional equalities record the alias (for
                    // guarded reasoning) but not this flag.
                    if asserted {
                        mark_asserted_alias(*lhs, *rhs, manager, &mut out.asserted_aliases);
                        mark_asserted_alias(*rhs, *lhs, manager, &mut out.asserted_aliases);
                    }
                }
                stack.push(WalkFrame {
                    term: *rhs,
                    positive,
                    asserted: false,
                    from_input,
                });
                stack.push(WalkFrame {
                    term: *lhs,
                    positive,
                    asserted: false,
                    from_input,
                });
            }
            TermKind::Ite(_, _, _) => {
                // NOTE: array-valued `ite` operands are deliberately NOT
                // recorded as interface arrays.  The `ite` encoding already
                // ties the mux result to the selected branch
                // (`cond => ite = then` / `~cond => ite = else`), so an
                // arrangement between the operands becomes observable only
                // through an equality atom mentioning the mux or a branch –
                // and those atoms reach the separation query through
                // `eq_pairs`.  Pre-emptively encoding every operand pair's
                // atom (the read6 shape: dozens of nested array `ite`s)
                // floods the search with arrangement decisions before it has
                // any structure to decide them with, and stalls the
                // refinement loop.
                for child in get_children(&data.kind).into_iter().rev() {
                    stack.push(WalkFrame {
                        term: child,
                        positive,
                        asserted: false,
                        from_input,
                    });
                }
            }
            TermKind::Apply { func, args } => {
                // `((as const (Array D R)) v)`: the SMT-LIB constant-function
                // array, parsed as a qualified `Apply` whose function name is
                // `(as const)` (see the parser's `Head::Qualified` arm).
                // Without recognizing it here, every read of the array is an
                // opaque select and `select(const v, i) = v` is never derived
                // (QF_ANIA avg40: `F ∧ (= ret5 162)` stayed `sat` against a
                // z3-unsat because the whole heap model read as const-arrays
                // never forced a single stored value).
                if manager.resolve_str(*func) == "(as const)"
                    && args.len() == 1
                    && is_array_sorted(term, manager)
                {
                    out.const_arrays.insert(term, args[0]);
                }
                // An array-sorted argument of an uninterpreted application
                // (`g(a)`, `sk(a1, a2)`) is a shared (interface) array: a
                // disequality between the applications forces the arguments
                // apart by congruence, with no array read witnessing it –
                // exactly the separation for which an extensionality witness
                // exists.  Z3's `is_shared` (parent of another theory's
                // family).
                for &arg in args.iter() {
                    if is_array_sorted(arg, manager) {
                        out.interface_arrays.push(arg);
                    }
                }
                for child in get_children(&data.kind).into_iter().rev() {
                    stack.push(WalkFrame {
                        term: child,
                        positive,
                        asserted: false,
                        from_input,
                    });
                }
            }
            _ => {
                for child in get_children(&data.kind).into_iter().rev() {
                    stack.push(WalkFrame {
                        term: child,
                        positive,
                        asserted: false,
                        from_input,
                    });
                }
            }
        }
    }
}

/// One work-list frame of [`collect_array_structure`].
struct WalkFrame {
    term: TermId,
    positive: bool,
    asserted: bool,
    from_input: bool,
}

/// Canonical unordered pair key.
fn unordered_pair(a: TermId, b: TermId) -> (TermId, TermId) {
    if a.raw() <= b.raw() { (a, b) } else { (b, a) }
}

/// How a pair of arrays came to be separated in the search that just finished
/// (see [`Solver::array_pair_separation`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PairSeparation {
    /// Nothing separates the pair.
    None,
    /// PROVEN disequal in the live EUF state (asserted or congruence-derived)
    /// – the Z3 `new_diseq_eh` case.
    Euf,
    /// The equality atom exists and the candidate model assigned it false.
    /// Weaker than [`PairSeparation::Euf`]: the atom's value may still be a
    /// free CDCL decision rather than a forced fact, but the search has
    /// committed to the separation in the model being refined.
    AtomFalse,
}

/// If `var_term` is a plain variable and `store_term` is a `store` expression,
/// record `var_term -> store_term`.
///
/// A variable may be equated to SEVERAL stores in one formula (e.g.
/// `(= b (store a x v))` and `(= b (store a y w))`), and the array decision
/// procedure must honour ALL of them: dropping the second alias silently
/// loses the read-over-write lemma through it, and the two stores then never
/// get reconciled – a spurious `sat` for an UNSAT goal (Stump-Barrett-Dill-
/// Levitt `array_incompleteness1` shape).  De-duplicate by `store_term` so a
/// repeated identical assertion does not double-instantiate.
/// If `(var_term, store_term)` is a `var = store(...)` pair, record it in the
/// asserted-alias set (see [`ArrayStructure::asserted_aliases`]).
fn mark_asserted_alias(
    var_term: TermId,
    store_term: TermId,
    manager: &TermManager,
    asserted: &mut FxHashSet<(TermId, TermId)>,
) {
    let (Some(var_data), Some(store_data)) = (manager.get(var_term), manager.get(store_term))
    else {
        return;
    };
    if matches!(var_data.kind, TermKind::Var(_)) && matches!(store_data.kind, TermKind::Store(..)) {
        asserted.insert((var_term, store_term));
    }
}

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
    upward_defined: &FxHashSet<(TermId, TermId)>,
    candidates: &mut Vec<TermId>,
) {
    for &(select_term, array, index) in &collected.selects {
        // A read whose (array, index) the upward closure already defined gets
        // its read-over-write content ONE level at a time from those clauses
        // (each level links to the next); re-flattening the whole chain here
        // would duplicate that content depth-many times.
        if upward_defined.contains(&(array, index)) {
            continue;
        }
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
                // A store index that is SYNTACTICALLY the read index makes
                // every SAME guard's antecedent true and the ELSE disjunction
                // trivially satisfiable (`... ∨ index = ki` with ki == index):
                // the else clause is then a tautology and is dropped rather
                // than materialised.  Materialising it would mint
                // `select(ultimate_base, index)` - and on read-modify-write
                // heaps the ultimate base is itself a nested select, so the
                // fresh read re-seeds the select-over-select arm and the
                // chain resolves one memory level per refinement round
                // (the quadratic instance growth that first landed the
                // select-over-select fix: 0 -> 373 -> 997 -> 1659 over four
                // rounds on QF_ANIA avg40).
                if !entries.iter().any(|(ki, _)| *ki == index) {
                    let base_read = manager.mk_select(ultimate_base, index);
                    let mut else_disj: Vec<TermId> = Vec::with_capacity(entries.len() + 1);
                    else_disj.push(manager.mk_eq(select_term, base_read));
                    else_disj.extend(idx_eqs);
                    candidates.push(manager.mk_or(else_disj));
                }
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
            //    refinement round instead of N – which collapses the timeout on
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
            // to the arithmetic/EUF solvers – see the RoW note above); the new
            // `select(a, i)` / `select(b, i)` terms seed further instantiation
            // in the next refinement round.
            let read_a = manager.mk_select(a, index);
            let read_b = manager.mk_select(b, index);
            let hit = manager.mk_eq(select_term, read_a);
            let miss = manager.mk_eq(select_term, read_b);
            let not_c = manager.mk_not(c);
            candidates.push(manager.mk_implies(c, hit));
            candidates.push(manager.mk_implies(not_c, miss));
        } else if let Some((inner_array, inner_idx)) = as_select(array, manager) {
            // select-over-select: `select (select A j) i`, the
            // read-modify-write heap shape (`store(mem, base,
            // store(select(mem, base), off, v))`, Ultimate memory models).
            // The array operand is itself a read; resolve that inner read
            // through A's FULL store chain (aliases followed, so one round
            // instead of one level per round).  When a chain store's index
            // equals `j`, the array operand IS that store's value, so the
            // outer read twins to a read of the value (which the next
            // round's own read-over-write resolves).  Without this arm the
            // inner read is an opaque array term and the stored value never
            // reaches the outer read (QF_ANIA avg40: `F AND (= ret5 162)`
            // stayed `sat` against z3-unsat).
            let chain = collected
                .aliases
                .get(&inner_array)
                .and_then(|_| aliased_store_map(inner_array, &collected.aliases, manager))
                .or_else(|| {
                    direct_store_map(inner_array, manager).map(|(b, e)| (b, e, Vec::new()))
                });
            if let Some((_chain_base, entries, guard_pairs)) = chain
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
                // A store whose index is SYNTACTICALLY the read index makes
                // the resolution unconditional (outermost hit wins: entries
                // are newest-first) and every SAME guard's antecedent
                // trivially true - the ELSE disjunction is then trivially
                // satisfiable too, so it is dropped rather than
                // materialised.  A materialised ELSE twin is itself a
                // select-over-select and re-seeds this arm every round: the
                // quadratic instance growth that the first version of this
                // fix showed on avg40 (0 -> 373 -> 997 -> 1659 instances
                // over four rounds and a 2s -> 60s+ blowup).
                let syntactic_hit = entries
                    .iter()
                    .find(|(idx, _)| *idx == inner_idx)
                    .map(|&(idx, val)| (idx, val));
                if let Some((_, val)) = syntactic_hit {
                    let twin = manager.mk_select(val, index);
                    let same = manager.mk_eq(select_term, twin);
                    candidates.push(match guard_term {
                        Some(g) => manager.mk_implies(g, same),
                        None => same,
                    });
                }
                // No syntactic hit: the non-matching arrangement (store index
                // DIFFERS from the read index) is deliberately NOT
                // materialised here.  An ELSE twin would be a fresh nested
                // select that re-seeds this arm (and the upward-closure /
                // witness paths) every round - measured as the growth that
                // stalls the refinement loop on satisfiable QF_ANIA goals
                // (floppy2: `sat` 2.6 s -> honesty-gated `unknown`).  The
                // matching-index resolution above already covers the
                // RMW-heaps this arm exists for; the differing-index case
                // stays with the pre-existing machinery (incomplete, as
                // before this fix).
            }
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
        // INPUT atoms only.  Lemmas this module asserts (witness clauses,
        // congruence implications) re-contain the same `Eq` atoms, and firing
        // write-index congruence off those copies manufactures a fresh
        // `select(var, store_idx)` pair per copy per round – the closure
        // growth that stalled the refinement loop on deep chains.
        if !collected.input_eq_pairs.contains(&unordered_pair(a, b)) {
            continue;
        }
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

/// Upward read-over-write through a LEVEL-0 alias (Z3
/// `theory_array_full::set_prop_upward` + `instantiate_axiom2b`).
///
/// For every asserted `c = store(a, i, v)` and every index `j` the base `a` is
/// read at, the read of the WRITE at `j` is exactly
/// `ite(i = j, v, select(a, j))`.  Materialising `select(c, j)` with those two
/// case-split facts (UNGUARDED – the alias is a level-0 unit) is what lets an
/// asserted array equality between two aliased chains refute through the base
/// reads: e.g. the `storeinv` family, where `a_1 = store(a1,i1,e_0)` and
/// `a_1 = a_3` must force `select(a1, sk) = select(a2, sk)` – impossible with
/// `e_5 != e_6`.  Without this pass `select(a_1, j)` never exists as a term,
/// EUF congruence on `a_1 = a_3` has nothing to close over, and the goal goes
/// through as a false `sat`.
///
/// This is also the *replacement* for the old base-pair select-congruence
/// clauses (`a1 = store(a1,i1,e_0) => select(a1,j) = select(store(...),j)`):
/// those guarded clauses mostly sat vacuously (the antecedent is a free `false`
/// decision), and re-reading that free decision as a demanded separation
/// minted witnesses for every chain link – the closure growth this rework
/// exists to kill.  The upward facts carry the useful content without creating
/// the separating atoms at all.
///
/// Conditional aliases (a `var = store` equality under an `ite` / `or` / `=>`)
/// are NOT facts and are skipped here; the guarded per-alias lemmas of
/// [`build_read_over_write`] remain their path.
fn build_connected_upward_read_over_write(
    manager: &mut TermManager,
    collected: &ArrayStructure,
    candidates: &mut Vec<TermId>,
) -> FxHashSet<(TermId, TermId)> {
    let mut upward_defined: FxHashSet<(TermId, TermId)> = FxHashSet::default();
    let connected = connected_array_set(collected, manager);
    if connected.is_empty() {
        return upward_defined;
    }
    // Flow the observed read indices UP through the store/alias graph to a
    // fixpoint BEFORE minting axioms, so a depth-N chain whose bottom link is
    // read at `j` gets `select(link_k, j)` for EVERY level k in this single
    // round.  Minting one level per refinement round instead costs one full
    // re-solve per level (the depth-60 `storecomm` chains timed out exactly
    // there), and the dataflow is finite: each iteration adds an index to
    // some array's set, and both sets are bounded by the collected structure.
    let mut idx_closure: FxHashMap<TermId, Vec<TermId>> = collected.read_indices.clone();
    loop {
        let mut changed = false;
        // Store edge: `store(base, ...)`'s reads at `j` include the base's.
        for &(base, store_term) in &collected.store_base_pairs {
            flow_indices(&mut idx_closure, base, store_term, &mut changed);
        }
        // Alias edge: an asserted `var = store(base, ...)` makes the var and
        // the store term the same array, so the var inherits the base's
        // indices (and a chain through alias vars continues past the store
        // edge's result).
        for (&var, store_terms) in &collected.aliases {
            for &store_term in store_terms {
                let Some((base, _, _)) = as_store(store_term, manager) else {
                    continue;
                };
                flow_indices(&mut idx_closure, base, var, &mut changed);
                flow_indices(&mut idx_closure, base, store_term, &mut changed);
            }
        }
        if !changed {
            break;
        }
    }
    // Mint the upward read-over-write axioms.  Unlike the guarded congruence
    // clauses these are UNCONDITIONAL theorems: `select(store(a,i,v), j) =
    // ite(i = j, v, select(a, j))` needs no antecedent.  They are limited to
    // CONNECTED chains – chains an input array equality compares – because a
    // chain with no equality partner never needs its lower reads lifted, and
    // lifting them anyway cascades a read per link per level.
    for &(base, store_term) in &collected.store_base_pairs {
        if !connected.contains(&base) {
            continue;
        }
        let Some((_, store_idx, stored_val)) = as_store(store_term, manager) else {
            continue;
        };
        let Some(indices) = idx_closure.get(&base) else {
            continue;
        };
        for &j in indices {
            let read_s = manager.mk_select(store_term, j);
            let idx_eq = manager.mk_eq(store_idx, j);
            let hit = manager.mk_eq(read_s, stored_val);
            candidates.push(manager.mk_implies(idx_eq, hit));
            let idx_neq = manager.mk_not(idx_eq);
            let base_read = manager.mk_select(base, j);
            let miss = manager.mk_eq(read_s, base_read);
            candidates.push(manager.mk_implies(idx_neq, miss));
            upward_defined.insert((store_term, j));
        }
    }
    // Aliased form: an asserted `var = store(base, i, v)` also carries the
    // read on the VAR itself (same axiom, and the var is what other input
    // atoms mention).
    for (&var, store_terms) in &collected.aliases {
        if !connected.contains(&var) {
            continue;
        }
        for &store_term in store_terms {
            let Some((base, store_idx, stored_val)) = as_store(store_term, manager) else {
                continue;
            };
            let Some(indices) = idx_closure.get(&base) else {
                continue;
            };
            for &j in indices {
                let read_v = manager.mk_select(var, j);
                let idx_eq = manager.mk_eq(store_idx, j);
                let hit = manager.mk_eq(read_v, stored_val);
                candidates.push(manager.mk_implies(idx_eq, hit));
                let idx_neq = manager.mk_not(idx_eq);
                let base_read = manager.mk_select(base, j);
                let miss = manager.mk_eq(read_v, base_read);
                candidates.push(manager.mk_implies(idx_neq, miss));
                upward_defined.insert((var, j));
            }
        }
    }
    upward_defined
}

/// Flow `from`'s closed read-index set into `to`'s (one dataflow step of the
/// upward closure in [`build_connected_upward_read_over_write`]).
fn flow_indices(
    idx_closure: &mut FxHashMap<TermId, Vec<TermId>>,
    from: TermId,
    to: TermId,
    changed: &mut bool,
) {
    let Some(src) = idx_closure.get(&from).cloned() else {
        return;
    };
    let entry = idx_closure.entry(to).or_default();
    for j in src {
        if !entry.contains(&j) {
            entry.push(j);
            *changed = true;
        }
    }
}

/// The set of array terms whose store chains are *connected through an input
/// array equality* – an `Eq` atom from the user assertions that is not itself
/// a `var = store` alias definition.  Comparing two such chains pointwise
/// (which is what the upward read pass materialises) is only ever needed
/// between arrays the input actually equates; a chain with no equality
/// partner never needs its lower reads lifted, and lifting them anyway
/// cascades one read per link per level – the closure growth that stalls
/// deep `swap` / `storecomm` chains.
///
/// Seeded from the operands of non-alias input `Eq` atoms (either polarity: a
/// asserted disequality between two differently-based store chains is refuted
/// by the very same pointwise comparison) and closed DOWN each operand's alias
/// / store chain to the ultimate base, so every link that a compared read must
/// traverse is a member.
fn connected_array_set(collected: &ArrayStructure, manager: &TermManager) -> FxHashSet<TermId> {
    let mut connected: FxHashSet<TermId> = FxHashSet::default();
    let mut work: Vec<TermId> = Vec::new();
    for &(a, b) in &collected.eq_pairs {
        if !collected.input_eq_pairs.contains(&unordered_pair(a, b)) {
            continue;
        }
        if is_alias_pair(a, b, &collected.aliases) || is_alias_pair(b, a, &collected.aliases) {
            continue;
        }
        work.push(a);
        work.push(b);
    }
    while let Some(t) = work.pop() {
        if !connected.insert(t) {
            continue;
        }
        // Follow the term's own store chain down, and any asserted alias
        // definitions of it down their bases.
        let mut cur = t;
        while let Some((base, _, _)) = as_store(cur, manager) {
            if !connected.insert(base) {
                break;
            }
            cur = base;
        }
        if let Some(stores) = collected.aliases.get(&t) {
            for &store_term in stores {
                if let Some((base, _, _)) = as_store(store_term, manager)
                    && !connected.contains(&base)
                {
                    work.push(base);
                }
            }
        }
    }
    connected
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
/// arrays that a *complete* finite-disjunction clause settles – reads on those
/// arrays need not be eagerly unfolded (the clause decides them), which is the
/// lever that makes a depth-60 `storecomm` chain one flat clause instead of a
/// 60-deep unfolding.
fn build_extensionality_and_congruence(
    manager: &mut TermManager,
    collected: &ArrayStructure,
    separated_pairs: &FxHashSet<(TermId, TermId)>,
    interface_pairs: &[(TermId, TermId)],
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
    // it to EVERY store – including the innermost write of a deep `storecomm`
    // chain – spawns extensionality pairs whose witness reads unfold the whole
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
    // Base `(array, store-of-that-array)` pairs feed finite-disjunction; they
    // are NOT eligible for a fresh-witness clause and no longer feed select
    // congruence (`build_connected_upward_read_over_write` carries the alias-shape
    // bridge as level-0 facts instead – see its doc comment).
    for &(base, result) in &collected.store_base_pairs {
        if aliased_stores.contains(&result)
            && !pairs.contains(&(base, result))
            && !pairs.contains(&(result, base))
        {
            pairs.push((base, result));
        }
    }
    // Interface pairs take part in extensionality (witness) decisions only;
    // finite-disjunction / congruence over them is covered by their own atoms.
    for &(a, b) in interface_pairs {
        let key = unordered_pair(a, b);
        if !pairs.iter().any(|&(x, y)| unordered_pair(x, y) == key) {
            pairs.push((a, b));
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
        // deterministic witness index per unordered pair.  Minted ONLY for a
        // SEPARATED pair (`separated_pairs` – Z3's `new_diseq_eh` semantics):
        // an asserted input disequality, a pair the finished search proved
        // disequal in EUF, or a pair whose equality atom the candidate model
        // assigned false.  Extensionality exists to give a *demanded*
        // separation a concrete differing index; a pair nothing separates is
        // free to be equal in the model, and minting its witness anyway used
        // to unfold `select(a,k)` / `select(b,k)` through whole store chains
        // for every (base, store-of-it) pair of every chain link – the ~10-round
        // cascade that stalled deep `swap` / `storecomm` goals.  The demand
        // signal is made available by the interface-equality phase (Z3
        // `mk_interface_eqs`): cross-theory array pairs get their `a = b` atom
        // encoded so CDCL decides it, and a false decision lands the pair in
        // `separated_pairs` next round.
        //
        // Also skipped for a *self-alias* pair – one whose `a = b` IS an
        // asserted alias equality (`(= var store...)` collected in
        // [`ArrayStructure::aliases`]).  There `a = b` is a level-0 fact, so
        // the witness clause `a = b ∨ ...` is trivially satisfied and adds
        // nothing.  SOUND: the skipped clause is a tautology under the
        // level-0 alias, and the witness could never fire (`a ≠ b` is
        // impossible while the alias holds); the lemmas are retracted on `pop`
        // with the alias.
        let is_self_alias =
            is_alias_pair(a, b, &collected.aliases) || is_alias_pair(b, a, &collected.aliases);
        // A complete finite-disjunction clause also makes the witness redundant
        // (see [`finite_disjunction_extensionality`]: the flat value-disjunction
        // already decides `a = b`, and a fresh witness outside both store sets
        // can never witness `a ≠ b` over a shared base).
        if !(is_self_alias || pair_complete)
            && separated_pairs.contains(&unordered_pair(a, b))
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
        // read on either side.  INPUT pairs only, and never for a base
        // `(array, store-of-that-array)` pair: those `Eq` atoms do not occur
        // in the input, so materialising them here hands SAT a free `false`
        // decision (the implication is satisfied vacuously), which the next
        // round's separation query then misreads as a *demanded* array
        // separation – minting witnesses and unfolding whole chains for pairs
        // nothing separates.  EUF congruence closure already carries the
        // `a = b ⇒ select(a,j) = select(b,j)` consequence for every asserted
        // equality; this clause only has to cover input atoms whose reads the
        // lazy RoW pass would not otherwise connect.
        if !collected.input_eq_pairs.contains(&unordered_pair(a, b)) {
            continue;
        }
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

/// `(select A i)` destructuring for the select-over-select arm of
/// [`build_read_over_write`].
fn as_select(term: TermId, manager: &TermManager) -> Option<(TermId, TermId)> {
    match manager.get(term)?.kind {
        TermKind::Select(array, index) => Some((array, index)),
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
/// map, which is not useful here – callers gate on a non-empty map).
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
/// directly, without an array `select` unfolding – anything that is not a
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
/// pair – and it compares value terms directly (no `select`, no
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
    // clause decides `a = b` with no array-select unfolding – a common
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
    // (3) the SAME index set on both sides – a differing index set forces a
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
    // side).  All comparisons are on value terms / opaque base reads – no
    // read-over-write unfolding – so this is a flat clause regardless of chain
    // depth.
    let mut disjuncts: Vec<TermId> = vec![manager.mk_eq(a, b)];
    for (idx, va) in &ma {
        match mb.iter().find(|(i, _)| *i == *idx) {
            Some((_, vb)) if vb != va => {
                let eq = manager.mk_eq(*va, *vb);
                disjuncts.push(manager.mk_not(eq));
            }
            Some(_) => {} // shared index, equal value terms – cannot witness a diff
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
    // identical base – sound to assert, and it forces a conflict with any
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
    /// stack available per level – far under any native frame – not the
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
                collect_array_structure(select, true, &tm, &mut visited, &mut out);
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
        collect_array_structure(current, true, &tm, &mut visited, &mut out);
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
        collect_array_structure(both, true, &tm, &mut visited, &mut out);

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
        // The alias equality is a positive conjunct of the walked root, so it
        // is recorded as an input pair AND as a level-0 (asserted) alias; the
        // `select` equality is Int-sorted, so no pair is recorded for it.
        assert!(out.input_eq_pairs.contains(&(b, store_a)));
        assert!(out.asserted_aliases.contains(&(b, store_a)));
        assert!(out.asserted_diseq_pairs.is_empty());
    }

    /// The asserted-context/polarity bookkeeping: only a `not(= a b)` that is
    /// a conjunct of the walked root counts as an asserted array
    /// disequality; the same shape under an `or` is conditional and must not
    /// be recorded (it would mint an unconditional extensionality witness).
    #[test]
    fn s8_collect_array_structure_asserted_diseq_context() {
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let array_sort = tm.sorts.array(int_sort, int_sort);
        let a = tm.mk_var("a", array_sort);
        let b = tm.mk_var("b", array_sort);
        let t = tm.mk_var("t", tm.sorts.bool_sort);
        let eq_ab = tm.mk_eq(a, b);
        let diseq = tm.mk_not(eq_ab);

        // Conjunct of the root: an asserted disequality.
        let mut visited = FxHashSet::default();
        let mut out = ArrayStructure::default();
        let root = tm.mk_and(vec![diseq, t]);
        collect_array_structure(root, true, &tm, &mut visited, &mut out);
        assert_eq!(
            out.asserted_diseq_pairs,
            FxHashSet::from_iter([(unordered_pair(a, b))])
        );

        // Under an `or`: conditional, not asserted.
        let mut visited = FxHashSet::default();
        let mut out = ArrayStructure::default();
        let root = tm.mk_or(vec![diseq, t]);
        collect_array_structure(root, true, &tm, &mut visited, &mut out);
        assert!(out.asserted_diseq_pairs.is_empty());
        // ... but it is still an `eq_pair` (valid congruence material).
        assert_eq!(out.eq_pairs, vec![(a, b)]);
    }

    /// Cross-theory arguments are interface arrays; plain `select` array
    /// operands are not (their arrangement is witnessed by the reads
    /// themselves), and neither are array `ite` operands (see the walk's
    /// `Ite` arm for why).
    #[test]
    fn s8_collect_array_structure_interface_arrays() {
        let mut tm = TermManager::new();
        let int_sort = tm.sorts.int_sort;
        let array_sort = tm.sorts.array(int_sort, int_sort);
        let a = tm.mk_var("a", array_sort);
        let b = tm.mk_var("b", array_sort);
        let i = tm.mk_int(num_bigint::BigInt::from(1));

        // g(a) with g uninterpreted: `a` is an interface array.
        let ga = tm.mk_apply("g", vec![a], array_sort);
        let _ = tm.mk_eq(ga, b);
        let sel = tm.mk_select(a, i);
        let _ = tm.mk_eq(sel, i);

        let mut visited = FxHashSet::default();
        let mut out = ArrayStructure::default();
        collect_array_structure(sel, true, &tm, &mut visited, &mut out);
        assert!(
            out.interface_arrays.is_empty(),
            "a select's array operand is not an interface array"
        );

        let mut visited = FxHashSet::default();
        let mut out = ArrayStructure::default();
        collect_array_structure(ga, true, &tm, &mut visited, &mut out);
        assert_eq!(out.interface_arrays, vec![a]);
    }
}
