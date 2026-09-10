//! Unified bit-blasting: BV gate circuits built into the **main** SAT core.
//!
//! Stage 1 of the BV-circuit unification campaign
//! (`docs/handovers/2026-09-07-bv-unification.md`, Option A).  In the
//! historical architecture `BvSolver` owns an embedded SAT instance; BV atoms
//! are free Booleans to the main CDCL core, the theory manager replays each
//! assignment into the embedded solver, and only at the next theory check
//! does that solver run to consistency.  The campaign's measured ceilings –
//! the batch latency every QF_BV instance pays on the general path, and the
//! `distinct`-over-BV row that cannot converge under either encoding – both
//! reduce to that interleaving: gate propagation that would happen
//! per-decision in a unified core happens per-theory-check instead.
//!
//! This module turns the main core into the circuit target for *eligible*
//! generations.  At assertion time, after the Tseitin encoder has given every
//! Bool atom its main-core variable, each BV atom's defining circuit is built
//! **into the main core** and linked to that variable
//! (`atom_var <=> circuit_output`, two clauses).  From then on the atom's
//! semantics are ordinary clauses: deciding or propagating the atom moves the
//! bits natively during the descent, conflicts involving the atom are learned
//! by the main CDCL engine over its own literals, and the theory manager
//! skips the embedded assert+check round-trip for that atom.
//!
//! # Soundness envelope
//!
//! * The added clauses are Tseitin definitions of atoms the formula already
//!   constrains – a definitional extension, equisatisfiable with the input,
//!   so both `Unsat` (refutation of an extended but equisatisfiable clause
//!   set) and learned clauses over bit literals are sound.
//! * All-or-nothing per generation: a *generation* is the span between two
//!   eligibility decisions.  If any gate fails (a quantified/array/BV-result-
//!   UF assertion arrives, a user scope opens, the shape is ring-dominated
//!   with the arithmetic relaxation active, the subterm budget trips), the
//!   generation ends and [`BvSolver::exit_unified`] wipes every
//!   var-space-carrying table, so the lazy embedded path can never consume a
//!   main-core var.  Circuits already added survive (definitional, sound).
//! * **No UF application may return a bit-vector** in a unified generation:
//!   congruence-derived merges of BV-sorted `Apply` terms reach the bits
//!   today through `notify_equality -> assert_eq`; in a unified generation
//!   no clause can express a search-dependent merge, and a free-vector
//!   substitute would let the model disagree with congruence.  Datatype
//!   selectors over BV carriers are `Apply`s too, so they are covered by the
//!   same gate.
//! * **Honesty gate**: a BV atom the manager sees assigned *without* a
//!   unified circuit (late-minted atoms: `distinct` pair atoms, refinement
//!   lemmas) is recorded, and a `Sat` exit with unlinked atoms is not an
//!   honest model – `check_core` builds the missing links and re-searches
//!   (bounded rounds), answering `Unknown` only if the budget runs out.
//!
//! # What is deliberately *not* unified yet
//!
//! * The eager pure-QF_BV dispatch (`dispatch_pure_bv`) keeps its own
//!   single-shot embedded solve; it ends any unified generation before it
//!   drives the BV solver.
//! * Ring-dominated formulas with the arithmetic relaxation active keep the
//!   lazy path (the same routing the dispatch applies: the relaxation is the
//!   better decision procedure there, measured on the `Sage2` family).
//! * Incremental sessions keep the lazy path from the first `push` on:
//!   circuits added above the base scope would need scope-journalled memo
//!   retraction (the embedded solver's pop-decapitation problem all over
//!   again), which is stage-2 work.

use super::theory_bv_encode::encode_bv_term_recursive;
use super::*;
use nixie_core::ast::get_children;
use nixie_core::ast::{TermId, TermKind, TermManager};

/// Upper bound on distinct sub-terms one unified link pass will walk.  The
/// eager dispatch's fragment walk uses 2M; unification additionally creates
/// a main-core var per comparison *atom*, so the budget must keep C(n,2)
/// `distinct` blowups (n=2000 ⇒ ~2M pair atoms) on the lazy path instead of
/// eagerly linking two million equality circuits at assertion time.
const UNIFIED_LINK_BUDGET: usize = 200_000;

/// One BV atom to link (the atom term; its operands reach the builder via
/// the `bv_sorted` operand list).
#[derive(Debug, Clone, Copy)]
struct BvAtomToLink {
    term: TermId,
}

/// One pending **order-encoding spec** for a spine-asserted `distinct` over
/// BitVec (Option A stage 2 of the campaign): the term, its main-core
/// result var, the argument wires followed by the minted pad wires, and the
/// common width.
///
/// Recorded by `emit_assertion_clauses` exactly at fact positions (the
/// unit on `var` is emitted there; see `order.rs`'s module docs for why the
/// encoding is only sound in that shape).  The unified link pass builds the
/// bitonic network and drains the spec; `check` materialises any spec that
/// is still pending as the pairwise encoding at base scope.
#[derive(Debug, Clone)]
pub(crate) struct BvOrderSpec {
    /// The `distinct` term (for memoisation, guards, and diagnostics).
    pub term: TermId,
    /// The main-core var carrying the term's truth value.
    pub var: nixie_sat::Var,
    /// Argument wires first, then pads; every wire `width` bits.
    pub wires: Vec<TermId>,
    /// Common bit width of all wires.
    pub width: u32,
}

impl Solver {
    /// Whether unified bit-blasting is enabled (`NIXIE_BV_UNIFIED=0` disables;
    /// default on for eligible generations).
    pub(super) fn bv_unify_enabled() -> bool {
        match std::env::var("NIXIE_BV_UNIFIED") {
            Ok(v) => !(v == "0" || v.is_empty()),
            Err(_) => true,
        }
    }

    /// Whether pure QF_BV goals route through the unified main core instead
    /// of the eager embedded dispatch (`NIXIE_BV_DISPATCH_UNIFIED=0` restores
    /// the dispatch; default on – stage 4 of the campaign, flipped by the
    /// pre-registered corpus measurement: geomean 1.36× over the committed
    /// 300-file sample, zero verdict mismatches, +10/−5 timeouts at 30 s;
    /// see `docs/studies/2026-09-07-bv-dispatch-unification.md`).
    ///
    /// Routing declines the dispatch for goals the unified window can own
    /// (see [`Self::bv_unified_window_open`]); ring-dominated goals keep
    /// their existing general-path routing, and wide-`bvmul` goals keep the
    /// dispatch (its CEGAR machinery has no unified-path equivalent).
    pub(crate) fn bv_dispatch_unified() -> bool {
        match std::env::var("NIXIE_BV_DISPATCH_UNIFIED") {
            Ok(v) => !(v == "0" || v.is_empty()),
            Err(_) => true,
        }
    }

    /// Whether a unified build window may open **right now** (assertion
    /// time).  Every gate here is a generation-breaking condition when it
    /// flips false later; see the module docs for why failure *ends* the
    /// generation rather than falling back per-atom.
    fn bv_unified_window_open(&self) -> bool {
        Self::bv_unify_enabled()
            && self.context_stack.is_empty()
            && !self.has_quantifiers
            && !self.has_array_ops
            && self.array_select_terms.is_empty()
            && self.array_store_terms.is_empty()
            && self.proof.is_none()
            && self.config.certification_mode == CertificationMode::Uncertified
            && !self.has_bv_result_uf
            // The eager dispatch owns the all-blastable fragment (its
            // single-shot embedded solve is the better architecture there;
            // unification would blast every file twice) – unless stage 4's
            // routing mode hands the fragment to the unified core.
            && (Self::bv_dispatch_unified() || !self.all_assertions_bv_fragment)
            // Ring-dominated + relaxation active: the arith relaxation is
            // the better procedure (the dispatch applies the same routing);
            // eager circuits would only bloat the main core.
            && (!self.has_bv_ring_ops || self.arith_terms.is_empty())
    }

    /// Begin (or continue) a unified generation and link every BV atom of
    /// `root` into the main core.
    ///
    /// Called from the assertion path after `emit_assertion_clauses`, so the
    /// Tseitin encoder has already created the atom vars this pass links to.
    /// Also sweeps `var_to_constraint` for BV-sorted-operand atoms that carry
    /// no unified circuit yet – that is where the pairwise atoms of a large
    /// `distinct` show up (they are minted by the `Distinct` encode arm, not
    /// by sub-term walking).
    pub(super) fn link_bv_circuits_unified(&mut self, root: TermId, manager: &TermManager) {
        // ---- Pass 1 (no SAT access): collect the shapes, abort on breakers.
        let mut bv_sorted: Vec<TermId> = Vec::new();
        let mut bv_atoms: Vec<BvAtomToLink> = Vec::new();
        let mut bool_leaves: Vec<TermId> = Vec::new();
        if !self.collect_unified_bv_terms(
            root,
            manager,
            &mut bv_sorted,
            &mut bv_atoms,
            &mut bool_leaves,
        ) {
            self.end_bv_unified_generation();
            return;
        }
        self.collect_unified_constraint_atoms(manager, &mut bv_sorted, &mut bv_atoms);
        // A Bool-selector-only sweep (no BV atoms or operands in *this*
        // assertion) is worth a window only when the generation already
        // blasted circuits – a later `(not c)` must tie the selector of an
        // *earlier* assertion's `ite` to the main core.  A goal with no
        // circuits anywhere (pure propositional) never opens a window, so
        // the structural encoder's var-count contract holds untouched.
        if bv_atoms.is_empty()
            && bv_sorted.is_empty()
            && (bool_leaves.is_empty() || !self.bv.has_circuits())
        {
            return;
        }
        // The budget also bounds the *link* set: a large `distinct`'s C(n,2)
        // pair atoms arrive through the constraint sweep, not the sub-term
        // walk, and eagerly linking two million equality circuits at
        // assertion time is the blast the budget exists to prevent (n=2000
        // ⇒ ~2M atoms).  Operands are counted *distinctly* – the sweep
        // records one entry per (atom, operand) incidence, but the builder
        // memoises each term once.  Over budget ends the generation – the
        // lazy path builds each pair's circuit only when the search assigns
        // it.
        if !bv_atoms.is_empty() {
            let distinct_operands: FxHashSet<TermId> = bv_sorted.iter().copied().collect();
            if distinct_operands.len() + bv_atoms.len() > UNIFIED_LINK_BUDGET {
                self.end_bv_unified_generation();
                return;
            }
        }

        // ---- Pass 2: build, inside a window over the main core.
        let term_to_var = &self.term_to_var;
        let mut linked_atoms = 0usize;
        self.bv.build_with(&mut self.sat, |bv| {
            let mut encoded: FxHashSet<TermId> = FxHashSet::default();
            // Operands first: `encode_bool_node` on an atom requires its
            // operands' bits to exist.
            for &t in &bv_sorted {
                let width = manager
                    .get(t)
                    .and_then(|td| manager.sorts.get(td.sort))
                    .and_then(|s| s.bitvec_width());
                let Some(width) = width else { continue };
                if !encode_bv_term_recursive(bv, t, manager, &mut encoded) {
                    // Free-vector fallback (UF results, exotic shapes): the
                    // atom circuits still constrain these bits.
                    bv.new_bv(t, width);
                }
            }
            for atom in &bv_atoms {
                let Some(circuit_var) = bv.encode_bool_node(atom.term, manager) else {
                    // Shape outside the boolean encoder (e.g. mismatched
                    // widths on an ill-sorted input): leave unlinked.  The
                    // lazy path would not have modelled it either; the
                    // pending-atom honesty gate degrades such an atom to
                    // `Unknown` rather than guessing.
                    continue;
                };
                if let Some(&main_var) = term_to_var.get(&atom.term) {
                    bv.link_bool_vars(main_var, circuit_var);
                }
                bv.note_unified_atom(atom.term);
                linked_atoms += 1;
            }
            for &leaf in &bool_leaves {
                // Tie the circuit's selector var to the main-core var of
                // the same Bool leaf, when the leaf has one (a selector
                // under no other constraint keeps its fresh var – free, as
                // the lazy path would leave it).
                if let Some(&main_var) = term_to_var.get(&leaf)
                    && let Some(circuit_var) = bv.bool_node_var(leaf)
                {
                    #[cfg(feature = "std")]
                    if std::env::var("NIXIE_BV_UNIFIED_TRACE").is_ok() {
                        eprintln!("[bv-unified] bool leaf {leaf:?}: main={main_var:?} circuit={circuit_var:?}");
                    }
                    bv.link_bool_vars(main_var, circuit_var);
                }
            }
        });
        self.build_order_specs_in_window(manager);
        #[cfg(feature = "std")]
        if std::env::var("NIXIE_BV_UNIFIED_TRACE").is_ok() {
            eprintln!(
                "[bv-unified] link pass: {} atoms linked, main sat vars = {}",
                linked_atoms,
                self.sat.num_vars()
            );
        }
    }

    /// The assertion path's BV routing: unified link pass when a window may
    /// open, the historical embedded blast otherwise.
    ///
    /// This is the one place the two BV architectures are chosen between;
    /// every other site reacts to the decision (`bv_unified` /
    /// `BvSolver::is_unified`).  A window that cannot open *ends* an active
    /// generation (see the module docs: per-atom fallback would mix the two
    /// var spaces) and falls back to the embedded blast for this assertion.
    pub(super) fn link_or_blast_bv_circuits(&mut self, term: TermId, manager: &TermManager) {
        // Track whether the eager pure-BV dispatch remains a candidate for
        // the whole assertion set: while it is, unification stays off (the
        // dispatch's single-shot embedded solve is the better architecture
        // for that fragment; linking first would blast every file twice).
        if !super::dispatch_pure_bv::assertion_in_bv_fragment(term, manager) {
            self.all_assertions_bv_fragment = false;
        }
        // elim-uncnstr deferral: when the check-time unconstrained-variable
        // elimination is predicted to *delete* this assertion's expensive
        // circuits outright, skip building them now (Z3's `qfbv` pipeline
        // eliminates before bit-blasting; eagerly building a 1024-bit
        // divider network that the rewrite removes burns the whole budget
        // before the check ever starts).  Deferred atoms stay unlinked and
        // are owned by the check-time decision: the eager dispatch's
        // elimination pass if it fires (see `bv_elim_uncnstr`), otherwise
        // `bv_restore_deferred_circuits` pays the bet back before the
        // general path runs.
        if self.bv_elim_defer_eager_blast(term, manager) {
            self.bv_elim_deferred.push(term);
            return;
        }
        self.link_or_blast_bv_circuits_inner(term, manager);
    }

    /// The eager link/blast itself, separated from the deferral decision so
    /// [`Solver::bv_restore_deferred_circuits`] can replay it without
    /// re-triggering the deferral scan.
    fn link_or_blast_bv_circuits_inner(&mut self, term: TermId, manager: &TermManager) {
        if self.bv_unified_window_open() {
            if !self.bv_unified {
                self.bv.enter_unified();
                self.bv_unified = true;
                #[cfg(feature = "std")]
                if std::env::var("NIXIE_BV_UNIFIED_TRACE").is_ok() {
                    eprintln!("[bv-unified] generation entered");
                }
            }
            self.link_bv_circuits_unified(term, manager);
        } else {
            self.end_bv_unified_generation();
            self.blast_bv_circuits_at_base_scope(term, manager);
        }
    }

    /// Pay back the elim-uncnstr deferral bet: eagerly link/blast every
    /// deferred assertion (the exact work the deferral skipped at assert
    /// time), so the general path proceeds with the circuits it would have
    /// had without the deferral.  Called whenever the eager dispatch
    /// declines a goal — the only situation where the deferred circuits are
    /// still wanted.
    pub(super) fn bv_restore_deferred_circuits(&mut self, manager: &TermManager) {
        if self.bv_elim_deferred.is_empty() {
            return;
        }
        let deferred = std::mem::take(&mut self.bv_elim_deferred);
        for term in deferred {
            self.link_or_blast_bv_circuits_inner(term, manager);
        }
    }

    /// Whether to **defer** this assertion's eager circuit linking because
    /// the check-time elim-uncnstr pass is predicted to remove the
    /// assertion's expensive circuits outright (see the call site).
    ///
    /// Prediction, from one iterative walk of the assertion's DAG:
    ///
    /// * **Candidate**: some free variable's *total* occurrence count
    ///   across all assertions seen so far is exactly one, and its direct
    ///   parent application is one of the operators the elimination rules
    ///   handle (`bvadd`/`bvmul`/`bvudiv`/`bvand`/`bvor`/`bvnot`/
    ///   `concat`/`extract`/comparisons/`eq`/`ite`/Bool connectives …).
    /// * **Expensive**: the assertion contains a division/remainder at
    ///   width ≥ 64 or a non-constant multiply at width ≥ 64 — the node
    ///   kinds whose circuits dominate a wide blast.
    ///
    /// Deferral requires both.  A candidate alone is true of most ordinary
    /// files (some variable occurs once under an add); losing their eager
    /// blast is a measured negative (the stage-4 study), so the deferral
    /// stays off everything whose blast is cheap.  When the prediction is
    /// wrong at check time (a later assertion re-used the candidate
    /// variable), the elimination recount finds nothing and the general
    /// path links the deferred atoms lazily — slower than eager, never
    /// wrong.
    ///
    /// The occurrence counts in [`Solver::bv_elim_var_occurrences`] are
    /// updated on *every* call (deferred or not), so later assertions
    /// invalidate stale candidates.  They are a routing hint only and are
    /// not trailed on `push`/`pop`: a stale high count can only *disable*
    /// the deferral (keeping the default eager blast), never enable it
    /// spuriously across a scope boundary.
    pub(super) fn bv_elim_defer_eager_blast(
        &mut self,
        term: TermId,
        manager: &TermManager,
    ) -> bool {
        /// Width at which a division/remainder/non-constant multiply makes
        /// the blast expensive enough to be worth deferring.
        const EXPENSIVE_WIDTH: u32 = 64;

        let mut expensive = false;
        let mut candidate = false;
        let mut visited: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
        // (node, parent application kind) — the parent decides whether a
        // first-occurrence variable is an elimination candidate.
        let mut stack: Vec<(TermId, Option<&TermKind>)> = vec![(term, None)];
        while let Some((tid, parent)) = stack.pop() {
            let is_var = manager
                .get(tid)
                .is_some_and(|data| matches!(data.kind, TermKind::Var(_)));
            // Variables are counted on every pop (hash-consing: one pop per
            // occurrence site — see `collect_unconstrained`); compound terms
            // are walked once.
            if is_var {
                let count = self.bv_elim_var_occurrences.entry(tid).or_insert(0);
                *count += 1;
                if *count == 1 && parent.is_some_and(Self::parent_is_elim_eligible) {
                    candidate = true;
                }
                continue;
            }
            if !visited.insert(tid) {
                continue;
            }
            let Some(data) = manager.get(tid) else {
                continue;
            };
            let kind = &data.kind;
            // Expensive-node detection (width from the node's own sort).
            let width = manager
                .sorts
                .get(data.sort)
                .and_then(|s| s.bitvec_width())
                .unwrap_or(0);
            match kind {
                TermKind::BvUdiv(_, _)
                | TermKind::BvSdiv(_, _)
                | TermKind::BvUrem(_, _)
                | TermKind::BvSrem(_, _) => {
                    if width >= EXPENSIVE_WIDTH {
                        expensive = true;
                    }
                }
                TermKind::BvMul(a, b) if width >= EXPENSIVE_WIDTH => {
                    let const_a = manager
                        .get(*a)
                        .is_some_and(|t| matches!(t.kind, TermKind::BitVecConst { .. }));
                    let const_b = manager
                        .get(*b)
                        .is_some_and(|t| matches!(t.kind, TermKind::BitVecConst { .. }));
                    if !const_a && !const_b {
                        expensive = true;
                    }
                }
                _ => {}
            }
            let parent_ref: Option<&TermKind> = Some(kind);
            for child in get_children(kind).into_iter().rev() {
                stack.push((child, parent_ref));
            }
        }
        expensive && candidate
    }

    /// Whether `parent` is an operator the elim-uncnstr rules can rewrite
    /// when an unconstrained variable is its direct operand
    /// (see `bv_elim_uncnstr::try_elim` for the rule table).
    fn parent_is_elim_eligible(parent: &TermKind) -> bool {
        matches!(
            parent,
            TermKind::Eq(_, _)
                | TermKind::Ite(_, _, _)
                | TermKind::Not(_)
                | TermKind::And(_)
                | TermKind::Or(_)
                | TermKind::BvAdd(_, _)
                | TermKind::BvSub(_, _)
                | TermKind::BvMul(_, _)
                | TermKind::BvUdiv(_, _)
                | TermKind::BvSdiv(_, _)
                | TermKind::BvAnd(_, _)
                | TermKind::BvOr(_, _)
                | TermKind::BvXor(_, _)
                | TermKind::BvNot(_)
                | TermKind::BvConcat(_, _)
                | TermKind::BvExtract { .. }
                | TermKind::BvUle(_, _)
                | TermKind::BvSle(_, _)
        )
    }

    /// Link the late-minted (unlinked) BV atoms recorded by the theory
    /// manager, at a round boundary where the main core is reachable.
    ///
    /// Returns the number of atoms that now carry a circuit.  Atoms whose
    /// circuit still cannot be built are *not* re-queued (the builder is
    /// deterministic – retrying the same shape would loop forever); the
    /// caller's honesty gate decides what an unlinkable atom means for the
    /// verdict.
    pub(super) fn link_pending_bv_atoms(&mut self, manager: &TermManager) -> usize {
        if !self.bv_unified {
            return 0;
        }
        let pending = self.bv.take_pending_unlinked_atoms();
        if pending.is_empty() {
            return 0;
        }
        let mut linked = 0usize;
        let mut bv_sorted: Vec<TermId> = Vec::new();
        let mut bv_atoms: Vec<BvAtomToLink> = Vec::new();
        for term in pending {
            let Some(term_data) = manager.get(term) else {
                continue;
            };
            match &term_data.kind {
                TermKind::Eq(lhs, rhs)
                | TermKind::BvUlt(lhs, rhs)
                | TermKind::BvUle(lhs, rhs)
                | TermKind::BvSlt(lhs, rhs)
                | TermKind::BvSle(lhs, rhs) => {
                    bv_atoms.push(BvAtomToLink { term });
                    bv_sorted.push(*lhs);
                    bv_sorted.push(*rhs);
                }
                _ => {}
            }
        }
        let term_to_var = &self.term_to_var;
        self.bv.build_with(&mut self.sat, |bv| {
            let mut encoded: FxHashSet<TermId> = FxHashSet::default();
            for &t in &bv_sorted {
                let width = manager
                    .get(t)
                    .and_then(|td| manager.sorts.get(td.sort))
                    .and_then(|s| s.bitvec_width());
                let Some(width) = width else { continue };
                if !encode_bv_term_recursive(bv, t, manager, &mut encoded) {
                    bv.new_bv(t, width);
                }
            }
            for atom in &bv_atoms {
                if let Some(circuit_var) = bv.encode_bool_node(atom.term, manager) {
                    if let Some(&main_var) = term_to_var.get(&atom.term) {
                        bv.link_bool_vars(main_var, circuit_var);
                    }
                    bv.note_unified_atom(atom.term);
                    linked += 1;
                }
            }
        });
        linked
    }

    /// Collect the BV-sorted sub-terms and Bool-sorted BV atoms under `root`.
    ///
    /// Returns `false` when the walk hits a generation-breaking shape
    /// (quantifier, array op, `Apply` with a bit-vector result) or the
    /// sub-term budget; the caller then ends the generation, which parks the
    /// whole assertion set on the lazy path.
    fn collect_unified_bv_terms(
        &mut self,
        root: TermId,
        manager: &TermManager,
        bv_sorted: &mut Vec<TermId>,
        bv_atoms: &mut Vec<BvAtomToLink>,
        bool_leaves: &mut Vec<TermId>,
    ) -> bool {
        let bool_sort = manager.sorts.bool_sort;
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut stack: Vec<TermId> = vec![root];
        while let Some(tid) = stack.pop() {
            if !visited.insert(tid) {
                continue;
            }
            if visited.len() > UNIFIED_LINK_BUDGET {
                return false;
            }
            let Some(term) = manager.get(tid) else {
                continue;
            };
            let is_bv_sort = manager.sorts.get(term.sort).is_some_and(|s| s.is_bitvec());
            match &term.kind {
                TermKind::Forall { .. } | TermKind::Exists { .. } => {
                    // Quantifiers mint fresh atoms at instantiation time,
                    // mid-search, where no build window can reach.  (The
                    // `has_quantifiers` flag covers the common case; this is
                    // the belt-and-braces structural check.)
                    return false;
                }
                TermKind::Select(_, _) | TermKind::Store(_, _, _) => {
                    // Array axiom rounds mint fresh BV atoms over selects;
                    // same mid-search problem as quantifiers.
                    return false;
                }
                TermKind::Apply { .. } if is_bv_sort => {
                    // Congruence merges of BV-sorted applications have no
                    // clause-level equivalent (see the module docs); make the
                    // sighting sticky so later assertions do not re-enter a
                    // doomed generation.
                    self.has_bv_result_uf = true;
                    return false;
                }
                TermKind::Eq(lhs, _) if term.sort == bool_sort => {
                    let lhs_bv = manager
                        .get(*lhs)
                        .is_some_and(|t| manager.sorts.get(t.sort).is_some_and(|s| s.is_bitvec()));
                    if lhs_bv {
                        bv_atoms.push(BvAtomToLink { term: tid });
                    }
                }
                TermKind::BvUlt(_, _)
                | TermKind::BvUle(_, _)
                | TermKind::BvSlt(_, _)
                | TermKind::BvSle(_, _) => {
                    bv_atoms.push(BvAtomToLink { term: tid });
                }
                _ => {}
            }
            if is_bv_sort {
                bv_sorted.push(tid);
            }
            // Bool-sorted free variables matter as `ite` selectors: the
            // circuit builder mints its own var for such a leaf, and the
            // outer search's assignment only reaches the mux if that var
            // is tied to the leaf's main-core var (the unified analogue of
            // the lazy path's `assert_bool_value` echo).  The tie is made
            // only when a circuit var already exists (a selector no later
            // assertion ever uses keeps its fresh var – free, exactly as
            // the lazy path would leave it), so no var is ever minted here.
            if term.sort == bool_sort && matches!(term.kind, TermKind::Var(_)) {
                bool_leaves.push(tid);
            }
            // Descend: the walk must see every sub-term (children of every
            // kind, including the atoms' operands).
            for child in get_children(&term.kind) {
                stack.push(child);
            }
        }
        true
    }

    /// Sweep the constraint registry for BV-sorted-operand atoms that carry
    /// no unified circuit yet.  This is the channel through which the
    /// pairwise atoms of a large `distinct` (minted by the `Distinct` encode
    /// arm, not present as sub-terms of the asserted formula) get linked.
    fn collect_unified_constraint_atoms(
        &self,
        manager: &TermManager,
        bv_sorted: &mut Vec<TermId>,
        bv_atoms: &mut Vec<BvAtomToLink>,
    ) {
        let is_bv = |t: TermId| {
            manager
                .get(t)
                .and_then(|td| manager.sorts.get(td.sort))
                .is_some_and(|s| s.is_bitvec())
        };
        for (&var, constraint) in self.var_to_constraint.iter() {
            let (lhs, rhs) = match constraint {
                Constraint::Eq(a, b) | Constraint::Diseq(a, b) => (*a, *b),
                Constraint::Lt(a, b)
                | Constraint::Le(a, b)
                | Constraint::Gt(a, b)
                | Constraint::Ge(a, b) => (*a, *b),
                Constraint::BoolApp(_) => continue,
            };
            if !is_bv(lhs) || !is_bv(rhs) {
                continue;
            }
            // The atom term is whatever term the var was created for; only
            // Eq/comparison shapes are linkable through `encode_bool_node`.
            let Some(&term) = self.var_to_term.get(var.index()) else {
                continue;
            };
            let Some(term_data) = manager.get(term) else {
                continue;
            };
            let atom = match &term_data.kind {
                TermKind::Eq(..)
                | TermKind::BvUlt(..)
                | TermKind::BvUle(..)
                | TermKind::BvSlt(..)
                | TermKind::BvSle(..) => BvAtomToLink { term },
                _ => continue,
            };
            if self.bv.is_unified_atom(term) || bv_atoms.iter().any(|a| a.term == term) {
                continue;
            }
            bv_atoms.push(atom);
            bv_sorted.push(lhs);
            bv_sorted.push(rhs);
        }
    }

    /// Allocate a free bit-vector for `term` in whichever instance the
    /// current generation builds circuits into.
    ///
    /// The encode-time theory-variable walk creates free vectors for BV
    /// leaves; during a unified generation those vars must come from the
    /// main core or the leaf would be unassignable by the search that
    /// constrains it.
    pub(super) fn bv_new_free_vector(&mut self, term: TermId, width: u32) {
        if self.bv_unified {
            self.bv.build_with(&mut self.sat, |bv| {
                bv.new_bv(term, width);
            });
        } else {
            self.bv.new_bv(term, width);
        }
    }

    /// Whether the order encoding may replace pairwise for spine-asserted
    /// large `distinct` over BitVec (`NIXIE_BV_DISTINCT_ORDER=0` disables;
    /// default on).
    pub(super) fn bv_distinct_order_enabled() -> bool {
        match std::env::var("NIXIE_BV_DISTINCT_ORDER") {
            Ok(v) => !(v == "0" || v.is_empty()),
            Err(_) => true,
        }
    }

    /// Eligibility of a `distinct` term for the order-encoding handoff:
    /// arity above the pairwise threshold, every argument a bit-vector of
    /// one width, and the cheap unified-generation preconditions hold (the
    /// full window decision happens later; a spec whose generation never
    /// engages falls back to pairwise at `check`).
    pub(super) fn order_distinct_eligible(&self, kind: &TermKind, manager: &TermManager) -> bool {
        let TermKind::Distinct(args) = kind else {
            return false;
        };
        if args.len() <= Self::DISTINCT_PAIRWISE_MAX_ARGS
            || !Self::bv_distinct_order_enabled()
            || !Self::bv_unify_enabled()
        {
            return false;
        }
        if !(self.context_stack.is_empty()
            && !self.has_quantifiers
            && !self.has_array_ops
            && self.array_select_terms.is_empty()
            && self.array_store_terms.is_empty()
            && !self.has_bv_result_uf
            && self.proof.is_none()
            && self.config.certification_mode == CertificationMode::Uncertified
            && (Self::bv_dispatch_unified() || !self.all_assertions_bv_fragment))
        {
            return false;
        }
        let Some(w) = manager
            .get(args[0])
            .and_then(|t| manager.sorts.get(t.sort))
            .and_then(|s| s.bitvec_width())
        else {
            return false;
        };
        // The pigeonhole short-circuit upstream already refuted arities
        // over the domain size; the network additionally needs the identity
        // arrangement to fit (`n2 <= 2^w`), which the same bound grants.
        if w < 63 && args.len() > (1usize << w) {
            return false;
        }
        args.iter().all(|&a| {
            manager.get(a).is_some_and(|t| {
                // Ground-constant arguments pin their wire's bits outright,
                // so the identity-arrangement guidance (which assumes every
                // wire free) misleads the descent: measured as timeouts on
                // constant-mixed shapes that pairwise solves easily.  Those
                // inputs keep the pairwise row.
                !matches!(t.kind, TermKind::BitVecConst { .. })
                    && manager.sorts.get(t.sort).and_then(|s| s.bitvec_width()) == Some(w)
            })
        })
    }

    /// Encode a spine-asserted `distinct` via the order-encoding handoff:
    /// allocate (or reuse) the term's var, memoise, record the spec with
    /// minted pads.  The caller emits the unit that pins the term true.
    pub(super) fn encode_order_distinct_fact(
        &mut self,
        term: TermId,
        kind: &TermKind,
        manager: &mut TermManager,
    ) -> Lit {
        let TermKind::Distinct(args) = kind else {
            unreachable!("caller checked the kind");
        };
        let result_var = self.get_or_create_var(term);
        self.memoize_encoding(term, Lit::pos(result_var), Polarity::Positive);
        let width = manager
            .get(args[0])
            .and_then(|t| manager.sorts.get(t.sort))
            .and_then(|s| s.bitvec_width())
            .unwrap_or(1);
        let n2 = args.len().next_power_of_two();
        let sort = manager
            .get(args[0])
            .map(|t| t.sort)
            .unwrap_or_else(|| manager.sorts.bitvec(width));
        let mut wires: Vec<TermId> = args.to_vec();
        for i in args.len()..n2 {
            let name = format!("__nixie_order_pad_{}_{}", self.bv_order_specs.len(), i);
            wires.push(manager.mk_var(&name, sort));
        }
        self.bv_order_specs.push(BvOrderSpec {
            term,
            var: result_var,
            wires,
            width,
        });
        Lit::pos(result_var)
    }

    /// Build every pending order-encoding spec's bitonic network into the
    /// main core (inside the link pass's window); built specs move to
    /// `bv_order_built`, refused ones stay pending for the pairwise
    /// fallback at `check`.
    pub(super) fn build_order_specs_in_window(&mut self, manager: &TermManager) {
        if self.bv_order_specs.is_empty() {
            return;
        }
        let specs = std::mem::take(&mut self.bv_order_specs);
        let mut built: Vec<BvOrderSpec> = Vec::new();
        self.bv.build_with(&mut self.sat, |bv| {
            let mut encoded: FxHashSet<TermId> = FxHashSet::default();
            for spec in &specs {
                let mut inputs: Vec<smallvec::SmallVec<[nixie_sat::Var; 32]>> = Vec::new();
                for &wire in &spec.wires {
                    if !encode_bv_term_recursive(bv, wire, manager, &mut encoded) {
                        bv.new_bv(wire, spec.width);
                    }
                    match bv.bv_bits(wire) {
                        Some(bits) => inputs.push(bits),
                        None => break,
                    }
                }
                if inputs.len() == spec.wires.len()
                    && bv.encode_distinct_order_network(spec.var, &inputs)
                {
                    built.push(spec.clone());
                }
            }
        });
        let built_set: FxHashSet<nixie_sat::Var> = built.iter().map(|s| s.var).collect();
        self.bv_order_built.retain(|s| !built_set.contains(&s.var));
        self.bv_order_built.extend(built);
        self.bv_order_specs = specs
            .into_iter()
            .filter(|s| !built_set.contains(&s.var))
            .collect();
    }

    /// Materialise the pairwise encoding for every spec still pending at
    /// `check` entry (the generation never engaged, died, or the builder
    /// refused the shape), and add the equality guards for built specs.
    ///
    /// The pairwise fallback is the historical encoding for the same term,
    /// emitted at base scope; the unit on the result var is already on the
    /// trail from the assertion.  Speculative pad wires carry no
    /// constraints and are ignored.  Capped: a spec whose pair count
    /// exceeds the cap is left unencoded (the distinct floats; the model
    /// gate turns a would-be `Sat` into `Unknown`) rather than minting
    /// millions of atoms at check time – those arities time out under
    /// pairwise anyway.
    pub(super) fn materialise_pending_order_specs(&mut self, manager: &mut TermManager) {
        self.add_order_spec_eq_guards();
        const MAX_PAIRS: usize = 200_000;
        let specs = std::mem::take(&mut self.bv_order_specs);
        for spec in specs {
            // The pairwise atoms are over the *arguments*; recover them
            // from the term so pads are excluded (cloned out so the
            // `&mut TermManager` borrow is free for `mk_eq`).
            let args: Vec<TermId> = {
                let Some(td) = manager.get(spec.term) else {
                    continue;
                };
                let TermKind::Distinct(args) = &td.kind else {
                    continue;
                };
                args.to_vec()
            };
            if args.len() * args.len().saturating_sub(1) / 2 > MAX_PAIRS {
                continue;
            }
            let result = Lit::pos(spec.var);
            let mut diseq_lits: Vec<Lit> = Vec::new();
            for i in 0..args.len() {
                for j in (i + 1)..args.len() {
                    let eq = manager.mk_eq(args[i], args[j]);
                    diseq_lits.push(self.encode_depth(eq, manager, 0).negate());
                }
            }
            for &diseq in &diseq_lits {
                self.sat.add_clause([result.negate(), diseq]);
            }
            let mut clause: Vec<Lit> = diseq_lits.iter().map(|l| l.negate()).collect();
            clause.push(result);
            self.sat.add_clause(clause);
        }
    }

    /// For every built order-encoding spec, emit the valid guard clause
    /// `distinct -> ~(x_i = x_j)` for each argument pair that already has
    /// an equality atom in the main core.
    ///
    /// The network refutes duplicates only through the full sort (hard for
    /// resolution: measured 4M conflicts at n=16), while a single asserted
    /// `(= x_i x_j)` against its guard clause conflicts at once –
    /// pairwise's instant refutation, paid only for the pairs the formula
    /// actually equates (O(#eq atoms), typically a handful).  Sound
    /// unconditionally: `distinct` implies every pair differs, so
    /// `¬R ∨ ¬E` is valid for any pair, atom or not.
    fn add_order_spec_eq_guards(&mut self) {
        if self.bv_order_built.is_empty() || self.var_to_constraint.is_empty() {
            return;
        }
        let entries: Vec<(nixie_sat::Var, TermId, TermId)> = self
            .var_to_constraint
            .iter()
            .filter_map(|(&v, c)| match c {
                Constraint::Eq(a, b) => Some((v, *a, *b)),
                _ => None,
            })
            .collect();
        if entries.is_empty() {
            return;
        }
        for spec in &self.bv_order_built {
            for &(eq_var, a, b) in &entries {
                if spec.wires.contains(&a)
                    && spec.wires.contains(&b)
                    && self.bv_order_guarded.insert((spec.term, eq_var))
                {
                    self.sat.add_clause([Lit::neg(spec.var), Lit::neg(eq_var)]);
                }
            }
        }
    }

    /// End the unified generation: wipe the BV solver's var-space tables and
    /// drop the solver-side flag.  Safe at any point – already-added circuits
    /// are definitional clauses that stay sound in the main core.
    pub(super) fn end_bv_unified_generation(&mut self) {
        if self.bv_unified {
            self.bv_unified = false;
            self.bv.exit_unified();
        }
    }

    /// Debug-build model-validity net for a unified generation (the analogue
    /// of the lazy path's `debug_verify_bv_circuits` in `bv_run_check`):
    /// every linked atom's operands must reproduce their own operation
    /// concretely on the adopted main-core model.  Release builds compile this
    /// away entirely.
    #[cfg(debug_assertions)]
    pub(super) fn debug_verify_unified_circuits(&self, manager: &TermManager) {
        use super::theory_bv_encode::debug_verify_bv_circuits;
        if !self.bv_unified {
            return;
        }
        // Stand-down gate: destructive preprocessing (ELS substitution, BVE)
        // eliminates variables and *resolves their defining clauses away*.
        // `save_model` reconstructs values that satisfy the rewritten
        // formula, and those values need not satisfy the original circuit
        // clauses (they were deleted, not violated) — so comparing raw
        // circuit-var reads against reference semantics is a category
        // error once any elimination ran.  This is the root cause of the
        // false positives recorded in the study's appendix: the
        // mismatching `bvand` bit had *zero live clauses* precisely
        // because BVE had eliminated it.
        if self.sat.stats().substitutions > 0 || self.sat.stats().bve_eliminated > 0 {
            #[cfg(feature = "std")]
            eprintln!(
                "[bv-net] skipping: destructive preprocessing ran ({} substitutions, {} BVE) — raw circuit reads are not model-truthful",
                self.sat.stats().substitutions,
                self.sat.stats().bve_eliminated
            );
            return;
        }
        let mut net_failed: Vec<(nixie_core::ast::TermId, String)> = Vec::new();
        for &atom in self.bv.unified_atoms() {
            if let Some(term) = manager.get(atom) {
                match &term.kind {
                    TermKind::Eq(l, r)
                    | TermKind::BvUlt(l, r)
                    | TermKind::BvUle(l, r)
                    | TermKind::BvSlt(l, r)
                    | TermKind::BvSle(l, r) => {
                        debug_verify_bv_circuits(&self.bv, *l, manager);
                        debug_verify_bv_circuits(&self.bv, *r, manager);
                    }
                    _ => {}
                }
            }
        }
        #[cfg(feature = "std")]
        if net_failed.is_empty() {
            use super::theory_bv_encode::NET_MISMATCH;
            NET_MISMATCH.with(|m| net_failed.extend(std::mem::take(&mut *m.borrow_mut())));
        }
        if !net_failed.is_empty() {
            // Dump first, fail second (see the net's comment).
            for (t, why) in &net_failed {
                if std::env::var("NIXIE_NET_DUMP_CLAUSES").is_ok()
                    && let Some(bits) = self.bv.debug_bits(*t).map(<[nixie_sat::Var]>::to_vec)
                {
                    for v in bits {
                        let clauses = self.sat.debug_clauses_containing(v);
                        eprintln!(
                            "[net-dump] {t:?} {why}: bit var {} watched by {} clauses",
                            v.index(),
                            clauses.len()
                        );
                        for c in clauses.iter().take(4) {
                            eprintln!(
                                "[net-dump]   {:?}",
                                c.iter().map(|l| l.to_dimacs()).collect::<Vec<_>>()
                            );
                        }
                    }
                }
            }
            debug_assert!(
                net_failed.is_empty(),
                "bit-blasted BV circuits disagree with reference semantics: {net_failed:?}"
            );
        }
    }
}
