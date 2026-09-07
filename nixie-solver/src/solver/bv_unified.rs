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

impl Solver {
    /// Whether unified bit-blasting is enabled (`NIXIE_BV_UNIFIED=0` disables;
    /// default on for eligible generations).
    pub(super) fn bv_unify_enabled() -> bool {
        match std::env::var("NIXIE_BV_UNIFIED") {
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
            // unification would blast every file twice).
            && !self.all_assertions_bv_fragment
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
        if !self.collect_unified_bv_terms(root, manager, &mut bv_sorted, &mut bv_atoms) {
            self.end_bv_unified_generation();
            return;
        }
        self.collect_unified_constraint_atoms(manager, &mut bv_sorted, &mut bv_atoms);
        if bv_atoms.is_empty() && bv_sorted.is_empty() {
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
        });
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
    }
}
