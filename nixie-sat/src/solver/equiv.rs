//! Equivalent-literal substitution via SCC on the binary implication graph.
//!
//! Binary clauses `(a ∨ b)` entail `¬a → b` and `¬b → a`. The implication
//! graph's strongly-connected components are equivalence classes: every literal
//! in an SCC implies every other, so they share a truth value in every model.
//! Rewriting every clause to use one representative per class shrinks the
//! formula (non-representative variables vanish) and is sound: a model of the
//! rewritten formula extends to the original by giving each eliminated
//! variable its representative's value.
//!
//! This is the pass that collapses binary-heavy multiplier / carry-chain
//! circuits (e.g. `longmult15`, 67% binary, ~2200/7800 vars in non-trivial
//! SCCs). One-shot, pre-search, decision level 0, base assertion scope. It
//! rebuilds the watch lists and binary graph from the rewritten clauses and
//! re-propagates level-0 units (including newly exposed ones).

use super::*;
use crate::literal::LBool;
use smallvec::SmallVec;

/// Public re-export target for `watched.rs`'s index-maintenance wiring
/// (the surgery experiment needs the position index maintained).
pub(crate) fn equiv_surgery_enabled() -> bool {
    els_surgery_enabled()
}

/// `NIXIE_ELS_CSR_SURGERY=1` (slice-5 experiment, developed inside the
/// shadow): re-point the CSR shadow's watchers surgically at each ELS
/// rewrite (retire/shrink) instead of letting the rebuild replace them —
/// while the `Vec` side still rebuilds wholesale.  The rebuild's multiset
/// oracle (`csr_multiset_compare`) then verifies the surgery produced
/// exactly the entry SET the rebuild would have (order is allowed to
/// differ: a production surgery is a screen-gated heuristic change, and
/// the order-sensitive drift comparison resumes only after the layout is
/// re-adopted).  Requires `NIXIE_CSR_SHADOW=1`.
/// Whether the production surgery skip is armed (NIXIE_SURGERY_PROD=1):
/// rebuild-time audit-gated replacement of the watch-half rebuild by the
/// window's surgical updates.
pub(super) fn surgery_prod_enabled() -> bool {
    #[cfg(feature = "std")]
    {
        use std::sync::OnceLock;
        static FLAG: OnceLock<bool> = OnceLock::new();
        *FLAG.get_or_init(|| {
            std::env::var("NIXIE_SURGERY_PROD")
                .is_ok_and(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        })
    }
    #[cfg(not(feature = "std"))]
    {
        false
    }
}

pub(super) fn els_surgery_enabled() -> bool {
    #[cfg(feature = "std")]
    {
        use std::sync::OnceLock;
        static FLAG: OnceLock<bool> = OnceLock::new();
        *FLAG.get_or_init(|| {
            std::env::var("NIXIE_ELS_CSR_SURGERY")
                .is_ok_and(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        })
    }
    #[cfg(not(feature = "std"))]
    {
        false
    }
}

impl Solver {
    fn els_csr_surgery_shrink(
        &mut self,
        cid: ClauseId,
        old: Option<(Lit, Lit, crate::memory::ClauseRef)>,
    ) {
        let Some((a, b, r)) = old else {
            return;
        };
        let Some(c) = self.clauses.get(cid).filter(|c| !c.deleted) else {
            return;
        };
        if c.lits.len() >= 3 && (c.lits[0], c.lits[1]) == (a, b) {
            return; // watched pair unchanged by the rewrite
        }
        let _ = (a, b);
        if let Some(pos) = self.watches.csr_positions_of(r) {
            self.csr_surgery_pending.push((r, pos));
            self.csr_surgery_ops += 1;
            self.csr_surgery_fired = true;
        }
        if c.lits.len() >= 3 {
            let (na, nb) = (c.lits[0], c.lits[1]);
            // Deferred: applied after the removal flush (a re-point onto a
            // literal the clause already watches must survive the batch).
            self.csr_surgery_pending_adds
                .push((na.negate(), Watcher::new(cid, r, nb)));
            self.csr_surgery_pending_adds
                .push((nb.negate(), Watcher::new(cid, r, na)));
            self.csr_surgery_ops += 2;
        }
    }

    /// Apply the window's collected removals batched by literal (the
    /// production surgery shape), THEN the deferred adds — order is
    /// load-bearing (see the pending-adds field).
    fn flush_csr_surgery(&mut self) {
        if !self.csr_surgery_pending.is_empty() {
            let pending = std::mem::take(&mut self.csr_surgery_pending);
            self.watches.csr_surgery_flush(&pending);
        }
        if !self.csr_surgery_pending_adds.is_empty() {
            let adds = std::mem::take(&mut self.csr_surgery_pending_adds);
            for (lit, w) in adds {
                self.watches.csr_surgery_add(lit, w);
            }
        }
    }
}

/// Outcome of one substitution pass.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum SubstOutcome {
    /// Completed; formula still alive.
    Ok,
    /// Substitution proved the formula unsatisfiable (empty clause, conflicting
    /// unit, or an SCC containing both polarities of one variable).
    Unsat,
}

/// Reused ELS/Tarjan scratch (see `Solver::equiv_scratch`).
#[derive(Default, Debug)]
pub(crate) struct EquivScratch {
    /// `sub[code(l)]` = representative literal for `l`.
    pub(crate) sub: Vec<Lit>,
    /// Tarjan discovery index (valid only when `epoch[code] == stamp`).
    pub(crate) index: Vec<i64>,
    /// Tarjan low-link (valid only for visited nodes).
    pub(crate) lowlink: Vec<usize>,
    /// On-SCC-stack flags (balanced set/reset within a round).
    pub(crate) on_stack: Vec<bool>,
    /// Epoch stamp: `index`/`lowlink` entries carry values from their last
    /// visited round; `epoch[code] == stamp` marks "visited this round".
    pub(crate) epoch: Vec<u32>,
    pub(crate) stack: Vec<usize>,
    pub(crate) work: Vec<(usize, usize)>,
}

impl Solver {
    /// Detect equivalent literals (SCCs of the binary implication graph) and
    /// rewrite every clause through the representative map.
    ///
    /// Guards: decision level 0, base assertion scope, no DRAT writer.
    pub(super) fn substitute_equivalent_literals(&mut self) -> SubstOutcome {
        // One-shot for the pre-search call site (see `Solver::solve`); the
        // mid-search inprocessing schedule calls
        // [`Self::substitute_equivalent_literals_round`], which deliberately
        // re-runs: the substitution map composes across rounds (see the
        // `equiv_subst_inited` logic below).
        if self.did_equiv_subst {
            return SubstOutcome::Ok;
        }
        self.substitute_equivalent_literals_round()
    }

    /// One ELS round without the one-shot latch (mid-search re-arms keep all
    /// the other soundness gates: level 0, base scope, no proof tracing).
    pub(super) fn substitute_equivalent_literals_round(&mut self) -> SubstOutcome {
        if self.trail.decision_level() != 0
            || self.assertion_levels.len() > 1
            || self.proof.is_some()
        {
            return SubstOutcome::Ok;
        }

        let num_vars = self.num_vars;
        let num_lits = num_vars * 2;

        // Refresh the binary implication graph from current (incl. learned)
        // binary clauses so the SCC sees equivalences exposed during search –
        // essential for inprocessing re-runs. (On the first, pre-search call
        // the graph is already current; this is a cheap no-op there.)
        self.refresh_binary_graph();

        // Augment the binary implication graph with equivalences inferred from
        // congruent AND/XOR gates (multiplier / adder structure) before SCC, so
        // the closure below folds them in too.  Enabled under inprocessing as
        // well: the augmented edges are only consumed by the SCC below, and
        // **every** exit of this round now purges them via
        // `refresh_binary_graph` (the end-of-round purge existed before; the
        // early-out below used to skip it, which is why congruence was gated
        // off under inprocessing in 169217e – leaving unbacked edges in the
        // BIG through the search on the no-equivalence path).
        // Ternary×binary SSR cascade (kissat `extract_binaries`): derive the
        // resolvent binaries BEFORE gate detection so completed AND-gate
        // patterns (`o ↔ a ∧ b` needs `o→a`, `o→b`) enter the closure the
        // same round — on the bv_ILA class these few binaries unlock the
        // whole congruence cascade (study 2026-09-18-ssr-binaries).
        let mut big_augmented = false;
        if super::congruence::ssr_binaries_enabled() && self.destructive_preprocessing_safe() {
            let added = self.extract_binary_resolvents();
            #[cfg(feature = "std")]
            if added > 0 && super::learn::inproc_round_trace_enabled() {
                eprintln!("ssr_binaries: extracted {added} resolvent binaries");
            }
        }
        if self.config.enable_gate_congruence {
            self.augment_big_with_gate_congruence();
            big_augmented = true;
        }

        // ======== Iterative Tarjan over the binary implication graph. ========
        // Nodes are literal codes; successors of `lit` are the literals it
        // directly implies (binary_graph edges). Recursion would overflow on
        // deep implication chains (thousands deep on multiplier circuits).
        //
        // Scratch is solver-owned and reused across rounds (2026-09-17
        // amortization): `index` is epoch-stamped instead of refilled with
        // `-1`, because the per-round `vec![-1; 2·V]` / `vec![0; 2·V]` /
        // `vec![false; 2·V]` allocations were the measured
        // `extend_with`+`memset` hotspot (~2.5 % of whole-run wall on
        // b21-class instances).  Soundness of the no-fill scheme:
        // `on_stack` is balanced set/reset by construction (every push sets,
        // every SCC pop resets; the loops below read `on_stack[w]` /
        // `lowlink[w]` only for nodes whose epoch matches this round, and
        // both are written before their first read within a visit).
        let mut scratch = std::mem::take(&mut self.equiv_scratch);
        if scratch.sub.len() != num_lits {
            scratch.sub = (0..num_lits as u32).map(Lit::from_code).collect();
            scratch.index = vec![0; num_lits];
            scratch.lowlink = vec![0; num_lits];
            scratch.on_stack = vec![false; num_lits];
            scratch.epoch = vec![u32::MAX; num_lits];
        } else {
            for (c, l) in scratch.sub.iter_mut().enumerate() {
                *l = Lit::from_code(c as u32);
            }
        }
        // Epoch stamps: u32::MAX initial + wrapping round counter means a
        // fresh round's stamp never collides with an unused entry.
        let stamp = self.equiv_epoch;
        self.equiv_epoch = self.equiv_epoch.wrapping_add(1);
        let EquivScratch {
            sub,
            index,
            lowlink,
            on_stack,
            epoch,
            stack,
            work,
        } = &mut scratch;
        let mut index_counter: usize = 0;
        stack.clear();
        work.clear();

        for root in 0..num_lits {
            if epoch[root] == stamp {
                continue;
            }
            // Seed root.
            epoch[root] = stamp;
            index[root] = index_counter as i64;
            lowlink[root] = index_counter;
            index_counter += 1;
            stack.push(root);
            on_stack[root] = true;
            work.push((root, 0));

            while let Some(&(node, succ_i)) = work.last() {
                let succs = self.binary_graph.get(Lit::from_code(node as u32));
                if succ_i < succs.len() {
                    if let Some(entry) = work.last_mut() {
                        entry.1 = succ_i + 1;
                    }
                    let w = succs[succ_i].0.code() as usize;
                    if epoch[w] != stamp {
                        epoch[w] = stamp;
                        index[w] = index_counter as i64;
                        lowlink[w] = index_counter;
                        index_counter += 1;
                        stack.push(w);
                        on_stack[w] = true;
                        work.push((w, 0));
                    } else if on_stack[w] {
                        lowlink[node] = lowlink[node].min(index[w] as usize);
                    }
                } else {
                    work.pop();
                    if let Some(&(parent, _)) = work.last() {
                        lowlink[parent] = lowlink[parent].min(lowlink[node]);
                    }
                    if lowlink[node] == index[node] as usize {
                        // Pop the SCC rooted at `node` off `stack`.
                        let mut scc_start = stack.len();
                        loop {
                            scc_start -= 1;
                            let w = stack[scc_start];
                            on_stack[w] = false;
                            if w == node {
                                break;
                            }
                        }
                        // Actually remove the popped members: without this the
                        // `stack` Vec kept already-assigned nodes, and a later
                        // SCC's `stack[scc_start..]` slice re-included them –
                        // fabricating equivalences (and spurious pos(v)≡neg(v)
                        // contradictions) that proved satisfiable formulas UNSAT.
                        let scc_members = stack.split_off(scc_start);
                        // Freeze set: a class containing a frozen
                        // (theory-mapped) variable is left unfolded —
                        // folding would rewrite the frozen literal's
                        // clauses onto the representative and stop its
                        // atom from ever reaching the theory
                        // (`on_assignment` desync).
                        let class_has_frozen = scc_members
                            .iter()
                            .any(|&c| self.frozen_vars.contains(&Lit::from_code(c as u32).var()));
                        if scc_members.len() > 1
                            && !class_has_frozen
                            && let Some(&min_c) = scc_members.iter().min()
                        {
                            let rep = Lit::from_code(min_c as u32);
                            for &c in &scc_members {
                                sub[c] = rep;
                            }
                        }
                    }
                }
            }
        }

        // Tarjan phase complete: every `sub` write happened inside the SCC
        // pops above, and the rest of the round only READS the map — so
        // clone it out, return the scratch (all `&mut` borrows dead), and
        // continue with a plain local exactly like the pre-amortization
        // code.  The clone is one 2·V memcpy, the amortized equivalent of
        // the per-round identity fill it replaces.
        let sub: Vec<Lit> = scratch.sub.clone();
        self.equiv_scratch = scratch;
        let sub = &sub;

        // Contradiction check: pos(v) ≡ neg(v) (both resolve to the same rep)
        // means the formula entails both v and ¬v → UNSAT.
        for v in 0..num_vars {
            let pos = Lit::pos(Var::new(v as u32));
            if sub[pos.code() as usize] == sub[(pos.negate()).code() as usize] {
                self.trivially_unsat = true;
                return SubstOutcome::Unsat;
            }
        }

        // Early-out if nothing actually moved.  Even then, gate-congruence
        // augmentation (if it ran) must be rolled back: the augmented edges
        // are not backed by live clauses and would keep propagating through
        // the search (hanging-unit hazard – see the module comment on
        // `refresh_binary_graph`).
        if !(0..num_lits).any(|c| sub[c].code() as usize != c) {
            if big_augmented {
                self.refresh_binary_graph();
            }
            return SubstOutcome::Ok;
        }

        // ======== Rewrite every live clause through the map. ========
        // The surgery window: from here to the rebuild below nothing scans
        // (loop, bookkeeping, rebuild are scan-free), so the CSR-only
        // surgical edits cannot hit the dual-write mirror's precondition.
        self.els_surgery_window = els_surgery_enabled() && self.watches.csr_active();
        let live_ids: Vec<ClauseId> = self.clauses.iter_ids().collect();
        let mut new_units: SmallVec<[Lit; 64]> = SmallVec::new();
        let mut eliminated = 0usize;

        // Reusable per-clause buffers (perf, 2026-09-11): this loop is one
        // pass over every live clause per substitution round, and the
        // per-iteration `SmallVec` collect plus `Vec::with_capacity` were
        // two heap allocations per clause — on wide-uniform formulas
        // (si2-b03m: 600k clauses × width 20, the SmallVec also spills its
        // inline 8) that is >1 M malloc/free pairs per round and showed up
        // as the `_int_malloc`/`realloc`/`memmove` cluster under `perf
        // record`. Clear-and-refill keeps contents and processing order
        // bit-identical; only allocation identity changes.
        let mut mapped: SmallVec<[Lit; 8]> = SmallVec::new();
        let mut lits: Vec<Lit> = Vec::new();
        let mut seen: FxHashMap<Vec<Lit>, ClauseId> = FxHashMap::default();

        for cid in live_ids {
            // ELS-rewatching surgery hook (NIXIE_ELS_CSR_SURGERY=1): capture
            // the pre-rewrite watched pair so retire/shrink below can
            // re-point the CSR shadow's watchers surgically (slice-5
            // experiment; the Vec side is rebuilt wholesale as ground truth
            // and the rebuild's multiset oracle checks the equivalence).
            let surg_old = if self.els_surgery_window {
                match (
                    self.clauses
                        .get(cid)
                        .filter(|c| !c.deleted && c.lits.len() >= 3),
                    self.clauses.ref_of(cid),
                ) {
                    (Some(c), Some(r)) => Some((c.lits[0], c.lits[1], r)),
                    _ => None,
                }
            } else {
                None
            };
            // Rewrite semantics follow cadical `decompose.cpp` exactly:
            // evaluate every literal (and its representative) against the
            // level-0 trail while building the replacement clause –
            // * a literal (or its mapped representative) that is **true**
            //   satisfies the clause: the clause is retired outright (it
            //   constrains nothing further at this scope),
            // * a **false** literal is dropped from the replacement (a false
            //   disjunct contributes nothing; the level-0 unit that falsified
            //   it is permanent for this assertion scope).
            //
            // The value filtering is what makes the in-place rewrite + watch
            // rebuild sound: after it, every literal kept in a rewritten
            // clause is unassigned at level 0, so whichever two literals the
            // rebuild picks as watches are literals that have not yet fired –
            // their watch lists are still armed. Keeping a false literal (the
            // previous behavior) placed fresh watches on literals whose
            // falsification had *already happened* at level 0: those watch
            // lists are never visited again (a watch fires only when its
            // literal *becomes* false), so a clause that later became unit or
            // falsified hung silently until the full-assignment guard caught
            // it (reproduced: `constraints_17` under
            // `enable_equiv_substitution` returned Unknown via
            // `trail_falsifies_live_clause`; debug invariant:
            // `check_unit_propagation_complete` hanging-unit violations).
            mapped.clear();
            if let Some(c) = self.clauses.get(cid)
                && !c.deleted
            {
                mapped.extend(c.lits.iter().map(|&l| sub[l.code() as usize]));
            } else {
                continue;
            }
            if mapped.is_empty() {
                continue;
            }

            let mut satisfied = false;
            lits.clear();
            'lits: for &l in &mapped {
                match self.trail.lit_value(l) {
                    LBool::True => {
                        satisfied = true;
                        break 'lits;
                    }
                    LBool::False => continue,
                    LBool::Undef => lits.push(l),
                }
            }
            if satisfied {
                // retire_clause's central hook drops the shadow watchers.
                self.retire_clause(cid);
                continue;
            }

            // Sort + dedup + tautology detection. After sorting by code, the
            // two polarities of one variable are adjacent (pos(v)=2v, neg(v)=2v+1),
            // so a tautology is any adjacent pair sharing a variable.
            lits.sort_unstable_by_key(|l| l.code());
            lits.dedup_by_key(|l| l.code());
            let tautology = lits.windows(2).any(|w| w[0].var() == w[1].var());

            if tautology {
                self.retire_clause(cid);
                continue;
            }
            // Exact-duplicate retire — ONLY when the recorded owner is an
            // ORIGINAL clause (a learned owner can be purged later — the
            // doomed purge retires learned clauses mentioning eliminated
            // vars, correctly — and then the constraint is gone with no
            // obligation: retiring original (¬2990∨¬15955) in favor of the
            // learned twin 213141 was the b21/seed-1 false-sat's exact
            // mechanism).  An original meeting a learned owner takes the
            // ownership over; learned-vs-learned collisions leave both.
            match seen.get(&lits) {
                Some(&owner) => {
                    let owner_learned = self.clauses.get(owner).is_some_and(|c| c.learned);
                    let self_learned = self.clauses.get(cid).is_some_and(|c| c.learned);
                    if self_learned {
                        // learned never retires anything and never owns
                    } else if owner_learned {
                        seen.insert(lits.clone(), cid);
                    } else {
                        self.retire_clause(cid);
                    }
                }
                None => {
                    seen.insert(lits.clone(), cid);
                }
            }
            match lits.len() {
                0 => {
                    // Every literal of the clause is false at level 0 (after
                    // mapping through the equivalence classes): the clause is
                    // falsified by unconditional facts alone → UNSAT.
                    self.trivially_unsat = true;
                    return SubstOutcome::Unsat;
                }
                1 => {
                    new_units.push(lits[0]);
                    self.retire_clause(cid);
                }
                _ => {
                    self.clauses.shrink(cid, &lits);
                    // After the shrink: the helper reads the rewritten
                    // clause to decide the new watched pair.
                    self.els_csr_surgery_shrink(cid, surg_old);
                }
            }
        }

        // Batched surgical removals: one filtered pass per distinct literal
        // while still inside the scan-free window.
        self.flush_csr_surgery();
        self.els_surgery_window = false;
        // ======== Record model-reconstruction map + branching-skip flag. ========
        // `equiv_substitution[v]` is the CUMULATIVE representative literal for
        // `v` across all substitution rounds (identity `pos(v)` if never
        // eliminated). Each round COMPOSES this round's `sub` onto it – so an
        // inprocessing re-run that further folds a previous representative is
        // recorded correctly, instead of overwriting (and losing) the earlier
        // elimination. (Overwriting was the inprocessing soundness bug: a var
        // eliminated in round 1 became non-eliminated in round 2's map, got
        // re-branched, and took an unreconstructed value.)
        if !self.equiv_subst_inited {
            self.equiv_substitution.clear();
            self.equiv_substitution
                .extend((0..num_vars).map(|v| Lit::pos(Var::new(v as u32))));
            self.equiv_subst_inited = true;
        } else if self.equiv_substitution.len() < num_vars {
            // Variables created since the last round (incremental callers,
            // CDCL(T) refinement encoding new atoms) start at IDENTITY. A
            // uniform fill value here poisoned the grown tail: every new
            // variable became fake-eliminated into the fill's variable —
            // `var_eliminated` reported it folded (never branched),
            // `resolve_reintroduced_literal` rewrote later mentions of it
            // into that variable (corrupting the clause), and the compose
            // loop below pushed FABRICATED equivalence obligations onto the
            // extension stack, whose walk then toggled the variable to the
            // fill variable's value against live clauses (invalid `Sat`
            // witnesses; observed on Rodin/smt3878551918658299427).
            let old_len = self.equiv_substitution.len();
            self.equiv_substitution
                .resize(num_vars, Lit::pos(Var::new(0)));
            for v in old_len..num_vars {
                self.equiv_substitution[v] = Lit::pos(Var::new(v as u32));
            }
        }
        for v in 0..num_vars {
            let cur = self.equiv_substitution[v];
            let rep = sub[cur.code() as usize];
            self.equiv_substitution[v] = rep;
            if rep.var().index() != v {
                eliminated += 1;
                // Extension-stack witness clauses for the equivalence
                // `v ≡ rep` (both implications), so model reconstruction is
                // uniform with BVE: the backward walk in `save_model` repairs
                // a falsified implication by flipping `v`, exactly like an
                // eliminated pivot.  A separate representative-lookup pass
                // cannot express stack ORDER relative to BVE entries, and a
                // pre-defaulted unconstrained representative made such a
                // pass assign a variable against its own equivalence
                // (summle_X4053: `1268 ≡ ¬1267` with 1267 never branched
                // falsified `(1267 ∨ 1268)`).
                let var = Var::new(v as u32);
                let lit = Lit::pos(var);
                // (v ∨ ¬rep) with witness v
                self.ext_stack.push(lit.code());
                self.ext_stack.push(lit.code());
                self.ext_stack.push(rep.negate().code());
                self.ext_stack.push(u32::MAX);
                // (¬v ∨ rep) with witness ¬v
                self.ext_stack.push(lit.negate().code());
                self.ext_stack.push(lit.negate().code());
                self.ext_stack.push(rep.code());
                self.ext_stack.push(u32::MAX);
            }
        }

        // ======== Rebuild watch lists + binary implication graph. ========
        self.rebuild_watches_and_binary_graph();

        // ======== Assign the newly exposed level-0 units and re-propagate. ========
        for lit in new_units {
            match self.trail.lit_value(lit) {
                LBool::True => {}
                LBool::False => {
                    self.trivially_unsat = true;
                    return SubstOutcome::Unsat;
                }
                LBool::Undef => self.trail.assign_decision(lit),
            }
        }
        if self.propagate().is_some() {
            self.trivially_unsat = true;
            return SubstOutcome::Unsat;
        }

        self.stats.substitutions += eliminated as u64;
        // Purge the gate-congruence edges augment_big_with_gate_congruence
        // added to the binary implication graph: they served their purpose
        // (exposing equivalences for the SCC) and are not backed by live
        // clauses, so leaving them in the BIG through the search would let
        // an inprocessing clause deletion strand them -- stale edges that
        // produce hanging units (propagation fixpoint violations). That
        // purge, however, is already done: the mid-round
        // `rebuild_watches_and_binary_graph` reconstructs the BIG from the
        // live binary clauses (dropping the unbacked augmented edges), and
        // nothing between it and here changes the clause set — the units
        // loop only assigns trail literals and `propagate` derives
        // consequences without learning or deleting. The trailing rebuild
        // therefore reproduced an identical graph every round and is
        // skipped outright (one full clause-iteration pass per round; the
        // `big_augmented` flag stays for the early-exit paths above, which
        // genuinely bypass the mid-round rebuild).
        let _ = big_augmented;
        SubstOutcome::Ok
    }

    /// Whether `v` may be branched on. Every eliminated variable is
    /// unbranchable *except* one whose retired clauses were resurrected by
    /// re-introduction ([`Solver::void_elimination_promises`]): its
    /// constraints are live clauses again, so the search must be able to
    /// decide it — without this, a clause whose satisfaction needs a
    /// positive decision on such a variable (all its literals unassigned,
    /// no propagation possible) could never be satisfied and the model
    /// would default the variable to `false` in violation of it. The
    /// eliminated markers stay set, so the eliminator never re-eliminates
    /// the variable (and the extension-stack walk's per-var obligation
    /// skip in `save_model` remains exact).
    ///
    /// ELS-substituted variables are never re-introduced (their mentions
    /// are rewritten to the representative), so they remain unbranchable.
    #[inline]
    pub(super) fn branchable(&self, v: Var) -> bool {
        !self.var_eliminated(v) || self.ext_rementioned.contains(&v)
    }

    /// True if `v` was folded away by equivalent-literal substitution or
    /// BVE/elimination and must not be branched on. Cheap: empty maps mean no
    /// pass ran.
    #[inline]
    pub fn var_eliminated(&self, v: Var) -> bool {
        (self.equiv_substitution.len() > v.index() && self.equiv_substitution[v.index()].var() != v)
            || (self.bve_def.len() > v.index() && !self.bve_def[v.index()].is_empty())
            || (self.elim_var_flag.len() > v.index() && self.elim_var_flag[v.index()])
    }

    /// Rewrite a literal a later `add_clause`/assumption tries to reintroduce
    /// through the equivalent-literal-substitution map, so a variable ELS
    /// folded away is soundly replaced by its class representative (the
    /// equivalence was already proven) instead of being branched on as a free
    /// variable -- the gatekeeper fix for the SK-1 false-`sat` (a reintroduced
    /// ELS variable, no longer constrained by its equivalence, could be
    /// assigned freely and break the model). A literal whose variable was
    /// *not* ELS-substituted is returned unchanged. (BVE-eliminated variables
    /// have no sound on-demand rewrite here; main's BVE eliminates no
    /// variables under its sound literal-count bound, so that path is moot.)
    #[inline]
    pub(super) fn resolve_reintroduced_literal(&self, lit: Lit) -> Lit {
        let v = lit.var();
        if self.equiv_substitution.len() > v.index() {
            let rep = self.equiv_substitution[v.index()];
            if rep.var() != v {
                // `v` was folded into `rep.var()`; `lit`'s polarity carries
                // over (pos(v) == rep, neg(v) == neg(rep)).
                return if lit.is_pos() { rep } else { rep.negate() };
            }
        }
        lit
    }

    /// Rebuild the two-watched-literal structures and the binary implication
    /// graph from the current set of live (non-deleted) clauses. Used after any
    /// preprocessing pass that rewrites clause literals in place (equivalent-
    /// literal substitution, BVE): the old watches point at stale literals, so
    /// the whole structure is regenerated. Binary clauses also repopulate the
    /// binary implication graph.
    /// Rebuild ONLY the binary implication graph from current live binary
    /// clauses (original + learned). Used before re-running substitution during
    /// inprocessing so the SCC sees equivalences exposed by learned binaries.
    pub(super) fn refresh_binary_graph(&mut self) {
        // Two-phase CSR build: count every edge the refill will add, freeze
        // the exact-size layout, then fill. This replaces the per-literal
        // `Vec` refill whose doubling growth transiently doubled the BIG's
        // footprint on binary-dense instances (~250 MB cap vs ~165 MB
        // live on worker-class). Content and per-literal order are exactly
        // the old refill's: ids ascending, two edges per live binary.
        self.binary_graph.build_reset(self.num_vars);
        for cid in self.clauses.iter_ids() {
            if let Some(c) = self.clauses.get(cid)
                && !c.deleted
                && c.lits.len() == 2
            {
                let (a, b) = (c.lits[0], c.lits[1]);
                self.binary_graph.build_count(a.negate());
                self.binary_graph.build_count(b.negate());
            }
        }
        self.binary_graph.build_layout();
        for cid in self.clauses.iter_ids() {
            if let Some(c) = self.clauses.get(cid)
                && !c.deleted
                && c.lits.len() == 2
            {
                let (a, b) = (c.lits[0], c.lits[1]);
                self.binary_graph.build_edge(a.negate(), b, cid);
                self.binary_graph.build_edge(b.negate(), a, cid);
            }
        }
        // The CSR layout is exact by construction; this only drops the
        // flat buffer's `Vec` margin (trajectory-neutral).
        self.binary_graph.shrink();
    }

    pub(super) fn rebuild_watches_and_binary_graph(&mut self) {
        let num_vars = self.num_vars;
        // CSR dual-write drifted-state validation (slice 2,
        // `docs/studies/2026-09-13-csr-watches-kickoff.md`): before either
        // representation resets, the shadow — maintained since the previous
        // rebuild through every BCP scan (keep/remove/move) and every
        // cold-path mutation (attach, deletion, relocation, rollback) —
        // must equal the drifted `Vec` lists entry-for-entry, order
        // included.  This is the empirical order-isomorphism proof the
        // dual-write scan exists to produce.
        #[cfg(feature = "std")]
        if let Ok(prefix) = std::env::var("NIXIE_DUMP_BIG") {
            use std::fmt::Write as _;
            let mut out = String::new();
            let mut total = 0usize;
            for code in 0..self.num_vars * 2 {
                let (start, plen) = self.binary_graph.span_of(code);
                let primary = &self.binary_graph.edges[start..start + plen];
                let extra = &self.binary_graph.extra[code];
                if primary.is_empty() && extra.is_empty() {
                    continue;
                }
                total += primary.len() + extra.len();
                let _ = write!(out, "{code}:");
                for &(implied, _) in primary.iter().chain(extra.iter()) {
                    let _ = write!(out, " {}", implied.code());
                }
                let _ = writeln!(out);
            }
            let path = format!("{prefix}-{}.txt", self.stats.conflicts);
            let _ = std::fs::write(&path, out);
            eprintln!("[big-dump] {path}: {total} edges");
        }
        #[cfg(feature = "std")]
        if let Ok(prefix) = std::env::var("NIXIE_DUMP_WATCHES") {
            let path = format!("{prefix}-{}.txt", self.stats.conflicts);
            self.watches.dump_watches(num_vars, &path);
        }
        #[cfg(feature = "std")]
        if crate::watched::csr_shadow_enabled()
            && self.watches.csr_active()
            && !self.csr_surgery_fired
        {
            let (lits, entries, bad) = self.watches.csr_drifted_compare(num_vars);
            eprintln!(
                "[csr-shadow] drift@{}: lits={lits} entries={entries} mismatched={bad}",
                self.stats.conflicts
            );
        }
        // Detach the shadow for the duration of the rebuild: the fills below
        // reconstruct the `Vec` lists wholesale and the fresh layout adopted
        // at the end replaces the shadow's baseline (mirroring the fill's
        // `add`s would double-maintain into a state that is discarded).
        let mut drifted_shadow = self.watches.csr_take();
        #[cfg(feature = "std")]
        if crate::watched::csr_shadow_enabled()
            && let Some(dsh) = drifted_shadow.as_ref()
        {
            let vec_entries: usize = (0..num_vars * 2)
                .map(|code| self.watches.get(Lit::from_code(code as u32)).len())
                .sum();
            eprintln!(
                "[csr-shadow] entry@{}: csr_entries={} vec_entries={} index_refs={}",
                self.stats.conflicts,
                dsh.debug_total_entries(),
                vec_entries,
                dsh.debug_index_refs()
            );
        }
        // Reuse the existing outer allocation (2026-09-12): a fresh
        // `WatchLists::new` allocated `2·num_vars` empty `Vec` headers every
        // rebuild (si2-class: 6 ELS rounds x ~2.6 M headers zeroed plus
        // per-list regrowth during the fill), while the fill reconstructs
        // identical contents anyway. Clearing in place keeps every list's
        // capacity - same sequential clause-major pattern, zero allocation
        // churn, bit-identical contents (capacity is not semantic).
        if !crate::watched::csr_b_enabled() {
            self.watches.reset_lists_in_place(num_vars);
        }
        // Two-phase CSR build (count → layout → fill): the count pass must
        // apply exactly the filters the fill pass applies (nothing mutates
        // the clause database between the two, so the same live set is seen
        // twice). Replaces the per-literal `Vec` refill whose doubling
        // growth transiently doubled the BIG's footprint on binary-dense
        // instances (~250 MB cap vs ~165 MB live on worker-class).
        self.binary_graph.build_reset(num_vars);
        // Phantom tick-parity reset: the old scheme's rebuild re-created one
        // watch entry per live-binary direction; the refill below bumps one
        // phantom per direction in exactly the same places (see
        // `WatchLists`'s module note and
        // `studies/2026-09-big-authoritative-bcp.md`).
        self.watches.phantom_reset(num_vars * 2);
        // Iterate clause ids directly (no id-Vec collection) and read each
        // clause's literals IN THE ARENA (no per-clause SmallVec copy): only
        // the first two literals and the arena slot are needed, and all
        // touched state is split-borrowed from the destructured fields. The
        // previous shape collected every clause id into a fresh Vec and
        // copied every clause's literals – on a 10.3 M-clause instance that
        // was a ~40 MB Vec plus 10.3 M copies per rebuild, and the rebuild
        // itself measured ≈ 520 instructions per clause.
        {
            let Solver {
                clauses,
                watches,
                binary_graph,
                ..
            } = self;
            for cid in clauses.iter_ids() {
                let Some(c) = clauses.get(cid).filter(|c| !c.deleted) else {
                    continue;
                };
                if c.lits.len() == 2 {
                    let (a, b) = (c.lits[0], c.lits[1]);
                    binary_graph.build_count(a.negate());
                    binary_graph.build_count(b.negate());
                    // The phantom count is part of the tick-parity contract:
                    // one per direction, exactly where the edges land.
                    watches.phantom_bump(a.negate());
                    watches.phantom_bump(b.negate());
                }
            }
        }
        self.binary_graph.build_layout();
        {
            let Solver {
                clauses,
                watches,
                binary_graph,
                learned_clause_ids,
                ..
            } = self;
            for cid in clauses.iter_ids() {
                let Some(c) = clauses.get(cid).filter(|c| !c.deleted) else {
                    continue;
                };
                if c.lits.len() < 2 {
                    // Units are level-0 facts on the trail.
                    continue;
                }
                let Some(r) = clauses.ref_of(cid) else {
                    debug_assert!(
                        false,
                        "freshly added/known-live clause id without arena slot"
                    );
                    continue;
                };
                let (a, b) = (c.lits[0], c.lits[1]);
                if c.lits.len() == 2 {
                    // BIG-authoritative BCP (2026-09): a live binary registers
                    // ONLY in the binary implication graph (plus its phantom
                    // tick count) – never in the watch lists. The BIG scan in
                    // `propagate()` runs before the watch scan, so a watch entry
                    // for a binary could never reach its arena load.
                    binary_graph.build_edge(a.negate(), b, cid);
                    binary_graph.build_edge(b.negate(), a, cid);
                    continue;
                }
                // The shadow is detached for the whole rebuild (csr_take
                // above), so the fill uses the mirror-free push — the CSR
                // baseline is adopted wholesale from the fresh layout at
                // the end of this function.  Commit-B: the Vec side is
                // dead — only the CSR layout below is filled.
                if !crate::watched::csr_b_enabled() {
                    watches.push_only(a.negate(), Watcher::new(cid, r, b));
                    watches.push_only(b.negate(), Watcher::new(cid, r, a));
                }
            }
            learned_clause_ids.retain(|&cid| clauses.get(cid).is_some_and(|c| !c.deleted));
        }
        // The CSR layout is exact by construction; this only drops the flat
        // buffer's `Vec` margin. The watch lists above were rebuilt into
        // fresh `Vec`s, so their slack is already minimal.
        self.binary_graph.shrink();
        // CSR shadow validation (`NIXIE_CSR_SHADOW=1`): rebuild the watch
        // state independently as a CSR (count → layout → fill over the same
        // live long-clause set, in the same id order) and compare every
        // literal's span against the freshly built `Vec` lists, order
        // included.  The drifted comparison above validated the
        // *maintenance*; this validates the *build*, and the adopted layout
        // becomes the new dual-write baseline the next drift interval
        // maintains from.  Zero cost and zero reads when the flag is off.
        #[cfg(feature = "std")]
        if crate::watched::csr_shadow_enabled() || crate::watched::csr_b_enabled() {
            use crate::watched::CsrWatchBuild;
            let t0 = std::time::Instant::now();
            let num_lits = num_vars * 2;
            // PRODUCTION SURGERY (NIXIE_SURGERY_PROD=1): when the window's
            // surgical updates hold the watch contract (every live long
            // clause exactly two watchers, dead/short none — audited here,
            // one CSR sweep), the surgically-updated CSR IS the post-round
            // watch state and the counting-sort build is skipped.  A failed
            // audit falls back to the full rebuild — violations cost one
            // extra build, never wrongness.  Note the STATE is contract-equal
            // but the ORDER differs from the rebuild's id order (surgical
            // edits preserve drift order) — a screen-gated heuristic change.
            let mut surgery_skip = false;
            if surgery_prod_enabled()
                && self.csr_surgery_fired
                && let Some(surg) = drifted_shadow.as_ref()
            {
                let clauses = &self.clauses;
                let (total, wrong_live, stale_dead) =
                    self.watches.csr_surgery_contract_audit(surg, |off| {
                        match crate::memory::ClauseRef::from_byte_offset(off) {
                            Some(r) => match clauses.get_by_ref(r) {
                                Some(c) if !c.deleted && c.lits.len() >= 3 => {
                                    crate::watched::ClauseAuditState::LiveLong
                                }
                                _ => crate::watched::ClauseAuditState::DeadOrShort,
                            },
                            None => crate::watched::ClauseAuditState::DeadOrShort,
                        }
                    });
                if wrong_live == 0 {
                    surgery_skip = true;
                    if let Some(mut keep) = drifted_shadow.take() {
                        keep.maintain_index = crate::watched::csr_shadow_enabled()
                            || crate::watched::csr_index_enabled()
                            || els_surgery_enabled();
                        self.watches.csr_set(keep);
                    }
                    #[cfg(feature = "std")]
                    eprintln!(
                        "[surgery-prod] @{conflicts}: SKIP watch rebuild (audit green: {total} entries, {stale_dead} stale-on-dead)",
                        conflicts = self.stats.conflicts
                    );
                } else {
                    #[cfg(feature = "std")]
                    eprintln!(
                        "[surgery-prod] @{conflicts}: audit found {wrong_live} wrong-count clauses — full rebuild",
                        conflicts = self.stats.conflicts
                    );
                }
            }
            if !surgery_skip {
                let mut csr = CsrWatchBuild::default();
                {
                    let Solver { clauses, .. } = self;
                    for cid in clauses.iter_ids() {
                        let Some(c) = clauses.get(cid).filter(|c| !c.deleted) else {
                            continue;
                        };
                        if c.lits.len() < 3 {
                            continue;
                        }
                        csr.count(c.lits[0].negate());
                        csr.count(c.lits[1].negate());
                    }
                }
                csr.layout(num_lits);
                {
                    let Solver { clauses, .. } = self;
                    for cid in clauses.iter_ids() {
                        let Some(c) = clauses.get(cid).filter(|c| !c.deleted) else {
                            continue;
                        };
                        if c.lits.len() < 3 {
                            continue;
                        }
                        let Some(r) = clauses.ref_of(cid) else {
                            continue;
                        };
                        csr.fill(c.lits[0].negate(), Watcher::new(cid, r, c.lits[1]));
                        csr.fill(c.lits[1].negate(), Watcher::new(cid, r, c.lits[0]));
                    }
                }
                if crate::watched::csr_shadow_enabled() {
                    let (lits, entries, bad) = self.watches.csr_shadow_compare(num_vars, &csr);
                    eprintln!(
                        "[csr-shadow] rebuild@{}: lits={lits} entries={entries} mismatched={bad} build={}us",
                        self.stats.conflicts,
                        t0.elapsed().as_micros()
                    );
                }
                // The ELS surgery experiment's equivalence oracle: the shadow
                // holds the SURGICALLY updated state; the Vec lists above hold
                // the rebuilt ground truth.  Multiset equality per literal
                // (order-insensitive — the production surgery accepts an
                // order change, gated by the screen, not trajectory identity)
                // proves the surgery produced exactly the rebuild's entry sets.
                if self.csr_surgery_fired
                    && !surgery_skip
                    && let Some(surg) = drifted_shadow.as_ref()
                {
                    use crate::watched::ClauseAuditState;
                    let clauses = &self.clauses;
                    let (total, wrong_live, stale_dead) =
                        self.watches.csr_surgery_contract_audit(surg, |off| {
                            match crate::memory::ClauseRef::from_byte_offset(off) {
                                Some(r) => match clauses.get_by_ref(r) {
                                    Some(c) if !c.deleted && c.lits.len() >= 3 => {
                                        ClauseAuditState::LiveLong
                                    }
                                    _ => ClauseAuditState::DeadOrShort,
                                },
                                None => ClauseAuditState::DeadOrShort,
                            }
                        });
                    eprintln!(
                        "[csr-surgery] oracle@{}: ops={} entries={total} live-with-wrong-count={wrong_live} stale-on-dead-or-short={stale_dead}",
                        self.stats.conflicts, self.csr_surgery_ops
                    );
                    let (irefs, imissing, istale) = surg.csr_index_audit();
                    eprintln!(
                        "[csr-surgery] index: refs={irefs} with-missing-positions={imissing} with-stale-positions={istale}"
                    );
                    eprintln!(
                        "[csr-surgery] economics: surgery={}us ({} entry visits) vs rebuild-build={}us",
                        self.watches.csr_surgery_nanos / 1000,
                        self.watches.csr_surgery_visits,
                        t0.elapsed().as_micros()
                    );
                    let (sorted, total) = surg.span_sortedness();
                    eprintln!("[csr-surgery] spans sorted-by-ref: {sorted}/{total}");
                    self.watches.csr_surgery_visits = 0;
                    self.watches.csr_surgery_nanos = 0;
                    self.csr_surgery_fired = false;
                    self.csr_surgery_ops = 0;
                }
                let mut adopted = crate::watched::CsrWatchLists::default();
                adopted.maintain_index = crate::watched::csr_shadow_enabled()
                    || crate::watched::csr_index_enabled()
                    || els_surgery_enabled();
                adopted.adopt_layout(csr);
                self.watches.csr_set(adopted);
            }
        }
        #[cfg(feature = "std")]
        if let Ok(prefix) = std::env::var("NIXIE_DUMP_WATCHES_POST") {
            let path = format!("{prefix}-{}.txt", self.stats.conflicts);
            self.watches.dump_watches_post(num_vars, &path);
            if let Ok(bp) = std::env::var("NIXIE_DUMP_BIG_POST") {
                use std::fmt::Write as _;
                let mut out = String::new();
                let mut total = 0usize;
                for code in 0..self.num_vars * 2 {
                    let (start, plen) = self.binary_graph.span_of(code);
                    let primary = &self.binary_graph.edges[start..start + plen];
                    let extra = &self.binary_graph.extra[code];
                    if primary.is_empty() && extra.is_empty() {
                        continue;
                    }
                    total += primary.len() + extra.len();
                    let _ = write!(out, "{code}:");
                    for &(implied, _) in primary.iter().chain(extra.iter()) {
                        let _ = write!(out, " {}", implied.code());
                    }
                    let _ = writeln!(out);
                }
                let bpath = format!("{bp}-{}.txt", self.stats.conflicts);
                let _ = std::fs::write(&bpath, out);
                eprintln!("[big-dump-post] {bpath}: {total} edges");
            }
        }
    }
}
