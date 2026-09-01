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

/// Outcome of one substitution pass.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum SubstOutcome {
    /// Completed; formula still alive.
    Ok,
    /// Substitution proved the formula unsatisfiable (empty clause, conflicting
    /// unit, or an SCC containing both polarities of one variable).
    Unsat,
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
        let mut big_augmented = false;
        if self.config.enable_gate_congruence {
            self.augment_big_with_gate_congruence();
            big_augmented = true;
        }

        // `sub[code(l)]` = representative literal equivalent to `l` (itself if
        // `l` is in no non-trivial SCC). Members are set directly to the rep,
        // and the rep maps to itself, so one lookup resolves any chain.
        let mut sub: Vec<Lit> = (0..num_lits as u32).map(Lit::from_code).collect();

        // ======== Iterative Tarjan over the binary implication graph. ========
        // Nodes are literal codes; successors of `lit` are the literals it
        // directly implies (binary_graph edges). Recursion would overflow on
        // deep implication chains (thousands deep on multiplier circuits).
        let mut index_counter: usize = 0;
        let mut index: Vec<i64> = vec![-1; num_lits]; // -1 = unseen
        let mut lowlink = vec![0usize; num_lits];
        let mut on_stack = vec![false; num_lits];
        let mut stack: Vec<usize> = Vec::new();
        // DFS work stack of (node, next-successor-cursor).
        let mut work: Vec<(usize, usize)> = Vec::new();

        for root in 0..num_lits {
            if index[root] != -1 {
                continue;
            }
            // Seed root.
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
                    if index[w] == -1 {
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
        let live_ids: Vec<ClauseId> = self.clauses.iter_ids().collect();
        let mut new_units: SmallVec<[Lit; 64]> = SmallVec::new();
        let mut eliminated = 0usize;

        for cid in live_ids {
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
            let mapped: SmallVec<[Lit; 8]> = match self.clauses.get(cid) {
                Some(c) if !c.deleted => c.lits.iter().map(|&l| sub[l.code() as usize]).collect(),
                _ => continue,
            };
            if mapped.is_empty() {
                continue;
            }

            let mut satisfied = false;
            let mut lits: Vec<Lit> = Vec::with_capacity(mapped.len());
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
                }
            }
        }

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
        } else {
            self.equiv_substitution
                .resize(num_vars, Lit::pos(Var::new(0)));
        }
        for v in 0..num_vars {
            let cur = self.equiv_substitution[v];
            let rep = sub[cur.code() as usize];
            self.equiv_substitution[v] = rep;
            if rep.var().index() != v {
                eliminated += 1;
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
        // produce hanging units (propagation fixpoint violations). Rebuild
        // from the post-substitution live binary clauses.
        self.refresh_binary_graph();
        SubstOutcome::Ok
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
        self.binary_graph.clear();
        let live_ids: Vec<ClauseId> = self.clauses.iter_ids().collect();
        for cid in live_ids {
            let lits: SmallVec<[Lit; 8]> = match self.clauses.get(cid) {
                Some(c) if !c.deleted && c.lits.len() == 2 => c.lits.iter().copied().collect(),
                _ => continue,
            };
            let (a, b) = (lits[0], lits[1]);
            self.binary_graph.add(a.negate(), b, cid);
            self.binary_graph.add(b.negate(), a, cid);
        }
    }

    pub(super) fn rebuild_watches_and_binary_graph(&mut self) {
        let num_vars = self.num_vars;
        self.watches = WatchLists::new(num_vars);
        self.binary_graph.clear();
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
                binary_graph.add(a.negate(), b, cid);
                binary_graph.add(b.negate(), a, cid);
                watches.phantom_bump(a.negate());
                watches.phantom_bump(b.negate());
                continue;
            }
            watches.add(a.negate(), Watcher::new(cid, r, b));
            watches.add(b.negate(), Watcher::new(cid, r, a));
        }
        learned_clause_ids.retain(|&cid| clauses.get(cid).is_some_and(|c| !c.deleted));
    }
}
