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
        if self.did_equiv_subst
            || self.trail.decision_level() != 0
            || self.assertion_levels.len() > 1
            || self.proof.is_some()
        {
            return SubstOutcome::Ok;
        }

        let num_vars = self.num_vars;
        let num_lits = num_vars * 2;

        // Refresh the binary implication graph from current (incl. learned)
        // binary clauses so the SCC sees equivalences exposed during search —
        // essential for inprocessing re-runs. (On the first, pre-search call
        // the graph is already current; this is a cheap no-op there.)
        self.refresh_binary_graph();

        // Augment the binary implication graph with equivalences inferred from
        // congruent AND/XOR gates (multiplier / adder structure) before SCC, so
        // the closure below folds them in too.
        self.augment_big_with_gate_congruence();

        // `sub[code(l)]` = representative literal equivalent to `l` (itself if
        // `l` is in no non-trivial SCC). Members are set directly to the rep,
        // and the rep maps to itself, so one lookup resolves any chain.
        let mut sub: Vec<Lit> = (0..num_lits as u32).map(Lit::from_code).collect();

        // ---- Iterative Tarjan over the binary implication graph. ----
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
                    work.last_mut().unwrap().1 = succ_i + 1;
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
                        // SCC's `stack[scc_start..]` slice re-included them —
                        // fabricating equivalences (and spurious pos(v)≡neg(v)
                        // contradictions) that proved satisfiable formulas UNSAT.
                        let scc_members = stack.split_off(scc_start);
                        if scc_members.len() > 1 {
                            let rep = Lit::from_code(
                                (*scc_members.iter().min().unwrap()) as u32,
                            );
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

        // Early-out if nothing actually moved.
        if !(0..num_lits).any(|c| sub[c].code() as usize != c) {
            self.did_equiv_subst = true;
            return SubstOutcome::Ok;
        }

        // ---- Rewrite every live clause through the map. ----
        let live_ids: Vec<ClauseId> = self.clauses.iter_ids().collect();
        let mut new_units: SmallVec<[Lit; 64]> = SmallVec::new();
        let mut eliminated = 0usize;

        for cid in live_ids {
            let mapped: SmallVec<[Lit; 8]> = match self.clauses.get(cid) {
                Some(c) if !c.deleted => c.lits.iter().map(|&l| sub[l.code() as usize]).collect(),
                _ => continue,
            };
            if mapped.is_empty() {
                continue;
            }

            // Sort + dedup + tautology detection. After sorting by code, the
            // two polarities of one variable are adjacent (pos(v)=2v, neg(v)=2v+1),
            // so a tautology is any adjacent pair sharing a variable.
            let mut lits: Vec<Lit> = mapped.to_vec();
            lits.sort_unstable_by_key(|l| l.code());
            lits.dedup_by_key(|l| l.code());
            let tautology = lits.windows(2).any(|w| w[0].var() == w[1].var());

            if tautology {
                if let Some(c) = self.clauses.get_mut(cid) {
                    c.deleted = true;
                }
                continue;
            }
            match lits.len() {
                0 => {
                    // Every literal collapsed to one value and was a duplicate —
                    // impossible after dedup unless the original was empty.
                    self.trivially_unsat = true;
                    return SubstOutcome::Unsat;
                }
                1 => {
                    new_units.push(lits[0]);
                    if let Some(c) = self.clauses.get_mut(cid) {
                        c.deleted = true;
                    }
                }
                _ => {
                    if let Some(c) = self.clauses.get_mut(cid) {
                        c.lits = lits.into();
                    }
                }
            }
        }

        // ---- Record model-reconstruction map + branching-skip flag. ----
        // `equiv_substitution[v]` is the CUMULATIVE representative literal for
        // `v` across all substitution rounds (identity `pos(v)` if never
        // eliminated). Each round COMPOSES this round's `sub` onto it — so an
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
            self.equiv_substitution.resize(num_vars, Lit::pos(Var::new(0)));
        }
        for v in 0..num_vars {
            let cur = self.equiv_substitution[v];
            let rep = sub[cur.code() as usize];
            self.equiv_substitution[v] = rep;
            if rep.var().index() != v {
                eliminated += 1;
            }
        }


        // ---- Rebuild watch lists + binary implication graph. ----
        self.rebuild_watches_and_binary_graph();

        // ---- Assign the newly exposed level-0 units and re-propagate. ----
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
        self.did_equiv_subst = true;
        SubstOutcome::Ok
    }

    /// True if `v` was folded away by equivalent-literal substitution or BVE
    /// and must not be branched on. Cheap: empty maps mean no pass ran.
    #[inline]
    pub(super) fn var_eliminated(&self, v: Var) -> bool {
        (self.equiv_substitution.len() > v.index()
            && self.equiv_substitution[v.index()].var() != v)
            || (self.bve_def.len() > v.index() && !self.bve_def[v.index()].is_empty())
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
        let live_ids: Vec<ClauseId> = self.clauses.iter_ids().collect();
        for cid in live_ids {
            let lits: SmallVec<[Lit; 8]> = match self.clauses.get(cid) {
                Some(c) if !c.deleted => c.lits.iter().copied().collect(),
                _ => continue,
            };
            match lits.len() {
                2 => {
                    let (a, b) = (lits[0], lits[1]);
                    self.binary_graph.add(a.negate(), b, cid);
                    self.binary_graph.add(b.negate(), a, cid);
                    self.watches.add(a.negate(), Watcher::new(cid, b));
                    self.watches.add(b.negate(), Watcher::new(cid, a));
                }
                n if n >= 3 => {
                    let (a, b) = (lits[0], lits[1]);
                    self.watches.add(a.negate(), Watcher::new(cid, b));
                    self.watches.add(b.negate(), Watcher::new(cid, a));
                }
                _ => {} // units are level-0 facts on the trail
            }
        }
        self.learned_clause_ids
            .retain(|&cid| self.clauses.get(cid).is_some_and(|c| !c.deleted));
    }
}
