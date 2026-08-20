//! Failed-literal probing over binary-implication-graph roots — a port of
//! CaDiCaL `probe.cpp`'s scheduling discipline.
//!
//! Our previous probing (pre-search only, behind `INPROCESS`) walked every
//! variable **by index** and probed **both polarities**. CaDiCaL probes are
//! selected far more cheaply and effectively:
//!
//! * **Roots of the binary implication graph**: literals that occur
//!   *negatively* in a binary clause but not *positively* (`¬a ∨ b` makes
//!   `¬a` occur negatively... in the counting sense used here: the literal
//!   whose *negation* starts implications). Probing non-root literals pays a
//!   propagation cascade whose head is already implied; roots are where new
//!   failed literals and hyper-binary resolvents actually come from.
//! * **Ranked by negated-occurrence count** (descending): more binary
//!   implications out of the probe literal ⇒ richer cascade ⇒ more likely to
//!   fail or to derive hyper-binaries.
//! * **`propfixed` memoization** (Simons et al. 2002 / Boufkhad): when a
//!   probe propagates without conflict, remember the number of level-0
//!   assignments at that moment; re-probing the same literal is pointless
//!   until *new* level-0 facts appear (`propfixed(lit) >= all_fixed`).
//!   Failed literals are consumed (forced as level-0 units), so they never
//!   re-enter the queue.
//!
//! The probe itself assigns the literal at a fresh level and propagates:
//! conflict ⇒ the negation is a forced level-0 unit; success ⇒ every literal
//! `q` assigned during the cascade with a **non-binary** reason yields the
//! hyper-binary clause `(¬probe ∨ q)` (a real implication edge).
//!
//! Scheduling (cadical `inprobing`/`inprobe`): one probe round runs
//! `inprobe()` at the root, budgeted in propagations as a fraction of search
//! ticks (`probe_effort` per-mille), and re-arms when the conflict limit
//! passes with something new (units fixed, or original clauses
//! removed/shrunk — the same "new units" re-arm the eliminator uses).

use super::*;

/// cadical `probeeffort` (per-mille of search ticks as the probe budget).
const PROBE_EFFORT_PERMILLE: u64 = 80;
/// cadical `probmineff`: floor on the propagation budget of a round.
const PROBE_MIN_EFFORT: u64 = 1_000_000;
/// cadical `probemaxeff`: ceiling on the budget.
const PROBE_MAX_EFFORT: u64 = 2_000_000_000;
/// cadical `inprobeint` (its default 100): the base unit of the mid-search
/// probe schedule. The next round fires after
/// `25 × inprobeint × log10(rounds + 9)` conflicts (cadical `probe.cpp`),
/// i.e. ≈ 2.4k conflicts after the first round – NOT a flat 2 000× interval;
/// the previous value of 2 000 here delayed the second round to ~50k
/// conflicts, 20× later than cadical, starving the search of hyper-binaries
/// and forced units on probing-friendly instances.
pub(super) const INPROBE_BASE_INTERVAL: u64 = 100;

impl Solver {
    /// cadical `inprobing`: the mid-search probe-round trigger.
    pub(super) fn inprobing(&self) -> bool {
        if !self.config.enable_inprocessing || !self.config.enable_failed_literal_probing {
            return false;
        }
        self.stats.conflicts >= self.lim_inprobe
    }

    /// One probe round (cadical `probe`): schedule roots, probe each within
    /// the budget, force failed literals, derive hyper-binaries. Returns
    /// `(probed, failed, hyper)`; `failed > 0` re-arms dependent passes.
    pub(super) fn probe_round(&mut self) -> (usize, usize, usize) {
        if self.trail.decision_level() != 0 {
            self.backtrack_with_phase_saving(0);
        }
        if self.trivially_unsat || self.propagate().is_some() {
            self.trivially_unsat = true;
            return (0, 0, 0);
        }
        self.elim_probes_done = self.elim_probes_done.saturating_add(1);

        // Budget: fraction of accumulated search ticks (cadical SET_EFFORT_LIMIT).
        let ticks = self.ticks_focused + self.ticks_stable;
        let budget = (ticks.saturating_mul(PROBE_EFFORT_PERMILLE) / 1000)
            .clamp(PROBE_MIN_EFFORT, PROBE_MAX_EFFORT);
        let start_props = self.stats.propagations;

        // Schedule binary roots, ranked by negated-occurrence count.
        let queue = self.generate_probes();
        let (mut probed, mut failed, mut hyper) = (0usize, 0usize, 0usize);

        for probe in queue {
            if self.trivially_unsat {
                break;
            }
            if self.stats.propagations.saturating_sub(start_props) > budget {
                break;
            }
            if self.trail.is_assigned(probe.var()) {
                continue;
            }
            // `propfixed` memoization: skip if propagated before with no new
            // level-0 facts since.
            let pf = self.probe_propfixed[probe.code() as usize];
            if pf >= self.trail.size() as i64 {
                continue;
            }

            probed += 1;
            self.trail.new_decision_level();
            self.trail.assign_decision(probe);
            let (conflict, aborted) = self.propagate_bounded(20_000);
            if conflict {
                self.backtrack(0);
                // The probe literal is failed: its negation is forced.
                self.force_level0(probe.negate());
                failed += 1;
                if self.trivially_unsat {
                    break;
                }
                continue;
            }
            if aborted {
                self.backtrack(0);
                continue;
            }
            // Success: derive dominator-keyed hyper-binaries (see
            // `derive_hyper_binaries_dominator`), then record propfixed.
            self.derive_hyper_binaries_dominator(&mut hyper);
            self.backtrack(0);
            self.probe_propfixed[probe.code() as usize] = self.trail.size() as i64;
        }

        // Propagate any forced units to fixpoint (force_level0 assigns; the
        // propagation happens there, but re-check the whole trail).
        if !self.trivially_unsat && self.propagate().is_some() {
            self.trivially_unsat = true;
        }

        self.last_probe_units = self.trail.size();
        // Next round: 25 × interval × log10(rounds + 9) conflicts out (cadical).
        let rounds = self.elim_probes_done;
        let delta =
            (INPROBE_BASE_INTERVAL.saturating_mul(25)).saturating_mul(round_log10(rounds + 9));
        self.lim_inprobe = self.stats.conflicts.saturating_add(delta);

        (probed, failed, hyper)
    }

    /// cadical `generate_probes`: binary-implication-graph roots, ranked by
    /// negated binary occurrence count (descending).
    fn generate_probes(&mut self) -> Vec<Lit> {
        let num_vars = self.num_vars;
        let mut noccs = vec![0u32; 2 * num_vars];
        // Count binary-clause literal occurrences. Originals first (they are
        // the implication structure); learned binaries are real clauses too,
        // so both count (the binary graph may lag until rebuilt).
        for cid in self.clauses.iter_ids() {
            let Some(c) = self.clauses.get(cid) else {
                continue;
            };
            if c.deleted || c.lits.len() != 2 {
                continue;
            }
            noccs[c.lits[0].code() as usize] += 1;
            noccs[c.lits[1].code() as usize] += 1;
        }
        let mut probes: Vec<Lit> = Vec::new();
        for idx in 0..num_vars {
            let v = Var::new(idx as u32);
            if self.trail.is_assigned(v) || self.var_eliminated(v) {
                continue;
            }
            let pos = Lit::pos(v);
            let neg = pos.negate();
            let have_pos = noccs[pos.code() as usize] > 0;
            let have_neg = noccs[neg.code() as usize] > 0;
            // Root (cadical `probe = have_neg_bin_occs ? idx : -idx`):
            // the probe literal is the one occurring *negatively* in binary
            // clauses — i.e. `¬probe` heads implications, so probing `probe`
            // drives the richest cascade. Exactly one polarity occurs.
            let probe = if have_neg && !have_pos {
                pos
            } else if have_pos && !have_neg {
                neg
            } else {
                continue;
            };
            if self.probe_propfixed[probe.code() as usize] >= self.trail.size() as i64 {
                continue;
            }
            probes.push(probe);
        }
        // Rank: more negated occurrences of the probe (i.e. occurrences of
        // ¬probe) first.
        probes.sort_unstable_by_key(|&p| core::cmp::Reverse(noccs[p.negate().code() as usize]));
        // Matched-null arm (docs/BENCHMARKING.md): reverse the rank order.
        // The null runs the identical schedule/budget/propagations on the
        // same root literals, differing ONLY in the semantic content under
        // test (which root is probed first). Selected via OXIZ_PROBE_NULL=1
        // for the A/B harness; inert otherwise.
        if crate::probe_null_enabled() {
            probes.reverse();
        }
        probes
    }
}

impl Solver {
    /// Dominator-keyed hyper-binary resolution (a port of cadical's
    /// `hyper_binary_resolve` + `probe_dominator`, applied post-hoc).
    ///
    /// For every literal `q` propagated during the probe by a **long**
    /// (non-binary) reason `R = (q ∨ f1 ∨ … ∨ fk)` (all `fi` false), the
    /// derived binary is `(¬dom ∨ q)` where `dom` is the closest common
    /// ancestor – in the level-1 implication tree – of the literals `¬fi`
    /// that sit at level 1. Any common ancestor yields an implied binary
    /// (resolve `R` against the implication chains `dom → ¬fi`); the closest
    /// one is the strongest, and being closer to the probe root than `q`
    /// itself, the resolvent is a *backbone* edge rather than a probe-local
    /// one: `(¬probe ∨ q)` (the previous derivation) is the degenerate
    /// `dom = probe` case.
    ///
    /// Parents are reconstructed in trail order: a binary reason `(¬p ∨ q)`
    /// gives `parent(q) = p` directly; a long reason's parent is the
    /// dominator of its own false literals, already computable because every
    /// false literal was assigned (and processed) earlier. This mirrors
    /// cadical's on-the-fly parents (`set_parent_reason_literal`) without
    /// specializing the propagation loop.
    ///
    /// When the resolvent's `¬dom` already occurs in `R`, the binary
    /// subsumes `R` (cadical case (B)): `R` is retired. Retiring a reason
    /// clause mid-probe is sound – the resolvent plus the implication chains
    /// entail `R`, so any later conflict analysis resolving through `R`
    /// still resolves through an entailed clause.
    pub(super) fn derive_hyper_binaries_dominator(&mut self, hyper: &mut usize) {
        // Level-1 assignments in trail order (the probe's implication tree).
        let level_lits: SmallVec<[Lit; 64]> = self.trail.level_assignments().to_vec().into();
        if level_lits.is_empty() {
            return;
        }
        let num_lits = 2 * self.num_vars.max(1);
        // parent[code(lit)] = the implying literal's code
        // (u32::MAX = none/root probe; 0 is a VALID literal code).
        let mut parent: Vec<u32> = vec![u32::MAX; num_lits];

        for &q in &level_lits {
            let Reason::Propagation(cid) = self.trail.reason(q.var()) else {
                // The probe decision itself: root, no parent.
                continue;
            };
            let Some(c) = self.clauses.get(cid) else {
                continue;
            };
            if c.deleted || c.lits.len() <= 2 {
                // Binary reasons are already edges: parent is the other
                // literal of the binary clause. Find it through the reason
                // clause's literals (q is one of them; the false one implies
                // q).
                if let Some(c2) = self.clauses.get(cid).filter(|c2| c2.lits.len() == 2) {
                    let other = if c2.lits[0] == q {
                        c2.lits[1]
                    } else {
                        c2.lits[0]
                    };
                    let p = other.negate().code();
                    if p != q.code() {
                        parent[q.code() as usize] = p;
                    }
                }
                continue;
            }
            // Long reason R = (q ∨ f1 … fk): collect level-1 false lits'
            // negations and fold the dominator over them.
            let reason_lits: SmallVec<[Lit; 8]> = c.lits.iter().copied().collect();
            let mut dom: Option<u32> = None;
            for &f in &reason_lits {
                if f == q {
                    continue;
                }
                let nf = f.negate(); // true on the trail
                if self.trail.level(nf.var()) != 1 {
                    // Root-level fixed (cadical: `if (!var(other).level)
                    // continue;`) or not assigned by this probe: contributes
                    // nothing to the dominator, and its trail index would
                    // corrupt the parent walk.
                    continue;
                }
                let nf_code = nf.code();
                match dom {
                    None => dom = Some(nf_code),
                    Some(d) => {
                        if d != nf_code {
                            dom = Some(self.probe_dominator(d, nf_code, &parent));
                        }
                    }
                }
            }
            let Some(dom_code) = dom else { continue };
            parent[q.code() as usize] = dom_code;

            // Derive (¬dom ∨ q). Skip the degenerate dom == ¬(¬q)... note
            // dom is a *true* literal's code; the binary is (¬dom_lit ∨ q).
            let dom_lit = Lit::from_code(dom_code);
            let neg_dom = dom_lit.negate();
            if neg_dom == q {
                continue; // tautology, cannot happen but refuse anyway
            }
            if self.has_binary_implication(dom_lit, q) {
                continue;
            }
            let id = self.clauses.add_learned([neg_dom, q]);
            let lbd = self.compute_lbd(&[neg_dom, q]);
            self.clauses.set_lbd(id, lbd);
            self.debug_check_learned_clause_lbd(id);
            self.binary_graph.add(dom_lit, q, id);
            self.binary_graph.add(q.negate(), neg_dom, id);
            self.watches.add(neg_dom, Watcher::new(id, q));
            self.watches.add(q.negate(), Watcher::new(id, neg_dom));
            self.clause_hyper.resize(id.index() + 1, false);
            self.clause_hyper[id.index()] = true;
            *hyper += 1;

            // Case (B): the resolvent subsumes R when ¬dom ∈ R. cadical's
            // `red = !contained || reason->redundant`: subsuming an
            // ORIGINAL clause obliges the subsumer to carry its deletion
            // permanently – promote the binary to original before retiring
            // R. Leaving the binary learned (the port's first version)
            // under-constrains the formula once a later database reduction
            // deletes it: R is gone, only the weaker resolvent remains, and
            // UNSAT flips to SAT (reproducer: Break_unsat_06_07 under
            // INPROCESS+PROBE+HBP+BVE, 165 ms).
            if reason_lits.contains(&neg_dom) {
                // Never retire a clause that is a live propagation reason:
                // the trail's `reason` pointers must name live clauses
                // (debug invariant + conflict-analysis contract; the same
                // guard `reduce_clause_database` applies). During the probe
                // this covers level-1 literals of earlier cascade steps and
                // any level-0 propagation whose reason R happens to be.
                // A live clause is the recorded reason of at most its
                // `lits[0]` variable (the propagate watch-position
                // invariant: the propagated literal sits at position 0) –
                // the same O(1) guard `reduce_clause_database` uses. Note
                // this also (necessarily) covers the literal q currently
                // being processed, whose reason R is by construction.
                let head = reason_lits.first().copied();
                let is_reason = head.is_some_and(|h| {
                    self.trail.is_assigned(h.var())
                        && matches!(
                            self.trail.reason(h.var()),
                            Reason::Propagation(r) if r == cid
                        )
                });
                if !is_reason {
                    let r_learned = self.clauses.get(cid).is_some_and(|c| c.learned);
                    if !r_learned {
                        self.clauses.clear_learned(id);
                    }
                    // Retiring R is sound in both arms: original-R is
                    // covered by the promoted binary; learned-R was
                    // optional anyway. `retire_clause` re-points any live
                    // reason reference (including this literal's own).
                    self.retire_clause(cid);
                    self.stats.subsumed_removed += 1;
                }
            }
        }
    }

    /// Closest common ancestor of two level-1 literals in the probe's
    /// implication tree (cadical `probe_dominator`): walk the
    /// later-assigned one up its parent chain until the two meet. Sound
    /// because every parent edge is an implication established during this
    /// probe (binary clause or an already-derived dominator resolvent).
    fn probe_dominator(&self, a: u32, b: u32, parent: &[u32]) -> u32 {
        let trail_of = |code: u32| -> usize {
            let lit = Lit::from_code(code);
            self.trail.trail_index(lit.var()) as usize
        };
        let (mut l, mut k) = (a, b);
        let (mut tl, mut tk) = (trail_of(l), trail_of(k));
        let mut guard = 0usize;
        while l != k {
            guard += 1;
            if guard > self.num_vars + 2 {
                // Cycle defense: cannot happen through API-constructed
                // parents (they strictly decrease trail index), but a
                // corrupted parent chain must degrade, not hang.
                return l;
            }
            if tl > tk {
                core::mem::swap(&mut l, &mut k);
                core::mem::swap(&mut tl, &mut tk);
            }
            // l is earlier; advance k up.
            let p = parent[k as usize];
            if p == u32::MAX {
                return l; // k reached the root; l is the meeting point
            }
            k = p;
            tk = trail_of(k);
        }
        l
    }
}

/// log10 approximated in integers (cadical uses `log10` on the round count).
fn round_log10(n: u64) -> u64 {
    let mut digits = 1u64;
    let mut v = n;
    while v >= 10 {
        v /= 10;
        digits += 1;
    }
    digits
}
