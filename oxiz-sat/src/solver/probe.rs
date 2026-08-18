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
/// cadical `inprobeint` base: first mid-search round after these conflicts,
/// then scaled by 25·log10(rounds+9).
const INPROBE_BASE_INTERVAL: u64 = 2_000;

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
            // Success: record propfixed *after* the probe (no new fixed
            // literals were added at level 0 by the probe itself; the value
            // is the level-0 prefix size).
            self.derive_hyper_binaries(probe, &mut hyper);
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
