//! Structured bounded variable addition (k-way common-literal-set
//! extraction), pre-search slice.
//!
//! The published mechanism (BVA, Manthey et al.; structured variant LiPIcs
//! SAT 2023): find a set of `k ≥ 2` original clauses sharing a common
//! literal set `G`, and replace each `C_i = G ∪ U_i` by
//!
//! * `(G ∨ t)` — one clause, and
//! * `(¬t ∨ U_i)` — one per clause,
//!
//! with a fresh auxiliary `t`.  The encoding is the polarity-optimized
//! Tseitin of `G ∨ (U_1 ∧ … ∧ U_k)` (which is exactly `∧_i (G ∨ U_i)` by
//! distribution): `t` appears only in these clauses, positive in the first
//! and negative in the rest, so no reverse implication is needed.
//!
//! **Equisatisfiability and model preservation, both directions** (the
//! argument the whole pass rests on):
//!
//! * old → new: given a model of the original clauses, set `t := false`
//!   when `G` holds (then `(¬t ∨ U_i)` are satisfied by `¬t`) and
//!   `t := true` otherwise (then every `C_i` is satisfied through its
//!   `U_i`, so `(¬t ∨ U_i)` hold).
//! * new → old: a model of the new clauses either satisfies `G` (then
//!   every original `C_i` is satisfied through `G`) or forces `t` (from
//!   `(G ∨ t)`), and `t` forces every `U_i` (each original `C_i`
//!   satisfied through its `U_i`).
//!
//! So the transformation needs **no model reconstruction record**: the
//! model of the rewritten formula *is* a model of the original over the
//! original variables, and the introduced variables read their values
//! straight from it.
//!
//! **Benefit rule**: original size `k·|G| + Σ|U_i|`, new size
//! `|G| + 1 + Σ(|U_i| + 1) = |G| + Σ|U_i| + k + 1`; the introduction pays
//! when `saving = (k−1)·|G| − (k+1) > 0` (for `|G| = 2` needs `k ≥ 4`,
//! `|G| = 3` needs `k ≥ 3`, larger `k` lowers the bar).
//!
//! Slice gates (see the call site in `Solver::solve`): one-shot,
//! pre-search, decision level 0, base scope only (non-incremental), no
//! attached theory, no proof/LRAT tracer (introduced clauses and retired
//! originals have no derivation story yet — the doc's requirement, not a
//! TODO), bounded budgets.  Default off (`SolverConfig::enable_sbva`).
//!
//! **Matched null** (`NIXIE_SBVA_NULL=1`, the `NIXIE_PROBE_NULL` precedent):
//! identical candidate generation, budgets and application code; only the
//! processing ORDER of candidate groups is scrambled (a fixed hash key
//! instead of the saving rank).  Same number and shape of introductions
//! under the same eligibility rule, no best-first content.

use crate::clause::ClauseId;
use crate::literal::Lit;
use smallvec::SmallVec;

use super::Solver;

/// Hard cap on introduced variables per pass.
const MAX_INTRODUCTIONS: usize = 100_000;
/// Cap on the pair-index build (clauses × pairs); guards pathological
/// wide-clause inputs.
const MAX_PAIR_INDEX_ENTRIES: usize = 8_000_000;

/// One candidate introduction: the group's shared clause ids and the
/// computed common set `G` (literals), with the per-clause remainders
/// recovered at apply time.
struct Candidate {
    ids: SmallVec<[ClauseId; 8]>,
    g: SmallVec<[Lit; 8]>,
    saving: i64,
    /// Rank key: `saving` for the treatment, a scrambled hash for the
    /// matched null (filled by the caller).
    order_key: u64,
}

impl Solver {
    /// Run one bounded-variable-addition pass over the ORIGINAL clauses.
    /// Returns `(vars_introduced, literals_saved)`.
    pub(super) fn structured_bva(&mut self) -> (usize, i64) {
        if self.trail.decision_level() != 0
            || self.proof.is_some()
            || self.lrat
            || self.real_theory_attached
            || self.assertion_levels.len() > 1
            || self.trivially_unsat
        {
            return (0, 0);
        }
        let null_arm = std::env::var("NIXIE_SBVA_NULL").is_ok();

        // ---- 1. Candidate generation: pair index over original clauses.
        // For each unordered literal pair, the original clauses containing
        // both.  A mergeable group is a subset of one pair's list whose
        // full intersection `G` (⊇ the pair by construction) is beneficial.
        let mut pair_index: std::collections::HashMap<(u32, u32), SmallVec<[ClauseId; 8]>> =
            std::collections::HashMap::default();
        let mut entries = 0usize;
        for cid in self.clauses.iter_ids() {
            let Some(c) = self.clauses.get(cid) else {
                continue;
            };
            if c.deleted || c.learned || c.lits.len() < 3 || c.lits.len() > 24 {
                continue;
            }
            // Pairs over the stored literals (order-stable: codes sorted).
            let mut codes: SmallVec<[u32; 24]> = c.lits.iter().map(|l| l.code()).collect();
            codes.sort_unstable();
            for a in 0..codes.len() {
                for b in (a + 1)..codes.len() {
                    entries += 1;
                    if entries > MAX_PAIR_INDEX_ENTRIES {
                        break;
                    }
                    pair_index
                        .entry((codes[a], codes[b]))
                        .or_default()
                        .push(cid);
                }
            }
            if entries > MAX_PAIR_INDEX_ENTRIES {
                break;
            }
        }

        // ---- 2. Collect beneficial candidates.
        let mut candidates: Vec<Candidate> = Vec::new();
        for ((ca, cb), ids) in pair_index.iter() {
            // Same pair clause count first; k >= 2 required.
            if ids.len() < 2 {
                continue;
            }
            // Live filter + snapshot literal sets.
            let mut group: SmallVec<[(ClauseId, SmallVec<[Lit; 24]>); 8]> = SmallVec::new();
            for &cid in ids {
                let Some(c) = self.clauses.get(cid) else {
                    continue;
                };
                if c.deleted || c.learned {
                    continue;
                }
                let lits: SmallVec<[Lit; 24]> = c.lits.iter().copied().collect();
                if lits.len() < 3 {
                    continue;
                }
                group.push((cid, lits));
            }
            let k_all = group.len();
            if k_all < 2 {
                continue;
            }
            // G = intersection of all group clauses (contains the pair).
            let mut g: SmallVec<[Lit; 24]> = group[0].1.clone();
            for (_, lits) in group.iter().skip(1) {
                g.retain(|l| lits.contains(l));
            }
            if g.len() < 2 {
                continue;
            }
            // Drop clauses whose remainder is empty (C_i == G: subsumed by
            // the kept (G ∨ t) encoding's base clause? No — C_i == G stays
            // as-is and must NOT be retired; it does not join the merge).
            let merge: SmallVec<[ClauseId; 8]> = group
                .iter()
                .filter(|(_, lits)| lits.len() > g.len())
                .map(|(cid, _)| *cid)
                .collect();
            let k = merge.len();
            if k < 2 {
                continue;
            }
            let saving = (k as i64 - 1) * g.len() as i64 - (k as i64 + 1);
            if saving <= 0 {
                continue;
            }
            let g_small: SmallVec<[Lit; 8]> = g.iter().copied().collect();
            candidates.push(Candidate {
                ids: merge,
                g: g_small,
                saving,
                order_key: 0,
            });
            let _ = (ca, cb);
        }

        if candidates.is_empty() {
            return (0, 0);
        }

        // ---- 3. Rank: best-saving first (treatment) or scrambled (null).
        for c in &mut candidates {
            c.order_key = if null_arm {
                // Fixed-key scramble of the candidate's identity: same
                // set of candidates, same eligibility, zero rank signal.
                let mut h: u64 = 0x9E37_79B9_7F4A_7C15;
                for &cid in &c.ids {
                    h ^= (cid.index() as u64).wrapping_mul(0xBF58_476D_1CE4_E5B9);
                    h = h.rotate_left(27);
                }
                for l in &c.g {
                    h ^= (l.code() as u64).wrapping_mul(0x94D0_49BB_1331_11EB);
                    h = h.rotate_left(31);
                }
                h
            } else {
                // Pack (saving, tie-break on first clause id) so the sort is
                // deterministic.
                (c.saving as u64) << 32 | (c.ids[0].index() as u64 & 0xFFFF_FFFF)
            };
        }
        candidates.sort_by_key(|c| core::cmp::Reverse(c.order_key));

        // ---- 4. Apply greedily until budgets; groups whose clauses were
        // consumed by an earlier introduction are skipped (still-live check).
        let mut introduced = 0usize;
        let mut total_saving: i64 = 0;
        for cand in &candidates {
            if introduced >= MAX_INTRODUCTIONS {
                break;
            }
            // Re-validate the whole group under the current DB state.
            let mut group: SmallVec<[(ClauseId, SmallVec<[Lit; 24]>); 8]> = SmallVec::new();
            let mut live = true;
            for &cid in &cand.ids {
                let Some(c) = self.clauses.get(cid) else {
                    live = false;
                    break;
                };
                if c.deleted || c.learned {
                    live = false;
                    break;
                }
                let lits: SmallVec<[Lit; 24]> = c.lits.iter().copied().collect();
                if !cand.g.iter().all(|gl| lits.contains(gl)) || lits.len() <= cand.g.len() {
                    live = false;
                    break;
                }
                group.push((cid, lits));
            }
            if !live {
                continue;
            }

            // Fresh aux var; `new_var` wires it into every heuristic table.
            let t = Lit::pos(self.new_var());

            // (G ∨ t)
            let mut base: SmallVec<[Lit; 24]> = cand.g.iter().copied().collect();
            base.push(t);
            self.clauses.add_original(base.iter().copied());
            // (¬t ∨ U_i) per clause; retire the originals.
            for (cid, lits) in &group {
                let mut rest: SmallVec<[Lit; 24]> = SmallVec::new();
                for &l in lits {
                    if !cand.g.contains(&l) {
                        rest.push(l);
                    }
                }
                debug_assert!(!rest.is_empty());
                rest.push(t.negate());
                self.clauses.add_original(rest.iter().copied());
                // Pre-search at level 0 with no reasons on untouched
                // originals: a raw delete is exact here (no BIG edges or
                // reasons reference a clause never yet watched).
                self.clauses.remove(*cid);
            }
            introduced += 1;
            total_saving += cand.saving;
        }

        // ---- 5. Watches/BIG are stale for every touched clause: rebuild.
        if introduced > 0 {
            self.rebuild_watches_and_binary_graph();
        }
        (introduced, total_saving)
    }
}
