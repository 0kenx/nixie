//! Structured bounded variable addition (k-way common-literal-set
//! extraction): pre-search one-shot and mid-search inprocessing slices.
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
//! ## Slices
//!
//! * **Pre-search** (`enable_sbva`, `structured_bva`): one-shot before the
//!   search, gates: decision level 0, base scope only (non-incremental),
//!   no attached theory, no proof/LRAT tracer (introduced clauses and
//!   retired originals have no derivation story yet — the doc's
//!   requirement, not a TODO), bounded budgets.  Default off.  Matched
//!   null: `NIXIE_SBVA_NULL=1` (scrambled rank key).
//! * **Mid-search** (`enable_mid_bva`, `structured_bva_mid`, fired inside
//!   `inprocess()` rounds): the same generation/rank/apply machinery with
//!   effort budgets from the round's search-work window
//!   ([`super::learn::InprocBudgets`]) and mid-search hygiene:
//!   (a) groups containing a **live level-0 reason clause** are skipped —
//!   conflict analysis must never resolve against a retired clause;
//!   (b) retired and added clauses' variables are re-marked for the
//!   eliminator (`mark_elim_vars`) so its occurrence machinery sees the
//!   new structure;
//!   (c) the caller rebuilds watches/BIG and re-propagates once after
//!   introductions (new `(G ∨ t)`/`(¬t ∨ U_i)` clauses can be unit under
//!   the level-0 trail: `G` fully false forces `t`, then `t` forces each
//!   `U_i` — exactly the propagation the encoding guarantees, so a
//!   conflict there certifies Unsat against live clauses).
//!   Default off; knobs `NIXIE_BVA_MID=1` / `NIXIE_BVA_MID_NULL=1` in
//!   `stats_solve`.
//!
//! **Determinism**: candidate collection iterates the pair index in
//! **sorted key order** (not `HashMap` iteration, whose `RandomState`
//! order is per-process random — ties in the rank key would otherwise
//! resolve nondeterministically across runs).  The rank key is
//! `(saving, first clause id)`; ties between distinct groups sharing both
//! are then broken by the sorted pair order, deterministic by
//! construction.

use crate::clause::ClauseId;
use crate::literal::Lit;
use smallvec::SmallVec;

use super::Solver;

/// Hard cap on introduced variables per pass (pre-search / legacy budget).
const MAX_INTRODUCTIONS: usize = 100_000;
/// Cap on the pair-index build (clauses × pairs); guards pathological
/// wide-clause inputs (pre-search / legacy budget).
const MAX_PAIR_INDEX_ENTRIES: usize = 8_000_000;

/// Per-pass options shared by both slices.
pub(super) struct BvaOpts {
    /// Pair-index build cap (entries).
    max_entries: usize,
    /// Maximum introductions this pass.
    max_intros: usize,
    /// Matched-null arm: scramble the rank key.
    null_arm: bool,
    /// Mid-search hygiene: live-reason group skips + eliminator marking.
    mid_search: bool,
}

impl BvaOpts {
    fn presearch() -> Self {
        Self {
            max_entries: MAX_PAIR_INDEX_ENTRIES,
            max_intros: MAX_INTRODUCTIONS,
            null_arm: false,
            mid_search: false,
        }
    }
}

impl Solver {
    /// Mid-search AND-gate factoring (kissat `factor.c`'s rewrite, single-hop
    /// slice): a group of `k ≥ 2` original binary clauses sharing a literal
    /// `q` — `(x_1 ∨ q), …, (x_k ∨ q)` — becomes a fresh hub variable `t`
    /// with
    ///
    /// * `(¬t ∨ q)` — the shared consequence, one clause, and
    /// * `(t ∨ x_i)` — one per partner,
    ///
    /// deleting the originals.  Equisatisfiability (both directions):
    /// `q` true → set `t := true` (every `(t ∨ x_i)` satisfied, `(¬t ∨ q)`
    /// by `q`); `q` false → `(¬t ∨ q)` forces `¬t`, then every `(t ∨ x_i)`
    /// forces `x_i` — exactly what the originals forced.  Any model of the
    /// new clauses restricted to the original variables satisfies the
    /// originals, so no reconstruction record is needed.  Unit-propagation
    /// consequences are preserved through the hub (a falsified `q` or
    /// `x_i` re-derives the same forced literal via `t`), which is what
    /// makes `retire_clause`'s reason re-pointing safe here.
    ///
    /// This is deliberately NOT the literal-saving rule: the rewrite adds
    /// `+1` clause and `+2` literals per group.  The return is search
    /// structure — the hub centralizes `k` shared implications, and the
    /// introduced clauses re-arm elimination for the partners (each `x_i`
    /// now occurs in one fewer original).  kissat runs exactly this shape
    /// (its chain/hop generalization) inside elimination rounds; its
    /// `factor_ticks` own up to 71 % of its work on the worker class.
    ///
    /// Rank: largest group first (treatment) / scrambled (null arm,
    /// `config.mid_andgate_null`).  Retirement goes through
    /// [`Solver::remove_clause`] (BIG-edge purge, live-reason re-pointing,
    /// watcher removal, live counters); the caller rebuilds watches/BIG
    /// and re-propagates once after the whole BVA block.
    pub(super) fn and_gate_factoring_mid(&mut self) -> usize {
        if self.trail.decision_level() != 0
            || self.proof.is_some()
            || self.lrat
            || self.real_theory_attached
            || self.assertion_levels.len() > 1
            || self.trivially_unsat
        {
            return 0;
        }
        let (scan_cap, max_intros) = if self.inproc_budgets.window > 0 {
            (
                (self.inproc_budgets.bva_entries as usize).clamp(100_000, 4_000_000),
                (self.inproc_budgets.bva_intros as usize).clamp(50, 10_000),
            )
        } else {
            (4_000_000, 20_000)
        };

        // ---- 1. Tail index over original binaries: literal q -> partners
        // (with clause ids).  Each binary (a ∨ b) feeds both orientations.
        let mut tail_index: std::collections::HashMap<u32, SmallVec<[(u32, u32); 8]>> =
            std::collections::HashMap::default();
        let mut scanned = 0usize;
        'outer: for cid in self.clauses.iter_ids() {
            let Some(c) = self.clauses.get(cid) else {
                continue;
            };
            if c.deleted || c.learned || c.lits.len() != 2 {
                continue;
            }
            scanned += 1;
            if scanned > scan_cap {
                break 'outer;
            }
            let (a, b) = (c.lits[0], c.lits[1]);
            tail_index
                .entry(a.code())
                .or_default()
                .push((b.code(), cid.index() as u32));
            tail_index
                .entry(b.code())
                .or_default()
                .push((a.code(), cid.index() as u32));
        }

        // ---- 2. Groups: tails with k >= 2 distinct partners.
        struct GateCandidate {
            tail: u32,
            partners: SmallVec<[(u32, u32); 8]>, // (partner code, clause id)
            order_key: u64,
        }
        let mut candidates: Vec<GateCandidate> = Vec::new();
        let mut keys: Vec<&u32> = tail_index.keys().collect();
        keys.sort_unstable(); // deterministic iteration (see module doc)
        for key in keys {
            let mut partners = tail_index[key].clone();
            if partners.len() < 2 {
                continue;
            }
            // One entry per partner (a duplicate binary cannot exist in
            // the deduplicated database; a partner appearing via BOTH
            // orientations of one clause — (q∨x) counted under tail q only
            // once — is impossible since each clause contributes exactly
            // one partner per tail).
            partners.sort_unstable();
            candidates.push(GateCandidate {
                tail: *key,
                partners,
                order_key: 0,
            });
        }
        if candidates.is_empty() {
            return 0;
        }

        // ---- 3. Rank: largest group first; scrambled for the null.
        for c in &mut candidates {
            c.order_key = if self.config.mid_andgate_null {
                let mut h: u64 = 0x2545_F491_4F6C_DD1D;
                h ^= (c.tail as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15);
                h = h.rotate_left(29);
                for &(p, _) in &c.partners {
                    h ^= (p as u64).wrapping_mul(0xBF58_476D_1CE4_E5B9);
                    h = h.rotate_left(31);
                }
                h
            } else {
                // (k, tie-break on tail code) — deterministic.
                ((c.partners.len() as u64) << 32) | (c.tail as u64)
            };
        }
        candidates.sort_by_key(|c| core::cmp::Reverse(c.order_key));

        // ---- 4. Apply until the introduction budget.
        let mut introduced = 0usize;
        for cand in &candidates {
            if introduced >= max_intros {
                break;
            }
            // Re-validate: every member binary still live and contains the
            // tail (an earlier introduction in this same pass may have
            // retired one).
            let mut group: SmallVec<[ClauseId; 8]> = SmallVec::new();
            let mut live = true;
            for &(_, idx) in &cand.partners {
                let cid = ClauseId::new(idx);
                let Some(c) = self.clauses.get(cid) else {
                    live = false;
                    break;
                };
                if c.deleted || c.learned || c.lits.len() != 2 {
                    live = false;
                    break;
                }
                let tail = Lit::from_code(cand.tail);
                if !c.lits.contains(&tail) {
                    live = false;
                    break;
                }
                group.push(cid);
            }
            if !live || group.len() < 2 {
                continue;
            }

            let tail = Lit::from_code(cand.tail);
            let t = Lit::pos(self.new_var());
            // (¬t ∨ q)
            self.clauses.add_original([t.negate(), tail]);
            // (t ∨ x_i) per partner.
            for &cid in &group {
                let Some(c) = self.clauses.get(cid) else {
                    continue;
                };
                let other = if c.lits[0] == tail {
                    c.lits[1]
                } else {
                    c.lits[0]
                };
                self.clauses.add_original([t, other]);
            }
            // Retire with full hygiene: BIG-edge purge, reason re-pointing,
            // watcher removal, DRAT deletion line, and the live counters
            // (`remove_clause`, unlike the raw `retire_clause`, keeps
            // `num_original` exact — schedules key on it).
            for &cid in &group {
                self.remove_clause(cid);
            }
            // Re-mark the touched variables for the eliminator: the
            // partners each occur in one fewer original now.
            let mut touched: SmallVec<[Lit; 24]> = SmallVec::new();
            touched.push(tail);
            touched.push(t);
            touched.push(t.negate());
            for &cid in &group {
                if let Some(c) = self.clauses.get(cid) {
                    touched.extend(c.lits.iter().copied());
                }
            }
            self.mark_elim_vars(touched.iter().copied());
            introduced += 1;
            self.stats.bva_introduced += 1;
        }
        introduced
    }

    /// Pre-search one-shot (see the module doc).  Returns
    /// `(vars_introduced, literals_saved)`.
    pub(super) fn structured_bva(&mut self) -> (usize, i64) {
        let null_arm = std::env::var("NIXIE_SBVA_NULL").is_ok();
        let mut opts = BvaOpts::presearch();
        opts.null_arm = null_arm;
        self.structured_bva_with(opts)
    }

    /// Mid-search inprocessing-round slice: effort budgets from the round's
    /// window when scheduled (window > 0), legacy caps otherwise.  The null
    /// arm comes from `config.mid_bva_null`.  The caller owns the
    /// watch/BIG rebuild and re-propagation when this returns
    /// `introduced > 0`.
    pub(super) fn structured_bva_mid(&mut self) -> (usize, i64) {
        let (entries, intros) = if self.inproc_budgets.window > 0 {
            (
                (self.inproc_budgets.bva_entries as usize).clamp(200_000, MAX_PAIR_INDEX_ENTRIES),
                (self.inproc_budgets.bva_intros as usize).clamp(50, 10_000),
            )
        } else {
            (MAX_PAIR_INDEX_ENTRIES, MAX_INTRODUCTIONS)
        };
        let opts = BvaOpts {
            max_entries: entries,
            max_intros: intros,
            null_arm: self.config.mid_bva_null,
            mid_search: true,
        };
        self.structured_bva_with(opts)
    }

    /// Shared body (see the module doc for the encoding proof).
    fn structured_bva_with(&mut self, opts: BvaOpts) -> (usize, i64) {
        if self.trail.decision_level() != 0
            || self.proof.is_some()
            || self.lrat
            || self.real_theory_attached
            || self.assertion_levels.len() > 1
            || self.trivially_unsat
        {
            return (0, 0);
        }

        // ---- 1. Candidate generation: pair index over original clauses.
        // For each unordered literal pair, the original clauses containing
        // both.  A mergeable group is a subset of one pair's list whose
        // full intersection `G` (⊇ the pair by construction) is beneficial.
        let mut pair_index: std::collections::HashMap<(u32, u32), SmallVec<[ClauseId; 8]>> =
            std::collections::HashMap::default();
        let mut entries = 0usize;
        'outer: for cid in self.clauses.iter_ids() {
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
                    if entries > opts.max_entries {
                        break 'outer;
                    }
                    pair_index
                        .entry((codes[a], codes[b]))
                        .or_default()
                        .push(cid);
                }
            }
        }

        // Deterministic iteration order over the index (HashMap iteration
        // is per-process random; see the module doc's determinism note).
        let mut pair_keys: Vec<&(u32, u32)> = pair_index.keys().collect();
        pair_keys.sort_unstable();

        // ---- 2. Collect beneficial candidates.
        let mut candidates: Vec<Candidate> = Vec::new();
        for key in pair_keys {
            let ids = &pair_index[key];
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
            // Drop clauses whose remainder is empty (C_i == G stays as-is
            // and must NOT be retired; it does not join the merge).
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
        }

        if candidates.is_empty() {
            return (0, 0);
        }

        // ---- 3. Rank: best-saving first (treatment) or scrambled (null).
        for c in &mut candidates {
            c.order_key = if opts.null_arm {
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
            if introduced >= opts.max_intros {
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
            // Mid-search hygiene (a): never retire a clause the trail still
            // records as a propagation reason — level-0 facts can carry
            // original-clause reasons, and conflict analysis resolving
            // against a retired clause is unsound.
            if opts.mid_search
                && group
                    .iter()
                    .any(|(cid, lits)| self.is_live_reason_clause(*cid, lits))
            {
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
                if opts.mid_search {
                    // Hygiene (b): re-mark the touched variables so the
                    // scheduled eliminator re-examines them (occurrence
                    // machinery rebuilds from the live DB).
                    self.mark_elim_vars(lits.iter().copied().chain(rest.iter().copied()));
                }
                // Pre-search at level 0 with no reasons on untouched
                // originals: a raw delete is exact there (no BIG edges —
                // members are ≥3-lit — and no reasons reference a clause
                // never yet watched).  Mid-search, reason-members were
                // skipped above and watches are rebuilt by the caller.
                self.clauses.remove(*cid);
            }
            introduced += 1;
            total_saving += cand.saving;
            if opts.mid_search {
                self.stats.bva_introduced += 1;
                self.mark_elim_vars(base.iter().copied());
            }
        }

        // ---- 5. Watches/BIG are stale for every touched clause: the
        // pre-search slice rebuilds here; the mid-search slice's caller
        // owns the rebuild (one per round, shared with other passes).
        if introduced > 0 && !opts.mid_search {
            self.rebuild_watches_and_binary_graph();
        }
        (introduced, total_saving)
    }
}

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
