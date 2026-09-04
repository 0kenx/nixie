//! Binary-chain factoring — first slice of the kissat `factor.c` port.
//!
//! The transformation (verified equisatisfiable and model-preserving by a
//! direct argument, pinned by unit tests and the corpus differential): for
//! a literal `f` with binary clauses `(f ∨ q_i)` and a *second* literal
//! `g` such that every matched `q_i` also occurs in a **distinct kept**
//! clause `(q_i ∨ g)`, replace the deleted set with
//!
//! * dividers `(x ∨ f)` and `(x ∨ g)` for a fresh auxiliary `x`, and
//! * quotients `(¬x ∨ q_i)` — one per matched binary,
//!
//! keeping the `(q_i ∨ g)` witnesses untouched.
//!
//! * new → old: `x = F` forces `f ∧ g` (every deleted original satisfied
//!   through `f`, every witness through `g`); `x = T` forces every `q_i`
//!   (each deleted original satisfied through `q_i`, each witness through
//!   `q_i`).
//! * old → new: a model with `f ∧ g` extends with `x = F`; a model with
//!   `¬f` forces every `q_i` (unit originals) — extend with `x = T`; a
//!   model with `f ∧ ¬g` forces every `q_i` through the unit witnesses
//!   `(q_i ∨ g)` — again `x = T`.  Every case extends.
//!
//! The witness polarity is load-bearing: `(¬g ∨ q_i)` instead of
//! `(q_i ∨ g)` makes the `f ∧ ¬g` case unextendable (an unsound rewrite —
//! the corpus A/B caught 18 sat→unsat flips with that direction before
//! anything landed).  The witness must also be a **different clause** than
//! the quotient binary: a clause witnesses itself exactly when `g = ¬f`
//! (the clause `(f ∨ q)` reads as `(q ∨ g)` with `g = ¬f`... only in the
//! degenerate `t == f` adjacency entry), excluded by the `t == f` guard.
//!
//! Economics (kissat's occurrence accounting): `k` quotient binaries carry
//! `2k` factor-side occurrences (`f`'s watch side and `g`'s implication
//! side); the rewrite leaves `k + 2` (the quotients on `¬x` plus the two
//! dividers) — the reduction is `k − 2`, so the pass fires at `k ≥ 3`
//! (kissat `best_quotient` with `bound = 0`).
//!
//! This is the worker_550 lever: kissat's `--factor=0` knockout on that
//! instance measures 2 003 → 43 083 conflicts (21.5×), with 51 466
//! variables (55 %) factored; every other probe sub-pass is neutral or
//! counterproductive there.  worker_550 is 97 % binary and carries, with
//! shuffling-2, almost the entire standing conflicts-to-verdict geomean
//! gap (1.332× → ~1.08× without those two files).
//!
//! Slice gates (mirroring `bva.rs`): one-shot pre-search, decision level
//! 0, base scope only, no attached proof/LRAT tracer, no real theory,
//! deterministic budgets.  Default off (`SolverConfig::enable_factoring`).
//!
//! Divergences from `factor.c` (recorded): no chain refinement beyond one
//! `g` per `f` (kissat refines quotient chains by co-occurrence counting
//! with hop scores), no large-clause factoring (kissat matches same-size
//! clauses through minimal watch lists), candidates ranked by partner
//! count only.  The binary chain is the measured worker_550 case.

use crate::literal::Lit;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;

use super::Solver;

/// Maximum fresh variables introduced per pass (bva precedent).
const MAX_INTRODUCTIONS: usize = 100_000;
/// Deterministic work budget: total adjacency-list entries visited while
/// counting next-factor candidates.  Guards pathological dense instances.
const MAX_EDGE_VISITS: u64 = 400_000_000;

/// Env override for the edge-visit budget (diagnostics: measures whether
/// the pass volume is budget-limited or structurally limited).
fn edge_visit_budget() -> u64 {
    std::env::var("NIXIE_FACTOR_BUDGET")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(MAX_EDGE_VISITS)
}
/// Fixpoint rounds per pass (each round re-scans candidates over the
/// rewritten binary structure; kissat achieves the same by re-arming
/// candidates inside one pass).
const FACTOR_MAX_ROUNDS: u32 = 4;

impl Solver {
    /// One factoring pass over the binary structure.  Returns
    /// `(introductions, occurrence_reduction)`.
    pub(super) fn factor_binaries(&mut self) -> (usize, i64) {
        if self.trail.decision_level() != 0
            || self.proof.is_some()
            || self.lrat
            || self.real_theory_attached
            || self.assertion_levels.len() > 1
            || self.trivially_unsat
        {
            return (0, 0);
        }
        if self.propagate().is_some() {
            self.trivially_unsat = true;
            return (0, 0);
        }

        let mut introduced = 0usize;
        let mut reduction_total: i64 = 0;
        let edge_budget = edge_visit_budget();
        let mut edge_visits: u64 = 0;
        let mut budget_hit = false;
        let mut fresh_vars: SmallVec<[crate::literal::Var; 64]> = SmallVec::new();
        // Fixpoint rounds: each round's quotients `(not-x v q_i)` are new
        // binaries on `not-x` and re-arm candidates for the next round
        // (kissat re-arms inside one pass via `update_candidate`; rounds are
        // the slice's equivalent).  Bounded by FACTOR_MAX_ROUNDS.
        let max_rounds: u32 = std::env::var("NIXIE_FACTOR_ROUNDS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(FACTOR_MAX_ROUNDS);
        let do_bump = std::env::var("NIXIE_FACTOR_BUMP").is_ok();
        // Literals introduced by THIS pass (the fresh `x`s): re-factoring a
        // quotient `(¬x ∨ q_i)` against its own old witness `g` rewrites an
        // isomorphic structure with no gain — the degenerate churn guard
        // kissat avoids by clearing each literal's factor flag once
        // processed.
        let mut self_introduced: rustc_hash::FxHashSet<u32> = rustc_hash::FxHashSet::default();
        for _round in 0..max_rounds {
            let mut round_introduced = 0usize;

            // ---- 1. Candidate literals by live-binary partner count.
            // Clauses `(f ∨ q)` are BIG edges `¬f → q`.  Recomputed per round:
            // the previous round's quotients are new binaries that re-arm
            // candidates (kissat re-arms touched literals inside one pass via
            // `update_candidate`).
            let mut cands: Vec<(u32, u32)> = Vec::new(); // (count, literal code)
            for code in 0..(self.num_vars * 2) as u32 {
                let f = Lit::from_code(code);
                let mut n = 0u32;
                // No per-entry clause dereference: the pass maintains the
                // invariant that BIG entries reference live binary clauses
                // (parse-time registration + incremental purge on this
                // pass's deletions); the random-access arena lookups
                // dominated the scan cost (~20x kissat's per-tick rate).
                for (q, _cid) in self.binary_graph.get(f.negate()) {
                    if q.var() != f.var() && !self.trail.is_assigned(q.var()) {
                        n += 1;
                    }
                }
                if n >= 3 {
                    cands.push((n, code));
                }
            }
            // Descending partner count; ascending literal code tie-break.
            cands.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)));

            for &(_, fcode) in &cands {
                if introduced >= MAX_INTRODUCTIONS || budget_hit {
                    break;
                }
                let f = Lit::from_code(fcode);
                if self.trail.is_assigned(f.var()) || self_introduced.contains(&fcode) {
                    continue;
                }

                // ---- 2. Quotient set: live binaries `(f ∨ q)`, edges `¬f → q`.
                let quotients: Vec<(Lit, crate::clause::ClauseId)> = self
                    .binary_graph
                    .get(f.negate())
                    .iter()
                    .filter(|(q, _)| q.var() != f.var() && !self.trail.is_assigned(q.var()))
                    .map(|(q, cid)| (*q, *cid))
                    .collect();
                if quotients.len() < 3 {
                    continue;
                }

                // ---- 3. Count next-factor candidates `g`: an adjacency entry
                // `¬q → t` IS the clause `(q ∨ t)` (kissat matches the binary
                // `(q ∨ next)` directly on `q`'s watch list) — the witness is
                // `(q ∨ g)` with `g = t`, NOT `(¬g ∨ q)`.  The polarity is
                // load-bearing: with witness `(q_i ∨ g)`, a model with
                // `f ∧ ¬g` has every witness unit (`g` false forces `q_i`),
                // so `x = T` extends it — the flipped witness direction is
                // UNSOUND (a `f ∧ ¬g ∧ ¬q_j` model satisfies originals and
                // witnesses but has no `x` extension; caught by the corpus
                // A/B's 18 sat→unsat flips before landing).  `t == f` is the
                // quotient clause itself (self-witnessing) — excluded, as is
                // a tautological witness (`t == ¬q`) and same-variable noise.
                let mut count: FxHashMap<u32, Vec<(Lit, crate::clause::ClauseId)>> =
                    FxHashMap::default();
                'quot: for (q, qcid) in &quotients {
                    for (t, wcid) in self.binary_graph.get(q.negate()) {
                        edge_visits += 1;
                        if edge_visits > edge_budget {
                            budget_hit = true;
                            break 'quot;
                        }
                        if *t == f || t.var() == q.var() || t.var() == f.var() {
                            continue;
                        }
                        if *wcid == *qcid {
                            continue; // witness must differ from the quotient
                        }
                        count.entry(t.code()).or_default().push((*q, *wcid));
                    }
                }
                if count.is_empty() {
                    continue;
                }

                // Best `g`: most matched distinct partners, lowest literal code
                // on ties — independent of hash iteration order.
                let mut best_k = 0usize;
                let mut best_g: Option<u32> = None;
                for (gcode, bins) in &count {
                    let mut seen: SmallVec<[usize; 16]> = SmallVec::new();
                    let mut k = 0usize;
                    for (q, _) in bins {
                        if !seen.contains(&q.var().index()) {
                            seen.push(q.var().index());
                            k += 1;
                        }
                    }
                    if k > best_k || (k == best_k && best_g.is_some_and(|b| *gcode < b)) {
                        best_k = k;
                        best_g = Some(*gcode);
                    }
                }
                if best_k < 3 {
                    continue;
                }
                let gcode = best_g.unwrap_or(u32::MAX);
                let g = Lit::from_code(gcode);
                // `g == ¬f` cannot occur (`t == f` excluded); defensive re-check.
                debug_assert!(g != f.negate());
                if g == f.negate() || g.var() == f.var() {
                    continue;
                }

                // ---- 4. Apply.  Group members re-resolved against the live
                // DB (earlier introductions in this pass may have retired a
                // clause): the quotient clause id comes from the edge `¬f → q`.
                let bins = count.remove(&gcode).unwrap_or_default();
                let mut seen: SmallVec<[usize; 16]> = SmallVec::new();
                let mut group: Vec<(Lit, crate::clause::ClauseId)> = Vec::with_capacity(best_k);
                for (q, _wcid) in &bins {
                    if seen.contains(&q.var().index()) {
                        continue;
                    }
                    seen.push(q.var().index());
                    let Some(qcid) = self
                        .binary_graph
                        .get(f.negate())
                        .iter()
                        .find_map(|(l, cid)| (*l == *q).then_some(*cid))
                    else {
                        continue;
                    };
                    let live = self.clauses.get(qcid).is_some_and(|c| {
                        !c.deleted && c.lits.len() == 2 && c.lits.contains(&f) && c.lits.contains(q)
                    });
                    if live {
                        group.push((*q, qcid));
                    }
                }
                if group.len() < 3 {
                    continue;
                }

                let x = Lit::pos(self.new_var());
                fresh_vars.push(x.var());
                self_introduced.insert(x.code());
                self_introduced.insert(x.negate().code());
                // Incremental BIG maintenance (kissat connects new binaries
                // to the watches immediately, which is what lets its pass —
                // and our fixpoint rounds — match the NEW quotients
                // `(¬x ∨ q_i)` as witnesses for other candidates; with a
                // single end-of-pass rebuild they are invisible mid-pass
                // and the rounds stall after round 1).
                let add_bin = |s: &mut Solver, a: Lit, b: Lit| {
                    let cid = s.clauses.add_original([a, b]);
                    s.binary_graph.add(a.negate(), b, cid);
                    s.binary_graph.add(b.negate(), a, cid);
                    cid
                };
                add_bin(self, x, f);
                add_bin(self, x, g);
                for (q, qcid) in &group {
                    add_bin(self, x.negate(), *q);
                    // Pre-search at level 0, nothing watched yet: raw delete
                    // is exact for the arena (the bva precedent); the BIG
                    // edges of the quotient binary are purged by id.
                    self.binary_graph.remove_clause_edges(f.negate(), *qcid);
                    self.binary_graph.remove_clause_edges(q.negate(), *qcid);
                    self.clauses.remove(*qcid);
                }
                introduced += 1;
                round_introduced += 1;
                reduction_total += group.len() as i64 - 2;
            }

            #[cfg(feature = "std")]
            if std::env::var("NIXIE_FACTOR_TRACE").is_ok() {
                let cand3 = cands.iter().filter(|c| c.0 >= 3).count();
                eprintln!(
                    "factor_round: cands={} cand3={} round_introduced={} total={}",
                    cands.len(),
                    cand3,
                    round_introduced,
                    introduced
                );
            }
            if round_introduced == 0 {
                break;
            }
        } // rounds

        if introduced > 0 {
            self.rebuild_watches_and_binary_graph();
            // kissat `adjust_scores_and_phases_of_fresh_variables`: fresh
            // variables are moved to the FRONT of the decision queue (and
            // score-unbumped) — deciding `x = T` early fires the quotient
            // propagations that are the point of the rewrite.  Our
            // equivalent: one strong hint bump across every heuristic.
            if do_bump {
                self.bump_decision_hint(&fresh_vars);
            }
            // Dominant-activity variant of the queue-front hypothesis: the
            // fresh variables outrank every conflict-bumped variable for a
            // long horizon (O(1) per decision, unlike `domain_priority`'s
            // O(|priority|) scan which alone exceeds the cap on
            // worker-class DBs).
            if let Ok(n) = std::env::var("NIXIE_FACTOR_BUMPN")
                && let Ok(times) = n.parse::<u32>()
            {
                for &v in &fresh_vars {
                    self.bump_var_activity(v, times);
                }
            }
            // kissat's literal queue-front semantics: `adjust_scores_and_
            // phases_of_fresh_variables` moves fresh variables to the FRONT
            // of its decision queue.  Our equivalent of "decide these
            // first, unconditionally" is `domain_priority` (the bump above
            // only raises VSIDS activity and measured harmful on worker_550;
            // the queue-front is the hypothesis under test).
            if std::env::var("NIXIE_FACTOR_PRIORITY").is_ok() {
                let mut pri = core::mem::take(&mut self.domain_priority);
                pri.extend(fresh_vars.iter().copied());
                self.domain_priority = pri;
            }
        }
        (introduced, reduction_total)
    }
}
