//! Transitive reduction of the binary implication graph — a port of CaDiCaL
//! `transred.cpp`.
//!
//! A binary clause `(¬src ∨ dst)` is **transitively redundant** when the
//! implication `src → dst` also holds along a different path through the
//! binary implication graph; the clause can then be retired. This is the
//! documented amortizer for hyper-binary resolution, which otherwise
//! "has the risk to produce too many hyper binary resolvents" (cadical's
//! own words) — the most probable missing piece behind this repo's
//! full-inprocessing-stack-as-default rejections.
//!
//! # Soundness rules (each from cadical's source or the inprocessing-rules
//! paper it cites)
//!
//! * **Original candidates use original-only paths.** An irredundant
//!   (original) binary may only be proven transitive through *other
//!   irredundant* binaries: a path through a learned clause justifies
//!   deletion only while that learned clause lives, and learned clauses
//!   are removed by database reduction — deleting an original on such a
//!   transient justification under-constrains the formula (the same class
//!   as the subsume-promotion bugs fixed earlier: the subsumer of an
//!   original must carry the obligation permanently).
//! * **The candidate's own edge is excluded** from the alternative-path
//!   search (`if (d == c) continue`).
//! * **Hyper-derived binaries are not candidates**: they arrive in bulk,
//!   are mostly reduced away, and were non-transitive at creation.
//! * **Failed literals**: if the BFS from `src` reaches both `x` and `¬x`,
//!   `src` is failed — `¬src` is forced as a level-0 unit (and the scan
//!   re-propagates).
//! * Retirements go through [`Solver::retire_clause`] (BIG-edge purge +
//!   live-reason re-pointing), per the deleted-reason hygiene rules.
//!
//! Scheduling: cadical runs transred inside `inprobe` on an
//! effort-per-mille-of-search-ticks budget with a per-clause `transred`
//! checked-flag (reset wholesale once every candidate has been examined);
//! this port runs one budgeted round per `inprocess()` invocation.

use super::*;

/// cadical `transredeffort` (per-mille of search ticks as the budget).
const TRANSRED_EFFORT_PERMILLE: u64 = 100;
/// cadical `transredmineff` / `transredmaxeff`.
const TRANSRED_MIN_EFFORT: u64 = 1_000_000;
const TRANSRED_MAX_EFFORT: u64 = 1_000_000_000;

impl Solver {
    /// One transitive-reduction round. Returns `(removed, failed)`.
    pub(super) fn transred_round(&mut self) -> (usize, usize) {
        if self.trail.decision_level() != 0 || self.trivially_unsat || self.lrat {
            return (0, 0);
        }
        if self.propagate().is_some() {
            self.trivially_unsat = true;
            return (0, 0);
        }

        let ticks = self.ticks_focused + self.ticks_stable;
        // Effort-scheduled rounds (2026-09-07): cadical's window form —
        // `transredeffort` (100‰) of the search work since the last round,
        // in this round's step budget, instead of the cumulative-tick form.
        let budget = if self.inproc_budgets.window > 0 {
            self.inproc_budgets.transred_steps
        } else {
            (ticks.saturating_mul(TRANSRED_EFFORT_PERMILLE) / 1000)
                .clamp(TRANSRED_MIN_EFFORT, TRANSRED_MAX_EFFORT)
        };
        let mut steps: u64 = 0;

        // Candidate list: live, non-hyper, unchecked binaries whose literals
        // are still unassigned at level 0.
        let n = self.clauses.num_slots();
        self.clause_transred_checked.resize(n, false);
        self.clause_hyper.resize(n, false);
        let mut candidates: Vec<ClauseId> = Vec::new();
        let mut any_unchecked = false;
        for idx in 0..n {
            let id = ClauseId::new(idx as u32);
            let Some(c) = self.clauses.get(id) else {
                continue;
            };
            if c.deleted || c.lits.len() != 2 {
                continue;
            }
            any_unchecked |= !self.clause_transred_checked[idx];
            if self.clause_transred_checked[idx] || self.clause_hyper[idx] {
                continue;
            }
            candidates.push(id);
        }
        if !any_unchecked {
            // Every binary has been checked: reset wholesale (cadical's
            // rescheduling sweep) so future rounds re-examine.
            for f in &mut self.clause_transred_checked {
                *f = false;
            }
            candidates.clear();
            for idx in 0..n {
                let id = ClauseId::new(idx as u32);
                let Some(c) = self.clauses.get(id) else {
                    continue;
                };
                if !c.deleted && c.lits.len() == 2 && !self.clause_hyper[idx] {
                    self.clause_transred_checked[idx] = false;
                    candidates.push(id);
                }
            }
        }

        let num_lits = 2 * self.num_vars.max(1);
        // Signed marks: +1 = reachable from src, -1 = its negation is.
        let mut mark: Vec<i8> = vec![0; num_lits];
        let mut work: Vec<u32> = Vec::new();
        let (mut removed, mut failed) = (0usize, 0usize);

        'cand: for id in candidates {
            if self.trivially_unsat || steps >= budget {
                break;
            }
            // Re-validate under the current state (units forced this round,
            // clauses retired this round).
            let Some(c) = self
                .clauses
                .get(id)
                .filter(|c| !c.deleted && c.lits.len() == 2)
            else {
                continue;
            };
            let idx = id.index();
            self.clause_transred_checked[idx] = true;
            let (a, b) = (c.lits[0], c.lits[1]);
            let learned = c.learned;
            // Candidate edge: src → dst (clause (¬src ∨ dst) ≡ (a ∨ b) with
            // src = ¬a, dst = b). Skip if either endpoint is assigned.
            if self.trail.is_assigned(a.var()) || self.trail.is_assigned(b.var()) {
                continue;
            }
            // Two searches prove transitivity of the edge src→dst:
            // forward from `src`, or mirrored from `¬dst` (paths in the
            // BIG respect negation symmetry). Start the BFS from whichever
            // frontier is smaller (cadical's direction heuristic).
            let (fwd, mir) = (
                Lit::from_code(a.negate().code()),
                Lit::from_code(b.negate().code()),
            );
            let (src, dst) = if self.binary_graph.get(mir).len() < self.binary_graph.get(fwd).len()
            {
                (mir, a)
            } else {
                (fwd, b)
            };

            mark[src.code() as usize] = 1;
            work.clear();
            work.push(src.code());
            let mut transitive = false;
            let mut failed_lit: Option<u32> = None;
            let mut j = 0usize;
            while !transitive && failed_lit.is_none() && j < work.len() && steps < budget {
                let lit_code = work[j];
                j += 1;
                let lit = Lit::from_code(lit_code);
                let edges: SmallVec<[(Lit, ClauseId); 8]> =
                    self.binary_graph.get(lit).iter().copied().collect();
                for (other, cid) in edges {
                    steps += 1;
                    if cid == id {
                        continue; // the candidate's own edge
                    }
                    let Some(d) = self.clauses.get(cid) else {
                        continue;
                    };
                    if d.deleted {
                        continue; // stale edge (defensive; purged on retire)
                    }
                    if !learned && d.learned {
                        continue; // original-only paths for original candidates
                    }
                    let oc = other.code() as usize;
                    if other == dst {
                        transitive = true;
                        break;
                    }
                    match mark[oc] {
                        1 => continue, // already reachable
                        -1 => {
                            // both `other` and `¬other` reachable from src:
                            // src is a failed literal.
                            failed_lit = Some(src.code());
                            break;
                        }
                        _ => {
                            mark[oc] = 1;
                            mark[other.negate().code() as usize] = -1;
                            work.push(oc as u32);
                        }
                    }
                }
            }
            // Unmark (both the reached literals and their negations).
            for &wc in &work {
                mark[wc as usize] = 0;
                mark[(wc ^ 1) as usize] = 0;
            }
            work.clear();

            if transitive {
                self.retire_clause(id);
                self.stats.deleted_clauses += 1;
                removed += 1;
                continue 'cand;
            }
            if let Some(fc) = failed_lit {
                let flit = Lit::from_code(fc);
                failed += 1;
                self.force_level0(flit.negate());
                if self.trivially_unsat {
                    return (removed, failed);
                }
                if self.propagate().is_some() {
                    self.trivially_unsat = true;
                    return (removed, failed);
                }
            }
        }

        (removed, failed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a solver with `n` vars and the given DIMACS clauses.
    fn solver_with(n: usize, clauses: &[&[i32]]) -> Solver {
        let mut s = Solver::new();
        for _ in 0..n {
            s.new_var();
        }
        for c in clauses {
            s.add_clause_dimacs(c);
        }
        s
    }

    /// `a→b→c` plus a direct `a→c`, all original: the direct edge is
    /// transitively redundant via an original-only path and must be
    /// retired; the chain edges must survive.
    #[test]
    fn transitive_original_edge_retired_via_original_path() {
        let mut s = solver_with(3, &[&[-1, 2], &[-2, 3], &[-1, 3]]);
        let (removed, failed) = s.transred_round();
        assert_eq!(failed, 0);
        assert_eq!(removed, 1, "exactly the direct a→c edge is transitive");
        // (¬a∨c) retired; (¬a∨b) and (¬b∨c) live.
        let live: Vec<Vec<i32>> = s
            .clauses
            .iter_ids()
            .filter_map(|id| s.clauses.get(id))
            .filter(|c| !c.deleted)
            .map(|c| c.lits.iter().map(|l| l.to_dimacs()).collect())
            .collect();
        assert!(
            live.contains(&vec![-1, 2]),
            "chain edge a→b survives: {live:?}"
        );
        assert!(
            live.contains(&vec![-2, 3]),
            "chain edge b→c survives: {live:?}"
        );
        assert!(!live.contains(&vec![-1, 3]), "direct a→c retired: {live:?}");
    }

    /// Original `a→c` whose only alternative path runs through LEARNED
    /// binaries (`a→d`, `d→c`): must NOT be retired (a learned
    /// justification is transient; deleting the original on it
    /// under-constrains the formula — the inprocessing-rules restriction).
    #[test]
    fn original_not_retired_via_learned_path() {
        let mut s = solver_with(4, &[&[-1, 3]]);
        // Learned binaries a→d and d→c, wired like `learn_clause` does.
        let d1 = s
            .clauses
            .add_learned([Lit::from_dimacs(-1), Lit::from_dimacs(4)]);
        s.binary_graph
            .add(Lit::from_dimacs(1), Lit::from_dimacs(4), d1);
        s.binary_graph
            .add(Lit::from_dimacs(-4), Lit::from_dimacs(-1), d1);
        let d2 = s
            .clauses
            .add_learned([Lit::from_dimacs(-4), Lit::from_dimacs(3)]);
        s.binary_graph
            .add(Lit::from_dimacs(4), Lit::from_dimacs(3), d2);
        s.binary_graph
            .add(Lit::from_dimacs(-3), Lit::from_dimacs(-4), d2);
        let (removed, failed) = s.transred_round();
        assert_eq!(failed, 0);
        assert_eq!(
            removed, 0,
            "an original edge is not transitive through learned clauses"
        );
        let live = s
            .clauses
            .iter_ids()
            .filter_map(|id| s.clauses.get(id))
            .filter(|c| !c.deleted && !c.learned)
            .count();
        assert_eq!(live, 1, "the original (¬a∨c) survives");
    }

    /// Failed-literal detection: from the probe literal, reaching both `x`
    /// and `¬x` (via distinct edges, neither being the candidate's own)
    /// fails it and forces its negation. The instance is built so the
    /// direction heuristic (start from the smaller out-degree frontier)
    /// provably picks `¬a`: out(¬a) = out(¬b) = 3 and the tie keeps the
    /// forward search.
    #[test]
    fn failed_literal_from_reachable_complement_pair() {
        let mut s = solver_with(
            6,
            // BIG edges (clause (¬s∨d) = s→d, keyed by s):
            //   a→b, a→x, a→¬x   (a reaches a complement pair)
            //   ¬b→p, ¬b→q, ¬b→y (balances out-degree so the direction
            //                     heuristic keeps the forward search from a)
            // 1=a, 2=b, 3=x, 4=p, 5=q, 6=y.
            &[&[-1, 2], &[-1, 3], &[-1, -3], &[2, 4], &[2, 5], &[2, 6]],
        );
        let (removed, failed) = s.transred_round();
        assert_eq!(removed, 0);
        assert_eq!(failed, 1, "a reaches both x and ¬x: a is failed");
        assert_eq!(
            s.trail.lit_value(Lit::from_dimacs(-1)),
            crate::literal::LBool::True,
            "¬a forced true as a level-0 unit (negation of the failed a)"
        );
    }
}
