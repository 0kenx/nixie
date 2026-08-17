//! Global forward subsumption with strengthening (port of CaDiCaL `subsume.cpp`).
//!
//! For every scheduled clause `c` (ascending size) we look for an already
//! *connected* clause `d` (smaller or equal size) whose literals all occur in
//! `c` – then `c` is subsumed and deleted – or that occur in `c` except for
//! exactly one complementary literal – then that literal is removed from `c`
//! (self-subsuming resolution).  After a clause has been checked (and neither
//! subsumed nor strengthened) it is *connected* into the one-watched
//! occurrence list of its least-occurring literal, so later (larger)
//! candidates can find it as a subsumer.
//!
//! This replaces the previous O(N²·L²) pairwise scan
//! (`Preprocessor::subsumption_elimination`), which could not be scheduled
//! mid-search at all: on `stable-300-0.1-20` (17.5k clauses) one round of it
//! exceeded any reasonable conflict interval, while CaDiCaL runs an
//! occurrence-driven round every ~2k conflicts and credits it with 46 %
//! subsumed clauses on that instance.
//!
//! Differences from CaDiCaL, deliberately:
//! * no `subsume` dirty-bit filtering of which clauses need re-checking
//!   (rebuild the schedule every round; the budget bounds the work);
//! * binaries are matched through the existing [`BinaryImplicationGraph`]
//!   instead of CaDiCaL's dedicated per-literal arrays;
//! * no `transred` (transitive reduction of the binary implication graph).
//!
//! Runs at decision level 0 only, like every inprocessing pass.

use super::*;
use crate::clause::{ClauseId, ClauseTier};

/// Outcome of one subsumption check of candidate `c` against connected `d`.
enum SubCheck {
    /// Every literal of `d` occurs in `c`: `c` is subsumed by `d`.
    Subsumed { subsumer: ClauseId },
    /// All but one literal of `d` occur in `c`, and that one occurs
    /// complemented: remove `remove` from `c` (self-subsuming resolution).
    Strengthen { remove: Lit },
}

impl Solver {
    /// One forward-subsumption round over the live clause database.
    ///
    /// Returns `(subsumed, strengthened)` counts.  Sound at any assertion
    /// scope (a subsumed clause is entailed by its subsumer; a strengthened
    /// clause is entailed by resolution), but only runs at decision level 0.
    /// Skipped entirely while an LRAT tracer is attached, like the rest of
    /// `inprocess` (strengthening's hypothetical-probe derivation is not
    /// threaded through the tracer).
    pub(super) fn subsume_round(&mut self) -> (usize, usize) {
        if self.trail.decision_level() != 0 || self.lrat || self.trivially_unsat {
            return (0, 0);
        }

        // Budget (cadical `subsumelimited`): delta = search propagations ×
        // subsumeeffort/1000 (= ×1), clamped to [2·active vars, 1e8] checks.
        let budget: u64 = self
            .stats
            .propagations
            .clamp((2 * self.num_vars.max(1)) as u64, 100_000_000);
        let mut subchecks: u64 = 0;

        // Snapshot the schedule: live clauses within the size limit and with
        // no level-0-fixed literal, sorted ascending by size so smaller
        // (potential subsumers) are connected first.
        const CLS_LIMIT: usize = 100; // cadical subsumeclslim
        let mut schedule: Vec<(u32, ClauseId)> = Vec::new();
        let mut has_candidate = false;
        for cid in self.clauses.iter_ids() {
            let Some(c) = self.clauses.get(cid) else {
                continue;
            };
            if c.deleted || c.lits.len() > CLS_LIMIT || c.lits.len() < 3 {
                continue;
            }
            // Learned clauses: only those worth keeping participate (cadical
            // `likely_to_be_kept_clause`): Core/Mid tier or low glue.  Local
            // tier (deleted en masse at every reduction) is not worth the
            // scheduling cost.
            if c.learned && matches!(c.tier, ClauseTier::Local) && c.lbd > 8 {
                continue;
            }
            // Skip clauses with a level-0 assigned literal: they are either
            // satisfied (nothing to do) or falsified-to-a-suffix (handled by
            // propagation), and skipping keeps the check assignment-free.
            if c.lits.iter().any(|&l| self.trail.lit_val(l) != 0) {
                continue;
            }
            schedule.push((c.lits.len() as u32, cid));
            has_candidate = true;
        }
        if !has_candidate {
            return (0, 0);
        }
        schedule.sort_unstable_by_key(|&(size, _)| size);

        // One-watched occurrence lists over clause ids, by literal code.
        let num_lits = 2 * self.num_vars;
        let mut occs: Vec<SmallVec<[ClauseId; 4]>> = vec![SmallVec::new(); num_lits];

        // Signed marks over literal codes: 0 = unmarked, +pos/-neg.
        let mut mark: Vec<i8> = vec![0; num_lits];

        let mut subsumed = 0usize;
        let mut strengthened = 0usize;

        for &(_, cid) in &schedule {
            if subchecks >= budget || self.trivially_unsat {
                break;
            }
            let lits: SmallVec<[Lit; 8]> = match self.clauses.get(cid) {
                Some(c) if !c.deleted && c.lits.len() >= 3 => c.lits.iter().copied().collect(),
                _ => continue,
            };

            // Signed-mark the candidate's literals: `l ∈ c` marks +1 on
            // `l.code()` and -1 on `l.negate().code()`, so a connected clause
            // literal `d` reads mark +1 iff `d ∈ c` and -1 iff `¬d ∈ c`.
            for &l in &lits {
                mark[l.code() as usize] = 1;
                mark[l.negate().code() as usize] = -1;
            }

            let mut outcome: Option<SubCheck> = None;

            'candidate: for &l in &lits {
                // Binary fast path.  An edge `¬l → other` in the binary
                // implication graph is the clause `D = (l ∨ other)` (when `¬l`
                // becomes false, `other` is forced true).  Since `l ∈ c` is
                // marked, `D ⊆ c` holds iff `other` is marked +, and `D`
                // self-subsumes `c` iff `¬other` is marked - (resolve `¬other`
                // away).  NOTE the lookup key is `l.negate()`: edges keyed
                // under `l` itself encode `(¬l ∨ other)`, which cannot be a
                // subset of `c` at all – reading them was a false-subsumption
                // bug that deleted live clauses and flipped UNSAT to SAT.
                for &(other, bin_id) in self.binary_graph.get(l.negate()) {
                    // A binary-graph edge may outlive its clause (deletion
                    // paths that don't scrub the graph). Subsuming against a
                    // dead edge deletes live clauses on the word of a clause
                    // the formula no longer contains.
                    if self.clauses.get(bin_id).is_none_or(|c| c.deleted) {
                        continue;
                    }
                    let m = mark[other.code() as usize];
                    if m > 0 {
                        outcome = Some(SubCheck::Subsumed { subsumer: bin_id });
                        break 'candidate;
                    }
                    if m < 0 {
                        // `¬other ∈ c`: remove it.
                        outcome = Some(SubCheck::Strengthen {
                            remove: other.negate(),
                        });
                        break 'candidate;
                    }
                }

                // Longer connected clauses.
                for &did in occs[l.code() as usize].iter() {
                    let Some(d) = self.clauses.get(did) else {
                        continue;
                    };
                    if d.deleted {
                        continue;
                    }
                    subchecks = subchecks.saturating_add(1);
                    let mut flipped: Option<Lit> = None;
                    let mut failed = false;
                    for &dl in d.lits.iter() {
                        let m = mark[dl.code() as usize];
                        if m == 0 {
                            failed = true;
                            break;
                        }
                        if m > 0 {
                            continue;
                        }
                        // Complemented occurrence: allow exactly one.
                        if flipped.is_some() {
                            failed = true;
                            break;
                        }
                        flipped = Some(dl);
                    }
                    if failed {
                        continue;
                    }
                    match flipped {
                        None => {
                            outcome = Some(SubCheck::Subsumed { subsumer: did });
                            break 'candidate;
                        }
                        // `dl ∉ c` but `¬dl ∈ c`: strengthen by removing
                        // `¬dl` from the candidate.
                        Some(dl) => {
                            outcome = Some(SubCheck::Strengthen {
                                remove: dl.negate(),
                            });
                            break 'candidate;
                        }
                    }
                }
                if subchecks >= budget {
                    break;
                }
            }

            // Unmark (both polarities).
            for &l in &lits {
                mark[l.code() as usize] = 0;
                mark[l.negate().code() as usize] = 0;
            }

            match outcome {
                Some(SubCheck::Subsumed { subsumer }) => {
                    // cadical `subsume_clause`: deleting an *irredundant*
                    // (original) clause on the word of a *redundant*
                    // (learned) subsumer is only sound if the subsumer
                    // becomes permanent – promote it to irredundant. A
                    // learned subsumer can otherwise die later (database
                    // reduction, elimination of its variables), leaving the
                    // deleted original's obligation uncovered: the final
                    // model then violates an entailed clause and therefore
                    // an original clause (false SAT; reproduced by
                    // `crn_11_99_u`, where learned (57∨1101) subsumed
                    // (37∨57∨1101) and reduction later removed it).
                    let subsumed_learned = self.clauses.get(cid).is_some_and(|c| c.learned)
                        && std::env::var("OXIZ_NOPROMOTE").is_err();
                    if !subsumed_learned
                        && let Some(s) = self.clauses.get_mut(subsumer)
                        && s.learned
                    {
                        s.learned = false;
                    }
                    if let Some(c) = self.clauses.get(cid) {
                        // Re-arm elimination for the variables of the removed
                        // clause (cadical `elim_update_removed_clause`).
                        let lits: SmallVec<[Lit; 8]> = c.lits.iter().copied().collect();
                        self.mark_elim_vars(lits.iter().copied());
                    }
                    if let Some(c) = self.clauses.get_mut(cid) {
                        c.deleted = true;
                    }
                    self.stats.deleted_clauses += 1;
                    self.stats.subsumed_removed += 1;
                    // DRAT deletion (no-op unless enabled); read the literals
                    // before the clause is retired.
                    if self.proof.is_some()
                        && let Some(c) = self.clauses.get(cid)
                    {
                        let lits: SmallVec<[Lit; 8]> = c.lits.iter().copied().collect();
                        self.drat_delete_lits(&lits);
                    }
                    subsumed += 1;
                    continue;
                }
                Some(SubCheck::Strengthen { remove }) => {
                    let idx = lits.iter().position(|&l| l == remove);
                    if let Some(idx) = idx {
                        // Re-arm elimination for the shrunken clause's
                        // variables (cadical marks on `shrink_clause`).
                        self.mark_elim_vars(lits.iter().copied());
                        self.strengthen_clause_in_subsume(cid, idx);
                        strengthened += 1;
                    }
                    // Fall through: also connect the strengthened clause.
                }
                None => {}
            }

            // Connect the clause on its least-occurring literal so later,
            // larger candidates can match against it (cadical one-watch).
            let cur: SmallVec<[Lit; 8]> = match self.clauses.get(cid) {
                Some(c) if !c.deleted => c.lits.iter().copied().collect(),
                _ => continue,
            };
            let mut minlit = cur[0];
            let mut minsize = occs[minlit.code() as usize].len();
            for &l in &cur[1..] {
                let size = occs[l.code() as usize].len();
                if size < minsize {
                    minlit = l;
                    minsize = size;
                }
            }
            // Do not connect a clause through an over-long list.
            if minsize <= 100 {
                occs[minlit.code() as usize].push(cid);
            }
        }

        (subsumed, strengthened)
    }

    /// Strengthen `clause_id` by dropping the literal at `idx`, keeping
    /// watches, binary graph and proof stream consistent.
    ///
    /// A result of length 2 is additionally entered into the binary
    /// implication graph (mirroring what `learn_clause` does for binary
    /// learned clauses), so binary propagation keeps seeing it.
    fn strengthen_clause_in_subsume(&mut self, clause_id: ClauseId, idx: usize) {
        let len_before = self.clauses.get(clause_id).map_or(0, |c| c.lits.len());
        let learned = self.clauses.get(clause_id).is_some_and(|c| c.learned);
        self.remove_literal_and_rewatch(clause_id, idx);
        if learned
            && let Some(c) = self.clauses.get_mut(clause_id)
            && !c.deleted
        {
            // cadical `shrink_clause`: a shrunken redundant clause's glue is
            // clamped to `min(size - 1, glue)` (glue only ever decreases).
            // Without the clamp a learned clause's stale LBD can exceed its
            // new length, tripping the LBD≤length invariant at the next
            // consistency check.
            let cap = (c.lits.len().saturating_sub(1).max(1)) as u32;
            if c.lbd > cap {
                c.lbd = cap;
            }
        }
        if len_before == 3
            && let Some(c) = self.clauses.get(clause_id)
            && c.lits.len() == 2
        {
            let l0 = c.lits[0];
            let l1 = c.lits[1];
            self.binary_graph.add(l0.negate(), l1, clause_id);
            self.binary_graph.add(l1.negate(), l0, clause_id);
        }
    }
}
