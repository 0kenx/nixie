//! Forward subsumption and BIG-based self-subsumption passes used by the
//! pre-search simplification path.
//!
//! The one-shot SatELite-style bounded variable elimination that used to live
//! here was replaced by the cadical `elim.cpp` port in `solver/eliminate.rs`
//! (occurrence-list driven, on-the-fly self-subsumption, backward
//! subsumption of resolvents, growing elimination bound, re-armed during
//! search). The model-reconstruction machinery it shared (`bve_def` /
//! `bve_order`, `var_eliminated`) is unchanged and lives on `Solver`.

use super::*;
use crate::occurrence::OccurrenceList;

impl Solver {
    /// Forward subsumption: remove every clause that is subsumed by some other
    /// clause (C subsumes C' iff C ⊆ C'). This is what lets BVE / congruence
    /// actually *shrink* the formula – resolvents and rewritten clauses
    /// frequently subsume older, weaker clauses, and dropping them keeps
    /// propagation cheap.
    ///
    /// Occurrence-based with the smallest-occurrence-literal heuristic: for a
    /// clause C', a subsumer must share at least one literal with it, and we
    /// scan the occurrence list of C''s rarest literal (fewest candidates) and
    /// merge-check each. Cost-guarded so a single high-degree literal cannot
    /// dominate. Incomplete by construction (a subsumer missing the rarest
    /// literal is not found) – fine, since subsumption is an optimization.
    /// Returns the number of clauses removed.
    pub(super) fn forward_subsumption(&mut self) -> usize {
        if self.trail.decision_level() != 0 {
            return 0;
        }
        // Ensure every live clause is sorted + deduped (resolvents from BVE are
        // not), and drop any tautology that slipped through.
        let norm_ids: Vec<ClauseId> = self.clauses.iter_ids().collect();
        for cid in norm_ids {
            let needs = self
                .clauses
                .get(cid)
                .is_some_and(|c| !c.deleted && c.lits.len() >= 2);
            if !needs {
                continue;
            }
            let taut = self.clauses.normalize(cid);
            if taut {
                self.clauses.mark_deleted_raw(cid);
            }
        }

        let num_vars = self.num_vars;
        let mut occ = OccurrenceList::new();
        occ.resize(num_vars);
        for cid in self.clauses.iter_ids() {
            let Some(c) = self.clauses.get(cid) else {
                continue;
            };
            if c.deleted || c.lits.len() < 2 {
                continue;
            }
            for &lit in c.lits {
                occ.add(lit, cid);
            }
        }

        const OCC_CAP: usize = 512;
        let mut removed = 0usize;
        let ids: Vec<ClauseId> = self.clauses.iter_ids().collect();
        for cid in ids {
            let target_lits: SmallVec<[Lit; 8]> = match self.clauses.get(cid) {
                Some(c) if !c.deleted && c.lits.len() >= 2 => c.lits.iter().copied().collect(),
                _ => continue,
            };
            // Rarest literal → fewest candidates. Skip if even that is too
            // highly connected to bound the pass.
            let Some(&lstar) = target_lits.iter().min_by_key(|&&l| occ.count(l)) else {
                continue;
            };
            if occ.count(lstar) > OCC_CAP {
                continue;
            }
            // A clause justifying a level-0 trail assignment (a propagation
            // reason) must not be deleted – conflict analysis reads reason
            // clauses, and a deleted reason yields garbage (wrong UNSAT).
            let is_reason = self.clauses.get(cid).is_some_and(|c| {
                c.lits.iter().any(|&lit| {
                    let var = lit.var();
                    self.trail.is_assigned(var)
                        && matches!(self.trail.reason(var), Reason::Propagation(r) if r == cid)
                })
            });
            if is_reason {
                continue;
            }
            let subsumed = occ.get(lstar).iter().any(|&cand| {
                if cand == cid {
                    return false;
                }
                let Some(c) = self.clauses.get(cand) else {
                    return false;
                };
                if c.deleted || c.lits.len() > target_lits.len() {
                    return false;
                }
                subset_of(c.lits, &target_lits)
            });
            if subsumed {
                if let Some(c) = self.clauses.get(cid) {
                    for &lit in c.lits {
                        occ.remove(lit, cid);
                    }
                }
                self.clauses.mark_deleted_raw(cid);
                removed += 1;
            }
        }

        // ALWAYS rebuild the watched-literal structures after this pass.
        // The normalize prologue above reorders literals in place, and
        // `propagate` requires each clause's two watched literals at stored
        // positions [0]/[1] (see the `learn_clause` watch-position fix): a
        // normalize-only reorder with `removed == 0` used to skip the
        // rebuild, leaving every clause's watches pointing at stale
        // positions. BCP then "propagated" literals that were never implied
        // and the search concluded a false UNSAT within a handful of
        // conflicts (reproducer: `noL-11-14` with `INPROCESS=1`, SAT per
        // CaDiCaL, 6 conflicts). Tautology deletions in the prologue are
        // likewise only cleaned out of the watch lists by this rebuild.
        self.rebuild_watches_and_binary_graph();
        if removed > 0 {
            self.stats.subsumed_removed += removed as u64;
        }
        removed
    }
}

/// Check if `needle` (sorted) ⊆ `hay` (sorted), i.e. every literal of `needle`
/// appears in `hay`. Linear merge.
fn subset_of(needle: &[Lit], hay: &[Lit]) -> bool {
    let mut i = 0;
    let mut j = 0;
    while i < needle.len() && j < hay.len() {
        if needle[i] == hay[j] {
            i += 1;
            j += 1;
        } else if needle[i].code() < hay[j].code() {
            return false;
        } else {
            j += 1;
        }
    }
    i == needle.len()
}

impl Solver {
    /// BIG-based self-subsumption (diagnostic rebuild). Strengthen each clause
    /// by removing a literal implied (via the binary implication graph) by
    /// another literal in the same clause. Sound in isolation.
    pub(super) fn self_subsumption_pass(&mut self) -> usize {
        use crate::literal::LBool;
        if self.trail.decision_level() != 0 {
            return 0;
        }
        const MAX_LEN: usize = 16;
        let mut removed_lits = 0usize;
        let mut units: SmallVec<[Lit; 32]> = SmallVec::new();
        let ids: Vec<ClauseId> = self.clauses.iter_ids().collect();
        for cid in ids {
            let mut lits: SmallVec<[Lit; 8]> = match self.clauses.get(cid) {
                Some(c) if !c.deleted && (3..=MAX_LEN).contains(&c.lits.len()) => {
                    c.lits.iter().copied().collect()
                }
                _ => continue,
            };
            let orig_len = lits.len();
            loop {
                if lits.len() < 2 {
                    break;
                }
                let mut remove_idx: Option<usize> = None;
                'find: for i in 0..lits.len() {
                    let li = lits[i];
                    for j in 0..lits.len() {
                        if i == j {
                            continue;
                        }
                        if self.has_binary_implication(li, lits[j]) {
                            remove_idx = Some(i);
                            break 'find;
                        }
                    }
                }
                match remove_idx {
                    Some(i) => {
                        lits.remove(i);
                        removed_lits += 1;
                    }
                    None => break,
                }
            }
            match lits.len() {
                0 => {
                    self.trivially_unsat = true;
                    return removed_lits;
                }
                1 => {
                    units.push(lits[0]);
                    self.clauses.mark_deleted_raw(cid);
                }
                n if n < orig_len => {
                    self.clauses.shrink(cid, &lits);
                }
                _ => {}
            }
        }
        if removed_lits > 0 {
            self.rebuild_watches_and_binary_graph();
            for lit in units {
                match self.trail.lit_value(lit) {
                    LBool::True => {}
                    LBool::False => {
                        self.trivially_unsat = true;
                        return removed_lits;
                    }
                    LBool::Undef => self.trail.assign_decision(lit),
                }
            }
            if self.propagate().is_some() {
                self.trivially_unsat = true;
            }
        }
        removed_lits
    }
}
