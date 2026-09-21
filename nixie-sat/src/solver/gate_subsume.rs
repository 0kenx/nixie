//! Gate-modulo forward subsumption inside the equivalence-closure round —
//! a port of kissat `congruence.c:forward_subsume_matching_clauses`
//! (2026-09-21 slice; `docs/studies/2026-09-18-ite-gate-congruence.md`
//! measured kissat retiring **108,484 clauses = 44 % of tried** through
//! the repr-canonicalized literals on `bv_ILA` before search starts).
//!
//! Placement is kissat's exactly: after the SCC builds the class map and
//! the early-out, BEFORE the fold's rewrite writes the representatives
//! back.  Every whole-clause retirement here is one the rewrite would
//! otherwise leave behind: the rewrite only retires *exact* canonical
//! duplicates and tautologies — strictly-smaller-set subsumption modulo
//! the classes (`d ⊂ c` with `|d| < |c|`) is this pass's alone.
//!
//! Semantics: `d` subsumes `c` modulo classes iff every literal of `d`
//! (mapped through `sub`, value-filtered at level 0) occurs in `c`'s
//! mapped set.  Soundness for verdicts AND models: the equivalence
//! classes are entailed by the retained binary evidence, so any model of
//! the kept clauses plus the classes satisfies `c`; retirement is
//! whole-clause only — no strengthening, the shape the separate
//! post-substitution `forward_subsumption` + self-subsumption sequence's
//! ≈1/15k wrong-model interaction (see the caller in `mod.rs`) does not
//! take.  Retirements run through the same `retire_clause` the rewrite's
//! tautology path uses (binary-graph purge, reason fixup, arena
//! bookkeeping — including the `num_original` decrement the
//! fold-collapse accounting reads).
//!
//! Candidates are originals only (kissat's `last_irredundant` bound;
//! learned clauses are the search's own product), and — as in kissat —
//! only those containing a *matchable* variable (a literal whose
//! representative differs, or a representative of such a literal): the
//! no-matchable case is ordinary subsumption, owned by the regular
//! subsumption passes.  The subsumer pool is every live original's
//! canonical set.  Candidates are probed smallest-set-first so a
//! subsumer is met before its victims whenever sizes allow, exactly
//! kissat's `sort_references_by_clause_size`.  The probe then walks ONE
//! occurrence list per victim — the least-occurring repr's — which
//! makes the pass *incomplete* by design (kissat parity): a subsumer
//! sharing no literal with that repr is missed, falling to the regular
//! subsumption passes or the next round's exact-duplicate retire.

use super::Solver;
use crate::{ClauseId, LBool, Lit};
use smallvec::SmallVec;
use std::cmp::Ordering;

/// Probe work budget: literal comparisons across all subset checks.
/// Generous (kissat bounds by termination checks only); exists so a
/// pathological occurrence shape cannot run away on the gated arm.
const GATE_SUBSUME_WORK_CAP: u64 = 100_000_000;

/// Whether `small ⊆ big` for two repr sets sorted and deduped by literal
/// code.  Linear merge scan; `small.len() <= big.len()` is the caller's
/// ordering invariant (probes only look up the victim's own occurrence
/// lists, and the candidate order is ascending).
#[inline]
pub(super) fn sorted_subset(small: &[Lit], big: &[Lit]) -> bool {
    let mut i = 0usize;
    'outer: for &d in small {
        while i < big.len() {
            match big[i].code().cmp(&d.code()) {
                Ordering::Less => i += 1,
                Ordering::Equal => {
                    i += 1;
                    continue 'outer;
                }
                Ordering::Greater => return false,
            }
        }
        // Exhausted `big` without meeting `d`: it is absent.
        return false;
    }
    true
}

impl Solver {
    /// The port itself: retire every matchable-containing original whose
    /// canonical repr-set contains another live original's set.  Returns
    /// the retirement count.  Runs at level 0 inside the closure round
    /// (the caller's invariant); reads the trail only for value
    /// filtering, mutates only through `retire_clause`.
    pub(super) fn forward_subsume_matching(&mut self, sub: &[Lit]) -> usize {
        let num_vars = self.num_vars;
        let num_lits = num_vars * 2;
        debug_assert_eq!(sub.len(), num_lits);

        // Matchable variables (kissat's matchable bitmap): every literal
        // whose representative differs, and every representative such a
        // literal maps onto.
        let mut matchable = vec![false; num_vars];
        for v in 0..num_vars {
            let pos = Lit::pos(crate::Var::new(v as u32));
            let repr = sub[pos.code() as usize];
            if repr != pos {
                matchable[v] = true;
                matchable[repr.var().index()] = true;
            }
        }

        // One pass over the live originals: canonicalize (map through
        // `sub`, drop level-0-false literals, sort + dedup by code),
        // retire satisfied clauses and class-tautologies (the rewrite's
        // own retire paths — doing them here only moves them earlier),
        // collect every canonical set as subsumer pool, and the
        // matchable-containing ones as subsumption candidates.  Ids are
        // collected first: `retire_clause` takes `&mut self` while the
        // arena iterator holds an immutable borrow (the rewrite loop's
        // own shape).
        let ids: Vec<ClauseId> = self.clauses.iter_ids().collect();
        let mut sets: rustc_hash::FxHashMap<u32, SmallVec<[Lit; 8]>> =
            rustc_hash::FxHashMap::default();
        let mut candidates: Vec<u32> = Vec::new();
        let mut scratch: SmallVec<[Lit; 8]> = SmallVec::new();
        for cid in ids {
            let mut satisfied = false;
            scratch.clear();
            if let Some(c) = self.clauses.get(cid)
                && !c.deleted
                && !c.learned
            {
                'lits: for &l in c.lits.iter() {
                    match self.trail.lit_value(l) {
                        LBool::True => {
                            satisfied = true;
                            break 'lits;
                        }
                        LBool::False => continue,
                        LBool::Undef => scratch.push(sub[l.code() as usize]),
                    }
                }
            } else {
                continue;
            }
            if satisfied {
                self.retire_clause(cid);
                continue;
            }
            scratch.sort_unstable_by_key(|l| l.code());
            scratch.dedup_by_key(|l| l.code());
            // Class tautology: the mapped set holds a literal and its
            // negation (adjacent codes of the same variable).
            if scratch.windows(2).any(|w| w[0].var() == w[1].var()) {
                self.retire_clause(cid);
                continue;
            }
            let contains_matchable = scratch.iter().any(|l| matchable[l.var().index()]);
            if contains_matchable {
                candidates.push(cid.index() as u32);
            }
            sets.insert(cid.index() as u32, scratch.clone());
        }

        // Probe smallest-set-first (kissat sorts candidates by size).
        candidates.sort_by_key(|cid| sets.get(cid).map_or(0, |s| s.len()));

        // Occurrence lists over canonical reprs for the whole subsumer
        // pool (kissat's dense-mode lists contain every clause; candidates
        // connect lazily there, eagerly here — the probe's shortest-list
        // choice bounds the walk the same way).
        let mut occ: Vec<Vec<u32>> = vec![Vec::new(); num_lits];
        for (cid, set) in &sets {
            for &l in set {
                occ[l.code() as usize].push(*cid);
            }
        }

        let mut subsumed = 0usize;
        let mut work: u64 = 0;
        'victim: for &cid in &candidates {
            if work > GATE_SUBSUME_WORK_CAP {
                break;
            }
            // Retired earlier in this pass (a smaller victim met first)?
            if self
                .clauses
                .get(ClauseId::new(cid))
                .is_none_or(|c| c.deleted)
            {
                continue;
            }
            let Some(s_c) = sets.get(&cid) else {
                continue;
            };
            // Shortest occurrence list among the victim's reprs.
            let mut probe_lit = s_c[0];
            let mut probe_len = usize::MAX;
            for &l in s_c {
                let len = occ[l.code() as usize].len();
                if len < probe_len {
                    probe_len = len;
                    probe_lit = l;
                }
            }
            for &d_cid in &occ[probe_lit.code() as usize] {
                if d_cid == cid {
                    continue;
                }
                let Some(s_d) = sets.get(&d_cid) else {
                    continue;
                };
                work += s_d.len() as u64 + 1;
                if work > GATE_SUBSUME_WORK_CAP {
                    break 'victim;
                }
                if s_d.len() <= s_c.len() && sorted_subset(s_d, s_c) {
                    self.retire_clause(ClauseId::new(cid));
                    // The victim leaves the subsumer pool WITH its
                    // retirement: a later candidate probing this set
                    // would otherwise "subsume" through a clause that is
                    // itself gone — two equal-set clauses retire each
                    // other and the constraint vanishes entirely (the
                    // minimal counterexample: differential iter 1186,
                    // invalid model).  kissat's dense-mode lists make the
                    // same guarantee structurally (`assert (!d->garbage)`
                    // in `find_subsuming_clause`); the `sets.remove` here
                    // is that guarantee.
                    sets.remove(&cid);
                    subsumed += 1;
                    continue 'victim;
                }
            }
        }
        subsumed
    }
}
