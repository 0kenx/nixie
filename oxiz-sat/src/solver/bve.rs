//! Bounded Variable Elimination (BVE / SatELite).
//!
//! Eliminate a variable `v` by resolving every clause containing `v` against
//! every clause containing `¬v`, producing resolvents that no longer mention
//! `v`. This is sound (resolution preserves satisfiability) and shrinks the
//! formula whenever the resolvents are not more numerous than the original
//! clauses – the "bounded" gate. The eliminated variable is reconstructed at
//! model-extension time from its recorded positive clauses (see
//! [`Solver::save_model`]).
//!
//! One-shot, pre-search, decision level 0, base assertion scope. Rewrites the
//! clause database and folds variables out of the search, so it shares the
//! incremental/AllSAT caveat of `equiv.rs`.

use super::*;
use crate::clause::ClauseId;
use crate::literal::LBool;
use crate::occurrence::OccurrenceList;

/// Outcome of one BVE pass (reuses the substitution outcome type's intent).
pub(super) use super::equiv::SubstOutcome;

/// Upper bound on `|pos| * |neg|` before we even attempt to generate
/// resolvents for a variable (generating them is O(product*size)).
const RESOLVENT_PRODUCT_CAP: usize = 4_000;

impl Solver {
    /// Run bounded variable elimination over the live clause database.
    pub(super) fn bounded_variable_elimination(&mut self) -> SubstOutcome {
        if self.did_bve
            || self.trail.decision_level() != 0
            || self.assertion_levels.len() > 1
            || self.proof.is_some()
        {
            return SubstOutcome::Ok;
        }

        let num_vars = self.num_vars;
        // Occurrence lists over current live clauses (len >= 2; units live on
        // the trail, not in the DB).
        let mut occ = OccurrenceList::new();
        occ.resize(num_vars);
        for cid in self.clauses.iter_ids() {
            let Some(c) = self.clauses.get(cid) else {
                continue;
            };
            if c.deleted || c.lits.len() < 2 {
                continue;
            }
            for &lit in &c.lits {
                occ.add(lit, cid);
            }
        }

        // Process variables cheapest-first (fewest occurrences). The counts
        // drift as clauses are removed and resolvents added, so we re-read the
        // current count when we reach a variable.
        let mut order: Vec<Var> = (0..num_vars as u32).map(Var::new).collect();
        order.sort_by_key(|&v| occ.var_occurrence_count(v.index()));

        self.bve_def.resize(num_vars, Vec::new());

        let mut eliminated = 0usize;
        let mut unit_queue: SmallVec<[Lit; 32]> = SmallVec::new();
        let mut derived_units: SmallVec<[Lit; 32]> = SmallVec::new();
        for &v in &order {
            // Skip variables already folded out by substitution/BVE, or already
            // fixed at level 0 (their clauses are satisfied/falsified by that
            // fact; eliminating them would record a reconstruction that fights
            // the fixed value).
            if self.trail.is_assigned(v)
                || self.var_eliminated(v)
                || !self.bve_def[v.index()].is_empty()
            {
                continue;
            }
            let pos = Lit::pos(v);
            let neg = Lit::neg(v);
            let pos_ids: Vec<ClauseId> = occ.get(pos).to_vec();
            let neg_ids: Vec<ClauseId> = occ.get(neg).to_vec();
            // A variable with only one polarity present is *pure* – eliminating
            // it would drop clauses with no resolvents; leave that to
            // pure-literal handling. BVE needs both polarities.
            if pos_ids.is_empty() || neg_ids.is_empty() {
                continue;
            }
            let product = pos_ids.len().saturating_mul(neg_ids.len());
            if product > RESOLVENT_PRODUCT_CAP {
                continue;
            }

            // Snapshot the literal sets of the candidate clauses (they may be
            // shared / mutated during elimination of earlier variables, so read
            // fresh here).
            let pos_lits: Vec<SmallVec<[Lit; 8]>> = pos_ids
                .iter()
                .filter_map(|&cid| self.clauses.get(cid).map(|c| c.lits.clone()))
                .collect();
            let neg_lits: Vec<SmallVec<[Lit; 8]>> = neg_ids
                .iter()
                .filter_map(|&cid| self.clauses.get(cid).map(|c| c.lits.clone()))
                .collect();

            // Literal-aware SatELite bound: elimination must not increase the
            // *total literal count*, not just the clause count. The clause-
            // count bound alone lets several short clauses be replaced by fewer
            // but much longer resolvents (e.g. 6x3-lit clauses -> 6x5-lit
            // resolvents passes the clause bound but 18->30 literals). Cascaded
            // over thousands of inprocessing passes this bloats the DB with
            // long high-glue clauses, halving BCP throughput and exploding the
            // conflict count (~37x slowdown on mrpp_4x4#12_12). Stricter is
            // only more conservative here, so this cannot affect soundness.
            let removed_lits: usize = pos_lits
                .iter()
                .chain(neg_lits.iter())
                .map(|c| c.len())
                .sum();

            // Generate resolvents, skipping tautologies and duplicates.
            let mut resolvents: Vec<SmallVec<[Lit; 8]>> = Vec::new();
            let mut resolvent_lits: usize = 0;
            let mut abort = false;
            'pair: for pc in &pos_lits {
                for nc in &neg_lits {
                    let Some(r) = resolve(pc, nc, pos, neg) else {
                        continue; // tautology
                    };
                    match r.len() {
                        0 => {
                            // Empty resolvent: the formula is UNSAT.
                            self.trivially_unsat = true;
                            return SubstOutcome::Unsat;
                        }
                        1 => {
                            resolvent_lits += 1;
                            resolvents.push(r);
                        }
                        _ => {
                            // Early bounds: bail if this elimination would grow
                            // the formula by clause count *or* literal count.
                            resolvent_lits += r.len();
                            if resolvents.len() + 1 > pos_lits.len() + neg_lits.len()
                                || resolvent_lits > removed_lits
                            {
                                abort = true;
                                break 'pair;
                            }
                            resolvents.push(r);
                        }
                    }
                }
                if abort {
                    break;
                }
            }
            if abort {
                continue;
            }

            // SatELite bounds: only eliminate if resolvents neither outnumber
            // the removed clauses nor increase the total literal count.
            if resolvents.len() > pos_lits.len() + neg_lits.len() || resolvent_lits > removed_lits {
                continue;
            }

            // Deduplicate resolvents (a pair of clauses can resolve to the same
            // resolvent via different literals). Sorting by code gives a stable
            // canonical form.
            for r in &mut resolvents {
                r.sort_unstable_by_key(|l| l.code());
                r.dedup();
            }
            resolvents.sort_by(|a, b| {
                a.len().cmp(&b.len()).then_with(|| {
                    a.iter()
                        .map(|l| l.code())
                        .collect::<SmallVec<[u32; 8]>>()
                        .cmp(&b.iter().map(|l| l.code()).collect())
                })
            });
            resolvents.dedup_by(|a, b| a == b);

            // Record positive clauses (with v stripped) for model
            // reconstruction, then retire v's clauses from the DB + occurrences.
            for pc in &pos_lits {
                let stripped: SmallVec<[Lit; 4]> =
                    pc.iter().copied().filter(|&l| l != pos).collect();
                self.bve_def[v.index()].push(stripped);
            }
            for &cid in pos_ids.iter().chain(neg_ids.iter()) {
                if let Some(c) = self.clauses.get(cid).filter(|c| !c.deleted) {
                    for &lit in &c.lits {
                        occ.remove(lit, cid);
                    }
                }
                if let Some(c) = self.clauses.get_mut(cid) {
                    c.deleted = true;
                }
            }

            // Add the resolvents. Unit resolvents go into a queue and are applied
            // *immediately* via occurrence-based simplification (not deferred):
            // a derived unit is a constraint on its variable, and a later
            // variable's elimination must see it (else it eliminates the forced
            // variable as if free and silently drops the constraint – flipping
            // UNSAT to SAT). Watches are stale mid-pass, so this is occurrence-
            // based, not watch-based.
            for r in resolvents {
                match r.len() {
                    0 => {
                        self.trivially_unsat = true;
                        return SubstOutcome::Unsat;
                    }
                    1 => unit_queue.push(r[0]),
                    _ => {
                        let cid = self.clauses.add_original(r.iter().copied());
                        if let Some(c) = self.clauses.get(cid) {
                            for &lit in &c.lits {
                                occ.add(lit, cid);
                            }
                        }
                    }
                }
            }

            // Apply any units derived from this variable's resolvents (cascading)
            // before eliminating the next variable, so later eliminations see a
            // consistent, simplified formula.
            if self.bve_propagate_units(&mut occ, &mut unit_queue, &mut derived_units)
                == SubstOutcome::Unsat
            {
                self.trivially_unsat = true;
                return SubstOutcome::Unsat;
            }

            self.bve_order.push(v);
            eliminated += 1;
        }

        if eliminated == 0 {
            self.did_bve = true;
            return SubstOutcome::Ok;
        }

        // Rebuild watch lists + binary implication graph from the surviving
        // clause set, then assign the units derived during the pass (they are
        // already baked into the clause set via occurrence simplification, but
        // the level-0 trail must carry them so the search treats the forced
        // variables as assigned).
        self.rebuild_watches_and_binary_graph();

        for lit in &derived_units {
            match self.trail.lit_value(*lit) {
                LBool::True => {}
                LBool::False => {
                    self.trivially_unsat = true;
                    return SubstOutcome::Unsat;
                }
                LBool::Undef => self.trail.assign_decision(*lit),
            }
        }
        if self.propagate().is_some() {
            self.trivially_unsat = true;
            return SubstOutcome::Unsat;
        }

        self.stats.bve_eliminated += eliminated as u64;
        self.did_bve = true;
        SubstOutcome::Ok
    }

    /// Occurrence-based unit propagation for use *during* BVE, where the watch
    /// lists are stale. For a forced literal `lit` (true): clauses containing
    /// `lit` are satisfied (deleted); clauses containing `¬lit` are shortened by
    /// dropping `¬lit`, which may expose new units (cascaded via `queue`). Each
    /// propagated literal is recorded in `derived` so the caller can put it on
    /// the level-0 trail once watches are rebuilt. Returns `Unsat` if an empty
    /// clause (real contradiction) is produced.
    pub(super) fn bve_propagate_units(
        &mut self,
        occ: &mut OccurrenceList,
        queue: &mut SmallVec<[Lit; 32]>,
        derived: &mut SmallVec<[Lit; 32]>,
    ) -> SubstOutcome {
        while let Some(lit) = queue.pop() {
            // Idempotent: skip if this literal's polarity is already forced.
            if derived.contains(&lit) {
                continue;
            }
            // If the opposite polarity was already derived, that's a conflict.
            if derived.iter().any(|&d| d == lit.negate()) {
                self.trivially_unsat = true;
                return SubstOutcome::Unsat;
            }
            derived.push(lit);
            let neg = lit.negate();

            // Clauses containing `lit` (now true) are satisfied → delete.
            let sat_ids: Vec<ClauseId> = occ.get(lit).to_vec();
            for cid in sat_ids {
                let lits: SmallVec<[Lit; 8]> = match self.clauses.get(cid) {
                    Some(c) if !c.deleted => c.lits.iter().copied().collect(),
                    _ => continue,
                };
                for &l in &lits {
                    occ.remove(l, cid);
                }
                if let Some(c) = self.clauses.get_mut(cid) {
                    c.deleted = true;
                }
            }

            // Clauses containing `¬lit` (now false) → shorten by dropping `¬lit`.
            let short_ids: Vec<ClauseId> = occ.get(neg).to_vec();
            for cid in short_ids {
                let lits: SmallVec<[Lit; 8]> = match self.clauses.get(cid) {
                    Some(c) if !c.deleted => c.lits.iter().copied().collect(),
                    _ => continue,
                };
                occ.remove(neg, cid);
                let new_lits: SmallVec<[Lit; 8]> =
                    lits.iter().copied().filter(|&l| l != neg).collect();
                match new_lits.len() {
                    0 => {
                        // Empty clause: the formula is UNSAT.
                        self.trivially_unsat = true;
                        return SubstOutcome::Unsat;
                    }
                    1 => queue.push(new_lits[0]),
                    _ => {
                        if let Some(c) = self.clauses.get_mut(cid) {
                            c.lits = new_lits;
                        }
                    }
                }
            }

            // The variable is now forced: purge any stale residual occurrences.
            occ.clear_literal(lit);
            occ.clear_literal(neg);
        }
        SubstOutcome::Ok
    }
}

/// Resolve two clauses `pc` (containing `pos`) and `nc` (containing `neg`) on
/// variable `pos`/`neg`, returning the resolvent with the pivot removed. Returns
/// `None` if the resolvent is a tautology (contains both polarities of some
/// variable).
fn resolve(pc: &[Lit], nc: &[Lit], pos: Lit, neg: Lit) -> Option<SmallVec<[Lit; 8]>> {
    let mut out: SmallVec<[Lit; 8]> = SmallVec::new();
    for &lit in pc {
        if lit == pos {
            continue;
        }
        if out.contains(&lit) {
            continue;
        }
        if out.iter().any(|&l| l == lit.negate()) {
            return None; // tautology
        }
        out.push(lit);
    }
    for &lit in nc {
        if lit == neg {
            continue;
        }
        if out.contains(&lit) {
            continue;
        }
        if out.iter().any(|&l| l == lit.negate()) {
            return None; // tautology
        }
        out.push(lit);
    }
    Some(out)
}

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
            let taut = self.clauses.get_mut(cid).is_some_and(|c| c.normalize());
            if taut && let Some(c) = self.clauses.get_mut(cid) {
                c.deleted = true;
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
            for &lit in &c.lits {
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
                subset_of(&c.lits, &target_lits)
            });
            if subsumed {
                if let Some(c) = self.clauses.get(cid) {
                    for &lit in &c.lits {
                        occ.remove(lit, cid);
                    }
                }
                if let Some(c) = self.clauses.get_mut(cid) {
                    c.deleted = true;
                }
                removed += 1;
            }
        }

        if removed > 0 {
            self.rebuild_watches_and_binary_graph();
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
                    if let Some(c) = self.clauses.get_mut(cid) {
                        c.deleted = true;
                    }
                }
                n if n < orig_len => {
                    if let Some(c) = self.clauses.get_mut(cid) {
                        c.lits = lits;
                    }
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
