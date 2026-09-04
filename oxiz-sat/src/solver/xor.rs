//! XOR (parity) constraint extraction and Gaussian elimination — first
//! slice: detection of exact parity-class clause groups in the CNF, linear
//! solve over GF(2), and **phase seeding** of the solution.
//!
//! **Detection** (`detect_xor_constraints`): a conjunction of the
//! `2^(k-1)` clauses over a fixed variable set `V` (`|V| = k`) whose
//! negative-literal sets all share one negation parity is exactly the CNF
//! encoding of the parity constraint `⊕_{v∈V} v = c`.  The check is
//! strict: a var set whose clause group is incomplete, or whose patterns
//! mix parities (e.g. the pair `(a∨b)∧(¬a∨b)`, which *implies* `b` and is
//! no parity constraint), or duplicated clauses, is not an XOR
//! constraint.  Telemetry over the standing corpus (2026-09-05): 22 files
//! carry strict groups — the simon family (2–3k groups each),
//! g2-ak128booth (99k groups / 181k vars), summle ×3, mp1-Nb7T42 (25k
//! groups / 52k vars), g2-slp, pb_300 — and **mdp-28-14, one of the four
//! standing unsolved files (373 groups over 401 vars ≈ the whole
//! formula)**.
//!
//! **Why phases**: with the saved phases set to a *model* of a
//! satisfiable formula, CDCL descends without a single conflict — unit
//! propagation never conflicts under model-consistent decisions (any
//! clause that becomes unit has its last literal at the model's value).
//! The oracle-phase measurements of the same day showed exactly this,
//! with the residual conflicts attributable to `random_polarity_prob`.
//! Gaussian elimination over the extracted system produces a satisfying
//! assignment *of the XOR subsystem*; seeding phases with it is sound
//! (phases are preferences — no assignment, no proof interaction) and
//! converts the search into a descent whenever the XOR constraints pin
//! the formula's satisfying structure.
//!
//! **Slice gates** (mirroring `bva.rs`/`factor.rs`): pre-search, decision
//! level 0, base scope only, no attached theory, no proof/LRAT tracer,
//! deterministic budgets.  **No verdicts are produced** — an inconsistent
//! XOR subsystem does imply UNSAT, but slice 1 has no proof story for
//! that derivation and refuses to fabricate one; the trace records it.
//!
//! Divergences from CryptoMiniSat (the reference for XOR-CDCL
//! integration): no in-search propagation of linear consequences, no
//! clause learning from the matrix, no XOR proof emission.  This slice
//! only *reads* the formula and *writes phases*.

use smallvec::SmallVec;

use super::Solver;

/// Maximum clause width considered for parity-class detection (2^4 = 16
/// clauses per group at k=5; larger widths explode combinatorially and are
/// rare in practice).
const MAX_XOR_WIDTH: usize = 5;
/// Cap on distinct var-groups inspected (deterministic work bound).
const MAX_GROUPS: usize = 4_000_000;

/// One extracted parity constraint: `⊕ vars = rhs`.
pub(super) struct XorConstraint {
    /// Variable indices in increasing order (the matrix column order).
    pub vars: SmallVec<[u32; 5]>,
    /// `false` ⇒ even number of true variables, `true` ⇒ odd.
    pub rhs: bool,
}

impl Solver {
    /// Detect strict XOR constraints among live original clauses by
    /// delegating to the crate's [`crate::xor::XorDetector`] (the mature
    /// implementation this slice should not duplicate; its
    /// `compute_xor_rhs` carries the parity semantics — `rhs = (negation
    /// parity == 0)` — pinned by the `xor_detection_*` tests).
    pub(super) fn detect_xor_constraints(&self) -> Vec<XorConstraint> {
        if self.trail.decision_level() != 0 || self.trivially_unsat {
            return Vec::new();
        }
        let mut clauses: Vec<(Vec<crate::literal::Lit>, crate::clause::ClauseId)> = Vec::new();
        for cid in self.clauses.iter_ids() {
            let Some(c) = self.clauses.get(cid) else {
                continue;
            };
            if c.deleted || c.learned || c.lits.is_empty() || c.lits.len() > MAX_XOR_WIDTH {
                continue;
            }
            clauses.push((c.lits.to_vec(), cid));
        }
        if clauses.len() > MAX_GROUPS {
            clauses.truncate(MAX_GROUPS);
        }
        let detector = crate::xor::XorDetector::new(2, MAX_XOR_WIDTH);
        detector
            .detect_xor(&clauses)
            .into_iter()
            .map(|xc| XorConstraint {
                vars: xc.vars.iter().map(|v| v.index() as u32).collect(),
                rhs: xc.rhs,
            })
            .collect()
    }

    /// Gaussian elimination over GF(2) on the extracted system.
    /// Returns `Ok(assignment)` (a satisfying assignment for every
    /// constraint's variable, `var index -> bool`) or `Err(())` if the
    /// system is inconsistent.
    pub(super) fn solve_xor_system(
        &self,
        constraints: &[XorConstraint],
    ) -> Result<rustc_hash::FxHashMap<u32, bool>, ()> {
        if constraints.is_empty() {
            return Ok(rustc_hash::FxHashMap::default());
        }
        // Column map: var index -> column (deterministic, sorted).
        let mut col_of: rustc_hash::FxHashMap<u32, usize> = rustc_hash::FxHashMap::default();
        let mut vars: Vec<u32> = Vec::new();
        for c in constraints {
            for &v in &c.vars {
                if let std::collections::hash_map::Entry::Vacant(e) = col_of.entry(v) {
                    e.insert(vars.len());
                    vars.push(v);
                }
            }
        }
        vars.sort_unstable();
        for (i, v) in vars.iter().enumerate() {
            col_of.insert(*v, i);
        }
        let n = vars.len();
        let words = n.div_ceil(64);
        // Rows: bitset + rhs bit.
        let mut rows: Vec<(Vec<u64>, bool)> = Vec::with_capacity(constraints.len());
        for c in constraints {
            let mut r = vec![0u64; words];
            for &v in &c.vars {
                let col = col_of[&v];
                r[col / 64] |= 1u64 << (col % 64);
            }
            rows.push((r, c.rhs));
        }
        // Forward elimination with deterministic pivot choice (lowest
        // set column), tracking the row order for back-substitution.
        let mut pivots: Vec<(usize, usize)> = Vec::new(); // (column, row)
        let mut row = 0usize;
        for col in 0..n {
            let mut found = None;
            for (r, (bits, _)) in rows.iter().enumerate().skip(row) {
                if bits[col / 64] >> (col % 64) & 1 == 1 {
                    found = Some(r);
                    break;
                }
            }
            let Some(r) = found else { continue };
            rows.swap(row, r);
            for r2 in (row + 1)..rows.len() {
                if rows[r2].0[col / 64] >> (col % 64) & 1 == 1 {
                    for w in 0..words {
                        rows[r2].0[w] ^= rows[row].0[w];
                    }
                    rows[r2].1 ^= rows[row].1;
                }
            }
            pivots.push((col, row));
            row += 1;
            if row == rows.len() {
                break;
            }
        }
        // Consistency: a zero row with rhs = 1 is inconsistent.
        for (r, rhs) in &rows {
            if r.iter().all(|&w| w == 0) && *rhs {
                return Err(());
            }
        }
        // Back-substitution: pivot variables from the solution, free
        // variables at `false` (a deterministic, arbitrary choice — any
        // solution of the system works for phase seeding).
        let mut assign = vec![false; n];
        for &(col, r) in pivots.iter().rev() {
            let mut val = rows[r].1;
            for (c2, _) in pivots.iter().rev() {
                if c2 == &col {
                    break;
                }
                if rows[r].0[c2 / 64] >> (c2 % 64) & 1 == 1 {
                    val ^= assign[*c2];
                }
            }
            assign[col] = val;
        }
        let mut out: rustc_hash::FxHashMap<u32, bool> = rustc_hash::FxHashMap::default();
        for (i, v) in vars.iter().enumerate() {
            out.insert(*v, assign[i]);
        }
        Ok(out)
    }

    /// One pre-search XOR pass: detect, solve, seed phases.
    /// Returns `(constraints found, vars seeded, inconsistent)`.
    pub(super) fn xor_phase_seed(&mut self) -> (usize, usize, bool) {
        if self.trail.decision_level() != 0
            || self.proof.is_some()
            || self.lrat
            || self.real_theory_attached
            || self.assertion_levels.len() > 1
            || self.trivially_unsat
        {
            return (0, 0, false);
        }
        let constraints = self.detect_xor_constraints();
        if constraints.is_empty() {
            return (0, 0, false);
        }
        let n_constraints = constraints.len();
        match self.solve_xor_system(&constraints) {
            Err(()) => (n_constraints, 0, true),
            Ok(assignment) => {
                let mut seeded = 0usize;
                self.phase.resize(self.num_vars, false);
                self.target_phase.resize(self.num_vars, false);
                self.best_phase.resize(self.num_vars, false);
                for (&v, &val) in &assignment {
                    if (v as usize) < self.num_vars {
                        self.phase[v as usize] = val;
                        self.target_phase[v as usize] = val;
                        self.best_phase[v as usize] = val;
                        seeded += 1;
                    }
                }
                (n_constraints, seeded, false)
            }
        }
    }
}

impl Solver {
    /// XOR-aware failed-literal probing (2026-09-05 slice): build the
    /// GF(2) matrix from the detected constraints, force every unit the
    /// system pins (add-time reductions, then level-0 folding to a
    /// fixpoint with CNF propagation), and probe each remaining matrix
    /// variable's two polarities at a decision level — CNF propagate plus
    /// matrix folding; a failed polarity forces the opposite literal at
    /// level 0 (the `probe_round` pattern; probe-level assignments are
    /// self-contained, so no CDCL reason plumbing is needed).
    ///
    /// Fold discipline (soundness-critical, per `GF2Matrix::propagate`'s
    /// contract): every literal that appears on the trail during a probe —
    /// decisions, CNF propagations, XOR-derived units — is folded in trail
    /// order, and undone in exact reverse order before backtracking.  At
    /// level 0 the folds are permanent.
    ///
    /// No verdicts: an inconsistent system (add-time or both-polarity
    /// probe failure) is reported in the return value, not answered —
    /// pending a proof story.  Returns `(constraints, forced_units,
    /// inconsistent)`.
    pub(super) fn xor_probe(&mut self) -> (usize, usize, bool) {
        if self.trail.decision_level() != 0
            || self.proof.is_some()
            || self.lrat
            || self.real_theory_attached
            || self.assertion_levels.len() > 1
            || self.trivially_unsat
        {
            return (0, 0, false);
        }
        use crate::literal::Lit;
        use crate::xor::GF2Matrix;
        let constraints = self.detect_xor_constraints();
        if constraints.is_empty() {
            return (0, 0, false);
        }
        let n_constraints = constraints.len();

        // ---- 1. Build the matrix; add-time units are forced at level 0.
        let mut matrix = GF2Matrix::new();
        let mut pending: SmallVec<[Lit; 16]> = SmallVec::new();
        let mut inconsistent = false;
        for c in &constraints {
            let vars: Vec<crate::literal::Var> = c
                .vars
                .iter()
                .map(|v| crate::literal::Var::new(*v))
                .collect();
            match matrix.add_constraint(&vars, c.rhs, 0) {
                crate::xor::XorAddResult::Unit(v, val, _) => {
                    pending.push(if val { Lit::pos(v) } else { Lit::neg(v) });
                }
                crate::xor::XorAddResult::Conflict(_) => {
                    inconsistent = true;
                    break;
                }
                _ => {}
            }
        }
        if inconsistent {
            return (n_constraints, 0, true);
        }
        // ---- 2. Level-0 fixpoint: force units, fold every new trail
        // literal, collect newly pinned units.
        let mut forced_units = 0usize;
        let mut folded_level0 = 0usize;
        loop {
            // Fold everything not yet folded.
            while folded_level0 < self.trail.assignments().len() {
                let lit = self.trail.assignments()[folded_level0];
                folded_level0 += 1;
                for res in matrix.propagate(lit.var(), lit.is_pos()) {
                    if let crate::xor::XorAddResult::Unit(v, val, _) = res {
                        pending.push(if val { Lit::pos(v) } else { Lit::neg(v) });
                    }
                }
            }
            let Some(lit) = pending.pop() else { break };
            if matches!(self.trail.lit_value(lit), crate::literal::LBool::Undef) {
                self.force_level0(lit);
                forced_units += 1;
                if self.trivially_unsat {
                    // A forced unit conflicted with the CNF: the formula
                    // is UNSAT — reported, not answered.
                    return (n_constraints, forced_units, true);
                }
            }
        }

        // ---- 3. Probe each remaining matrix variable, both polarities.
        let probe_vars: Vec<crate::literal::Var> = {
            let mut vs: Vec<_> = (0..self.num_vars)
                .map(|i| crate::literal::Var::new(i as u32))
                .filter(|v| !self.trail.is_assigned(*v) && matrix.contains_var(*v))
                .collect();
            vs.sort_by_key(|v| v.index());
            vs
        };
        for v in probe_vars {
            if self.trivially_unsat {
                break;
            }
            if self.trail.is_assigned(v) {
                continue;
            }
            let mut failed = [false, false]; // [v=false failed, v=true failed]
            for polarity in [false, true] {
                let mark = self.trail.assignments().len();
                self.trail.new_decision_level();
                self.trail
                    .assign_decision(if polarity { Lit::pos(v) } else { Lit::neg(v) });
                let mut conflict = false;
                // CNF propagate + fold loop: XOR units assigned during the
                // loop extend the trail and are folded in the same pass.
                let mut folded = mark;
                loop {
                    if self.propagate().is_some() {
                        conflict = true;
                        break;
                    }
                    while folded < self.trail.assignments().len() {
                        let lit = self.trail.assignments()[folded];
                        folded += 1;
                        for res in matrix.propagate(lit.var(), lit.is_pos()) {
                            match res {
                                crate::xor::XorAddResult::Unit(uv, uval, _) => {
                                    let lit2 = if uval { Lit::pos(uv) } else { Lit::neg(uv) };
                                    match self.trail.lit_value(lit2) {
                                        crate::literal::LBool::Undef => {
                                            self.trail.assign_decision(lit2);
                                        }
                                        crate::literal::LBool::False => {
                                            conflict = true;
                                        }
                                        crate::literal::LBool::True => {}
                                    }
                                }
                                crate::xor::XorAddResult::Conflict(_) => {
                                    conflict = true;
                                }
                                _ => {}
                            }
                            if conflict {
                                break;
                            }
                        }
                        if conflict {
                            break;
                        }
                    }
                    if conflict || folded >= self.trail.assignments().len() {
                        break;
                    }
                }
                failed[polarity as usize] = conflict;
                // Undo folds in exact reverse trail order, then backtrack.
                while folded > mark {
                    folded -= 1;
                    let lit = self.trail.assignments()[folded];
                    let _ = matrix.undo_propagate();
                    let _ = lit;
                }
                self.backtrack(0);
            }
            match failed {
                [false, true] => {
                    self.force_level0(Lit::neg(v));
                    forced_units += 1;
                    // Fold the newly forced level-0 literals permanently.
                    while folded_level0 < self.trail.assignments().len() {
                        let lit = self.trail.assignments()[folded_level0];
                        folded_level0 += 1;
                        for res in matrix.propagate(lit.var(), lit.is_pos()) {
                            if let crate::xor::XorAddResult::Unit(uv, uval, _) = res {
                                pending.push(if uval { Lit::pos(uv) } else { Lit::neg(uv) });
                            }
                        }
                    }
                }
                [true, false] => {
                    self.force_level0(Lit::pos(v));
                    forced_units += 1;
                    while folded_level0 < self.trail.assignments().len() {
                        let lit = self.trail.assignments()[folded_level0];
                        folded_level0 += 1;
                        for res in matrix.propagate(lit.var(), lit.is_pos()) {
                            if let crate::xor::XorAddResult::Unit(uv, uval, _) = res {
                                pending.push(if uval { Lit::pos(uv) } else { Lit::neg(uv) });
                            }
                        }
                    }
                }
                [true, true] => {
                    // Both polarities fail: formula UNSAT — reported.
                    return (n_constraints, forced_units, true);
                }
                [false, false] => {}
            }
            // Drain any pending units (loop back to the fixpoint shape).
            loop {
                while folded_level0 < self.trail.assignments().len() {
                    let lit = self.trail.assignments()[folded_level0];
                    folded_level0 += 1;
                    for res in matrix.propagate(lit.var(), lit.is_pos()) {
                        if let crate::xor::XorAddResult::Unit(uv, uval, _) = res {
                            pending.push(if uval { Lit::pos(uv) } else { Lit::neg(uv) });
                        }
                    }
                }
                let Some(lit) = pending.pop() else { break };
                if matches!(self.trail.lit_value(lit), crate::literal::LBool::Undef) {
                    self.force_level0(lit);
                    forced_units += 1;
                    if self.trivially_unsat {
                        return (n_constraints, forced_units, true);
                    }
                }
            }
        }
        (n_constraints, forced_units, false)
    }
}
