//! Assignment trail for CDCL solver

use crate::clause::ClauseId;
use crate::literal::{LBool, Lit, Var};
#[allow(unused_imports)]
use crate::prelude::*;

/// Reason for an assignment
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reason {
    /// Decision (no antecedent)
    Decision,
    /// Unit propagation from a clause
    Propagation(ClauseId),
    /// Theory propagation
    Theory,
}

/// Information about a variable assignment
#[derive(Debug, Clone, Copy)]
pub struct VarInfo {
    /// Current value
    pub value: LBool,
    /// Decision level at which assigned
    pub level: u32,
    /// Reason for assignment
    pub reason: Reason,
    /// Position in trail
    #[allow(dead_code)]
    pub trail_idx: u32,
}

impl Default for VarInfo {
    fn default() -> Self {
        Self {
            value: LBool::Undef,
            level: 0,
            reason: Reason::Decision,
            trail_idx: 0,
        }
    }
}

/// The assignment trail
#[derive(Debug)]
pub struct Trail {
    /// Sequence of assigned literals
    assignments: Vec<Lit>,
    /// Per-literal truth value indexed by `Lit::code()`: `+1` = true,
    /// `-1` = false, `0` = undefined. Length is `2 * num_vars`. The hottest
    /// BCP lookup (`lit_val`) is a single unchecked byte load; the
    /// per-variable accessors read index `2 * var`. Kept separate from
    /// `var_info` so value reads don't pay the wider `VarInfo` stride.
    values: Vec<i8>,
    /// Information for each variable (level / reason – the cold path)
    var_info: Vec<VarInfo>,
    /// Indices marking the start of each decision level
    level_starts: Vec<usize>,
    /// Current decision level
    current_level: u32,
    /// Propagation queue head
    prop_head: usize,
}

impl Trail {
    /// Create a new trail for n variables
    #[must_use]
    pub fn new(num_vars: usize) -> Self {
        Self {
            assignments: Vec::with_capacity(num_vars),
            values: vec![0; num_vars * 2],
            var_info: vec![VarInfo::default(); num_vars],
            level_starts: vec![0],
            current_level: 0,
            prop_head: 0,
        }
    }

    /// Get the decision variable chosen at decision `level` (1-indexed), or
    /// `None` for level 0 or an out-of-range level. Used by reuse-trail restarts.
    #[must_use]
    pub fn decision_var_at_level(&self, level: u32) -> Option<Var> {
        if level == 0 {
            return None;
        }
        let idx = *self.level_starts.get(level as usize)?;
        let lit = self.assignments.get(idx)?;
        // The first assignment at a level is its decision literal.
        if matches!(
            self.var_info.get(lit.var().index())?.reason,
            Reason::Decision
        ) {
            Some(lit.var())
        } else {
            None
        }
    }

    /// Get the current decision level
    #[must_use]
    pub fn decision_level(&self) -> u32 {
        self.current_level
    }

    /// Trail index at which decision `level` starts (the prefix length that
    /// precedes it); `level_starts[level]`, so the trail slice of level `l`
    /// is `level_start(l)..level_start(l+1)`.  Level 0 always maps to `0`.
    ///
    /// cadical's `control[level].trail`: the conflict-free prefix recorded as
    /// `no_conflict_until` when a conflict fires on the current decision
    /// level is exactly `level_start(decision_level())`.
    #[must_use]
    pub fn level_start(&self, level: u32) -> usize {
        self.level_starts
            .get(level as usize)
            .copied()
            .unwrap_or(self.assignments.len())
    }

    /// Raw per-literal truth value: `+1` true, `-1` false, `0` undefined.
    /// The hottest BCP lookup – a single byte load indexed by literal code
    /// (no enum match, no sign branch). The solver maintains `values` at
    /// length `2 * num_vars` (grown only by `resize`, never shrunk — see
    /// `unassign`), so `lit.code()` is always in range and the direct index
    /// skips the `Option` bounds-check dance the `.get()` version paid on
    /// every watch visit.
    #[inline(always)]
    #[must_use]
    pub fn lit_val(&self, lit: Lit) -> i8 {
        self.values[lit.code() as usize]
    }

    /// Hot-path variant of [`Self::lit_val`] for the propagation scan:
    /// unchecked index.
    ///
    /// **Documented `unsafe` exception** (the crate denies `unsafe_code`;
    /// this is the single scoped escape in `trail.rs`, mirroring
    /// `memory.rs`'s module-level exception with its safety model): the
    /// index is in-bounds by construction — `values` is sized to cover
    /// every encodable literal by [`Self::resize`], and `Lit::code()` is
    /// `2·var + sign` with `var < num_vars` for every literal the solver
    /// constructs.  The elided bounds check was measured as part of the
    /// propagate `lit_val` bucket (~3 % of search time on noL,
    /// 2026-08-21); `debug_assert!` retains the check in dev builds.
    /// Scope discipline: propagation-scan call sites only.
    #[allow(unsafe_code)]
    #[inline]
    pub fn lit_val_hot(&self, lit: Lit) -> i8 {
        debug_assert!((lit.code() as usize) < self.values.len());
        // SAFETY: see the doc comment — `resize` guarantees the capacity.
        unsafe { *self.values.get_unchecked(lit.code() as usize) }
    }

    /// Get the value of a variable
    #[must_use]
    pub fn value(&self, var: Var) -> LBool {
        match self.values.get(var.index() << 1).copied().unwrap_or(0) {
            x if x > 0 => LBool::True,
            x if x < 0 => LBool::False,
            _ => LBool::Undef,
        }
    }

    /// Get the value of a literal
    #[must_use]
    pub fn lit_value(&self, lit: Lit) -> LBool {
        match self.lit_val(lit) {
            x if x > 0 => LBool::True,
            x if x < 0 => LBool::False,
            _ => LBool::Undef,
        }
    }

    /// Check if a variable is assigned
    #[must_use]
    pub fn is_assigned(&self, var: Var) -> bool {
        self.values.get(var.index() << 1).copied().unwrap_or(0) != 0
    }

    /// Get the level at which a variable was assigned
    #[must_use]
    pub fn level(&self, var: Var) -> u32 {
        self.var_info.get(var.index()).map_or(0, |v| v.level)
    }

    /// Overwrite the recorded reason of an assigned variable (see the
    /// deleted-reason hygiene in `Solver::retire_clause`). Used by
    /// deletion paths that retire a clause still referenced as a reason:
    /// they re-point the reference to `Decision` (no antecedent), which is
    /// exactly the semantics a level-0 fact carries in cadical
    /// (`v.reason = level ? ... : 0`) – and conflict analysis never
    /// resolves through a decision reason.
    pub(super) fn set_reason(&mut self, var: Var, reason: Reason) {
        if let Some(info) = self.var_info.get_mut(var.index()) {
            info.reason = reason;
        }
    }

    /// Get the reason for a variable's assignment.
    #[must_use]
    pub fn reason(&self, var: Var) -> Reason {
        self.var_info
            .get(var.index())
            .map_or(Reason::Decision, |v| v.reason)
    }

    /// Get the trail position (assignment order) at which a variable was
    /// assigned. Used to order literals for recursive minimization.
    #[must_use]
    pub fn trail_index(&self, var: Var) -> u32 {
        self.var_info.get(var.index()).map_or(0, |v| v.trail_idx)
    }

    /// Start a new decision level
    pub fn new_decision_level(&mut self) {
        self.current_level += 1;
        self.level_starts.push(self.assignments.len());
    }

    /// Assign a literal as a decision
    pub fn assign_decision(&mut self, lit: Lit) {
        self.assign(lit, Reason::Decision);
    }

    /// Assign a literal due to propagation
    pub fn assign_propagation(&mut self, lit: Lit, clause: ClauseId) {
        self.assign(lit, Reason::Propagation(clause));
    }

    /// Assign a literal due to theory propagation
    pub fn assign_theory(&mut self, lit: Lit) {
        self.assign(lit, Reason::Theory);
    }

    #[inline]
    fn assign(&mut self, lit: Lit, reason: Reason) {
        let var = lit.var();
        let idx = var.index();
        let code = lit.code() as usize;

        // Resize if needed. `new_var` normally sizes us up front, so this is
        // only hit by the small standalone tests that assign without `new_var`.
        // Kept out-of-line and cold: with the grow path split off, the hot
        // core is small enough to inline into the BCP assignment sites
        // (2026-09-07; previously a real `call` per BIG-edge propagation).
        if idx >= self.var_info.len() {
            self.assign_grow(idx);
        }

        let value = if lit.is_pos() {
            LBool::True
        } else {
            LBool::False
        };

        // `values` is the per-literal truth array (length `2 * (idx+1)`),
        // so both `code` and `code ^ 1` index it in range.
        self.values[code] = 1;
        self.values[code ^ 1] = -1;
        self.var_info[idx] = VarInfo {
            value,
            level: self.current_level,
            reason,
            trail_idx: self.assignments.len() as u32,
        };

        self.assignments.push(lit);
    }

    /// Cold half of [`Self::assign`]: the rare "assigned beyond the sized
    /// range" path (standalone tests only – `new_var` sizes both arrays up
    /// front in solver use).
    #[cold]
    #[inline(never)]
    fn assign_grow(&mut self, idx: usize) {
        self.var_info.resize(idx + 1, VarInfo::default());
        let need = (idx + 1) * 2;
        if self.values.len() < need {
            self.values.resize(need, 0);
        }
    }

    /// Get the next literal to propagate (if any)
    pub fn next_to_propagate(&mut self) -> Option<Lit> {
        if self.prop_head < self.assignments.len() {
            let lit = self.assignments[self.prop_head];
            self.prop_head += 1;
            Some(lit)
        } else {
            None
        }
    }

    /// Check if there are literals to propagate
    #[must_use]
    pub fn has_pending_propagation(&self) -> bool {
        self.prop_head < self.assignments.len()
    }

    /// Get the current size of the trail (number of assignments)
    #[must_use]
    pub fn size(&self) -> usize {
        self.assignments.len()
    }

    /// Backtrack to a specific trail size (number of assignments)
    /// This is useful for incremental solving where we want to restore
    /// the exact state at a push point
    pub fn backtrack_to_size(&mut self, target_size: usize) {
        while self.assignments.len() > target_size {
            let lit = self
                .assignments
                .pop()
                .expect("assignments non-empty in loop condition");
            let code = lit.code() as usize;
            // Zero both polarities to restore "undefined".
            self.values[code] = 0;
            self.values[code ^ 1] = 0;
            self.var_info[lit.var().index()].value = LBool::Undef;
        }
        // Reset decision level tracking
        self.current_level = 0;
        self.level_starts.truncate(1);
        self.prop_head = self.assignments.len();
    }

    /// Backtrack to a given decision level
    pub fn backtrack_to(&mut self, level: u32) {
        self.backtrack_to_with_callback(level, |_| {});
    }

    /// Backtrack to a given decision level, calling the callback for each unassigned literal
    /// Backtrack to `level` with **level-filtered** semantics (cadical
    /// `backtrack.cpp`'s out-of-order design, SAT'18 chronological
    /// backtracking): unassign exactly the literals whose **recorded decision
    /// level** exceeds `level`, and keep – compacting in place – every
    /// literal above the level boundary whose recorded level is ≤ `level`.
    ///
    /// The previous suffix-pop ("unassign everything positioned above
    /// `level_starts[level+1]`") is unsound once the trail can hold
    /// out-of-order literals – assignments recorded at a level *below* the
    /// level they were appended at.  Such literals are created by
    /// [`Trail::assign_propagation_at`] (chronological backtracking's
    /// asserting literal, recorded at its true implication level while the
    /// search sits above it).  A later suffix-pop backtracks *past* them
    /// positionally even though their recorded level says they survive,
    /// silently dropping justified assignments; clauses that were unit
    /// through them stop being enforced and the propagation-fixpoint
    /// invariant breaks – reproduced by `chronoalways` on the `pmres`
    /// stratified test (hanging unit `[-65, 64, 62]`, levels `[0, 8, 3]`,
    /// unassigned through a positional pop despite recorded level 8 ≤ the
    /// stop level).
    ///
    /// Soundness of the keep-by-level rule rests on the trail's recording
    /// invariant: a propagated literal's recorded level is the **maximum**
    /// of its reason's literal levels (`assign_propagation_at`; BCP's
    /// `assign_propagation` records `current_level`, itself an upper bound
    /// over every trail position).  Hence every reason literal of a kept
    /// literal has level ≤ the kept literal's level ≤ `level`, so kept
    /// literals never dangle; and a clause that is unit over kept literals
    /// has its open literal recorded at ≥ all their levels, so it is kept
    /// too – no hanging units.
    ///
    /// The propagation head is clamped to the level boundary (cadical
    /// `propagated = assigned`): the kept out-of-order region above the
    /// boundary is re-examined by the next `propagate` pass, re-deriving
    /// consequences whose originals were unassigned.  Re-processing is
    /// idempotent – satisfied first-watches short-circuit, already-derived
    /// units re-assert identically – and, per the invariant above, cannot
    /// produce conflicts among kept literals (they were mutually consistent
    /// at the last fixpoint each was appended in).
    pub fn backtrack_to_with_callback<F>(&mut self, level: u32, mut callback: F)
    where
        F: FnMut(Lit),
    {
        if level >= self.current_level {
            return;
        }

        let boundary = self.level_starts[(level + 1) as usize];

        // Unassign by recorded level; compact the survivors in place.
        let mut write = boundary;
        for read in boundary..self.assignments.len() {
            let lit = self.assignments[read];
            if self.var_info[lit.var().index()].level > level {
                let code = lit.code() as usize;
                self.values[code] = 0;
                self.values[code ^ 1] = 0;
                // Reset the full VarInfo (not just `.value`): leaving `.level`
                // stale after backtracking made `Trail::level` report the *old*
                // decision level for unassigned variables. That corrupted every
                // consumer of levels on unassigned vars – most importantly
                // `compute_lbd`, which is computed on the freshly-learned
                // clause *after* backtracking (so its literals above the
                // backtrack level read stale levels and produced garbage glue),
                // and the Glucose-style restart EMA.
                self.var_info[lit.var().index()] = VarInfo::default();
                callback(lit);
            } else {
                // Kept out-of-order literal: compact down and refresh its
                // trail index (reasons, watchers and `decision_var_at_level`
                // are unaffected – the decision of each level stays at
                // `level_starts[level]`, appended there by
                // `new_decision_level` + `assign_decision` before anything
                // else could interleave).
                self.assignments[write] = lit;
                self.var_info[lit.var().index()].trail_idx = write as u32;
                write += 1;
            }
        }
        self.assignments.truncate(write);

        self.level_starts.truncate((level + 1) as usize);
        self.current_level = level;
        // Clamp (never extend) the propagation head to the level boundary:
        // kept literals at or above it are re-processed by the next pass.
        self.prop_head = self.prop_head.min(boundary);
    }

    /// Get the number of assigned variables
    #[must_use]
    pub fn num_assigned(&self) -> usize {
        self.assignments.len()
    }

    /// Get all assignments
    #[must_use]
    pub fn assignments(&self) -> &[Lit] {
        &self.assignments
    }

    /// Get assignments at current level
    #[must_use]
    pub fn level_assignments(&self) -> &[Lit] {
        let start = *self.level_starts.last().unwrap_or(&0);
        &self.assignments[start..]
    }

    /// Resize to support more variables
    pub fn resize(&mut self, num_vars: usize) {
        let lit_cap = num_vars * 2;
        if lit_cap > self.values.len() {
            self.values.resize(lit_cap, 0);
        }
        if num_vars > self.var_info.len() {
            self.var_info.resize(num_vars, VarInfo::default());
        }
    }

    /// Clear the trail completely
    pub fn clear(&mut self) {
        for &lit in &self.assignments {
            let code = lit.code() as usize;
            self.values[code] = 0;
            self.values[code ^ 1] = 0;
            self.var_info[lit.var().index()].value = LBool::Undef;
        }
        self.assignments.clear();
        self.level_starts.clear();
        self.level_starts.push(0);
        self.current_level = 0;
        self.prop_head = 0;
    }
}

// ======== pr/sat additions (upstream/API functions main's trail.rs lacks) ========
// Representation-independent (prop_head only, or delegate to assign_at).
impl Trail {
    /// Level-aware assign: main's `assign` hard-codes `current_level`, but the
    /// effective-unit / asserting-literal paths must install a literal at an
    /// explicit level (the falsifying literal's level, or 0 for a root fact).
    /// Mirrors `assign` exactly except for the `VarInfo.level` field.
    fn assign_at(&mut self, lit: Lit, reason: Reason, level: u32) {
        let var = lit.var();
        let idx = var.index();
        let code = lit.code() as usize;
        if idx >= self.var_info.len() {
            self.var_info.resize(idx + 1, VarInfo::default());
            let need = (idx + 1) * 2;
            if self.values.len() < need {
                self.values.resize(need, 0);
            }
        }
        let value = if lit.is_pos() {
            LBool::True
        } else {
            LBool::False
        };
        self.values[code] = 1;
        self.values[code ^ 1] = -1;
        self.var_info[idx] = VarInfo {
            value,
            level,
            reason,
            trail_idx: self.assignments.len() as u32,
        };
        self.assignments.push(lit);
    }

    /// Assign `lit` as a propagation with reason `clause` at decision `level`.
    pub fn assign_propagation_at(&mut self, lit: Lit, clause: ClauseId, level: u32) {
        self.assign_at(lit, Reason::Propagation(clause), level);
    }

    /// Assign `lit` as a permanent level-0 fact (decision reason, level 0).
    pub fn assign_unit_fact(&mut self, lit: Lit) {
        self.assign_at(lit, Reason::Decision, 0);
    }

    /// Index of the propagation head: every literal strictly before it has had
    /// all of its consequences computed.
    pub fn propagation_head(&self) -> usize {
        self.prop_head
    }

    /// Decrement the propagation head by one, re-queuing the most recently
    /// dequeued literal (used when bailing out of a watch-list scan before the
    /// literal is fully propagated).
    pub fn requeue_last_propagated(&mut self) {
        debug_assert!(
            self.prop_head > 0,
            "requeue_last_propagated requires a literal to have been dequeued"
        );
        self.prop_head = self.prop_head.saturating_sub(1);
    }

    /// Reset the propagation head to 0, forcing the whole trail to be
    /// re-propagated on the next propagation pass.
    /// Rewind the propagation head to the start of the trail.
    ///
    /// Used after a clause is strengthened in place, or after a probe pass
    /// (`vivify` / failed-literal probing / `inprocess`) opened decision
    /// levels: a watch only ever fires when its literal is *newly* falsified,
    /// so a clause that becomes unit under an assignment already on the trail
    /// has no future event to fire on — a "hanging unit" that silently loses
    /// an implication (and a probe's `propagate()` drains still-pending
    /// level-0 literals *at the probe level*, whose backtrack then discards
    /// the consequences).  Re-propagating a literal that is still assigned is
    /// a no-op, so rewinding is always safe; it only costs one extra pass
    /// over the retained watch lists. (Doc from upstream v0.3.3.)
    pub fn reset_propagation_head(&mut self) {
        self.prop_head = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_trail_basic() {
        let mut trail = Trail::new(5);

        assert_eq!(trail.decision_level(), 0);
        assert!(!trail.is_assigned(Var::new(0)));

        trail.new_decision_level();
        trail.assign_decision(Lit::pos(Var::new(0)));

        assert_eq!(trail.decision_level(), 1);
        assert!(trail.is_assigned(Var::new(0)));
        assert!(trail.lit_value(Lit::pos(Var::new(0))).is_true());
        assert!(trail.lit_value(Lit::neg(Var::new(0))).is_false());
    }

    #[test]
    fn test_trail_backtrack() {
        let mut trail = Trail::new(5);

        trail.new_decision_level();
        trail.assign_decision(Lit::pos(Var::new(0)));

        trail.new_decision_level();
        trail.assign_decision(Lit::neg(Var::new(1)));

        assert_eq!(trail.decision_level(), 2);
        assert_eq!(trail.num_assigned(), 2);

        trail.backtrack_to(1);

        assert_eq!(trail.decision_level(), 1);
        assert_eq!(trail.num_assigned(), 1);
        assert!(trail.is_assigned(Var::new(0)));
        assert!(!trail.is_assigned(Var::new(1)));
    }

    #[test]
    fn test_trail_propagation() {
        let mut trail = Trail::new(5);

        trail.new_decision_level();
        trail.assign_decision(Lit::pos(Var::new(0)));
        trail.assign_propagation(Lit::neg(Var::new(1)), ClauseId::new(0));

        assert!(trail.has_pending_propagation());
        assert_eq!(trail.next_to_propagate(), Some(Lit::pos(Var::new(0))));
        assert_eq!(trail.next_to_propagate(), Some(Lit::neg(Var::new(1))));
        assert!(!trail.has_pending_propagation());
    }
}
