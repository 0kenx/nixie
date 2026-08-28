//! Bounded blocking of refuted candidate models (upstream issue #40).
//!
//! [`Solver::model_refutes_assertions`] is the last gate before a `Sat` leaves
//! the ground branch of `check_core`.  When it fires, the candidate assignment
//! on the table is not a model of the assertions — but *the search was not
//! finished*, and the formula may well have other models the CDCL(T) core
//! would have reached had it been asked to keep going.  Conceding `Unknown` on
//! the first unlucky candidate turned every single one into a lost `sat`.
//!
//! This module supplies the missing step: **exclude that one assignment and
//! re-solve**, up to the configured round budget.
//!
//! # A search restriction, not a lemma — and why that distinction is the
//! whole soundness argument
//!
//! A blocking clause here is emphatically **not** a consequence of the
//! assertions.  The gate fires on two different things (see
//! [`super::model_eval::EvalOutcome`]):
//!
//! * `Value(Bool(false))` — the model genuinely falsifies an assertion.  A
//!   clause excluding it *would* be entailed.
//! * `Unrepresentable` — the *evaluator's* fixed-width `Rational64` arithmetic
//!   could not represent an intermediate result.  That is a statement about
//!   the evaluator, not about the assignment: the assignment may be a
//!   perfectly good model that this particular checker cannot certify.  A
//!   clause excluding it is entailed by **nothing**.
//!
//! Because the second trigger exists, the clauses this module adds are treated
//! as a *restriction of the search space*, not as knowledge:
//!
//! * A `Sat` found afterwards is still a real `Sat` — it is a surviving
//!   assignment, re-verified by the same gate, and a restricted search can
//!   only ever return genuine models of the unrestricted problem.
//! * An `Unsat` found afterwards means "no model outside the excluded region",
//!   which is **not** `unsat`.  While [`Solver::model_blocking_active`] is
//!   nonzero, every SAT-core-derived `Unsat` is therefore surfaced as
//!   [`SolverResult::Unknown`] with no unsat core — see
//!   [`Solver::blocking_clauses_present`].
//!
//! The verdict lattice this produces is `Unknown -> {Sat, Unknown}`: the
//! feature can only ever upgrade the old spurious `Unknown` into a `Sat`,
//! never turn any answer into a worse or a wrong one.
//!
//! (This replaces this fork's earlier inline `block_current_model`, which
//! negated the *decision path* but never downgraded a later `Unsat` over its
//! own clauses — the restriction-vs-lemma distinction above is exactly what
//! that mechanism was missing.)
//!
//! # Two opposite-direction "drop a literal" rules
//!
//! 1. **MBQI's all-or-nothing reason clause** turns a *reason* — a set of
//!    terms whose conjunction the quantifier refutes — into a blocking
//!    clause.  Dropping a reason term that names no SAT literal there does
//!    not weaken the clause, it **strengthens** it into a claim the reason
//!    never made.
//!
//! 2. **Here the clause is a projection, not a reason.**  Its meaning is "not
//!    exactly this assignment (restricted to the mapped variables)", and a
//!    projection onto fewer variables is a *stronger* restriction that
//!    excludes a superset of assignments — sound in this direction precisely
//!    because the clause is a search restriction whose `Unsat` is already
//!    downgraded.  What is *not* acceptable is projecting onto **nothing**:
//!    an empty clause is the false clause.  An empty projection **declines**
//!    (`false`), leaving the caller to concede `Unknown` exactly as before.
//!
//! A variable the SAT core left `Undef` is dropped, never guessed: both
//! polarities are consistent with what the search committed to, and guessing
//! one would leave the sibling assignment unblocked, burning the round budget
//! without progress.
//!
//! # Scoping
//!
//! The clauses are added with [`oxiz_sat::Solver::add_clause`], so they live
//! at the SAT core's current scope and are retracted by `Solver::pop`'s
//! `self.sat.pop()` along with everything else that scope added.  The
//! `model_blocking_active` counter is snapshotted in
//! [`super::trail::ContextState`] so it is restored in lockstep.
//!
//! (Ported from upstream v0.3.3.  Adaptation: this fork removed the
//! wall-clock refinement ceiling on principle — "an overall unaffordable
//! search is the user's `timeout_ms`'s business" — so the round budget is the
//! only bound here, with no `affordable` gate.)

use oxiz_sat::{LBool, Lit, Var};

use super::Solver;

impl Solver {
    /// `true` iff at least one model-blocking clause is live in the SAT
    /// database, so a SAT-core-derived `Unsat` must be surfaced as `Unknown`.
    ///
    /// Every call site that turns an `oxiz_sat::SatResult::Unsat` into an
    /// [`crate::SolverResult::Unsat`] must consult this first; the syntactic
    /// early-conflict detectors (`check_string_constraints` and friends), the
    /// `has_false_assertion` fast path and the nonlinear dispatch do not,
    /// because none of them reads the SAT clause database.
    pub(super) fn blocking_clauses_present(&self) -> bool {
        self.model_blocking_active > 0
    }

    /// The clause that excludes the assignment currently on the SAT trail:
    /// the negation of that assignment, projected onto the SAT variables that
    /// carry a term.
    ///
    /// An unmapped SAT variable is a Tseitin auxiliary with no meaning
    /// outside the encoding, and a variable the core left `Undef` is one the
    /// candidate does not constrain; both are omitted.  See the module header
    /// for why omitting is the correct direction here and the wrong one in
    /// MBQI's reason clause.
    ///
    /// Split out from [`Self::block_refuted_model`] so the projection rule can
    /// be tested literal by literal, independently of the budget and of the
    /// SAT database it would otherwise be written into.
    pub(super) fn refuted_model_projection(&self) -> Vec<Lit> {
        let mut lits: Vec<Lit> = Vec::with_capacity(self.var_to_term.len());
        for idx in 0..self.var_to_term.len() {
            // `var_to_term` is indexed by SAT variable index, which
            // `oxiz_sat::Var` stores as a `u32`; a length past `u32::MAX` is
            // unreachable, and skipping is the sound response either way (a
            // shorter projection is a stronger restriction, never a wrong
            // one).
            let Ok(raw) = u32::try_from(idx) else {
                continue;
            };
            let var = Var::new(raw);
            match self.sat.model_value(var) {
                LBool::True => lits.push(Lit::neg(var)),
                LBool::False => lits.push(Lit::pos(var)),
                // Deliberately dropped, never guessed — see the module header.
                LBool::Undef => {}
            }
        }
        lits
    }

    /// Exclude the candidate assignment currently on the SAT trail.
    ///
    /// Returns `true` when a blocking clause was added (the caller owes a
    /// theory rebase and a re-solve) and `false` when this module declines —
    /// the feature is off, the round budget is spent, or the assignment
    /// projects onto no mapped variable at all.  On `false` the solver is
    /// left exactly as it was found.
    ///
    /// # Why `add_clause` returning `false` still counts as blocked
    ///
    /// `false` from [`oxiz_sat::Solver::add_clause`] means the clause was
    /// refused as an unconditional (level-0) conflict — the SAT core is now
    /// trivially unsat.  That is still a *successful* restriction of the
    /// search space, and the counter has already been bumped, so the next
    /// solve reports `Unsat` and [`Self::blocking_clauses_present`]
    /// downgrades it to `Unknown`.  Reporting `false` here instead would let
    /// the caller return `Sat` for the very model it just refuted.
    pub(super) fn block_refuted_model(&mut self) -> bool {
        if !self.config.enable_model_blocking {
            return false;
        }
        if self.model_blocking_active >= self.config.max_model_blocking_rounds {
            return false;
        }

        let lits = self.refuted_model_projection();
        if lits.is_empty() {
            // An empty clause is the false clause, not "block this one
            // assignment".  Decline rather than poison the database.
            return false;
        }

        self.model_blocking_active += 1;
        self.statistics.model_blocking_clauses += 1;
        // The return value is intentionally ignored: see the doc comment.
        let _ = self.sat.add_clause(lits);
        true
    }

    /// [`Self::block_refuted_model`] plus the state repair every re-solve in
    /// `check_core` owes before it continues.
    ///
    /// `add_clause` left the SAT core at the refuted candidate's trail, and
    /// the incremental theory solvers still hold that candidate's facts (only
    /// level-scoped `pop` is available, no surgical undo), so the next round
    /// must be driven from a rebased state — exactly as the case-split and
    /// array-axiom repair paths do.
    pub(super) fn block_refuted_model_and_rebase(&mut self) -> bool {
        if !self.block_refuted_model() {
            return false;
        }
        self.rebase_theory_state();
        self.debug_check_invariants("check_core: after model-blocking backtrack");
        true
    }
}

#[cfg(test)]
mod tests;
