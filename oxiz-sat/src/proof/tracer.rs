//! Proof tracer abstraction – faithful port of `tracer.hpp`.
//!
//! [`Tracer`] is the abstract observer base class from upstream: every proof
//! event the solver emits (clause added / deleted / finalized, assumptions,
//! status, conclusions, …) is reported through it. Concrete tracers
//! ([`crate::proof::drat::DratTracer`], [`crate::proof::lrat::LratTracer`])
//! implement the trait; the [`crate::proof::Proof`] manager fans each event
//! out to every attached tracer.
//!
//! All methods default to no-ops (matching the C++ `virtual … {}` base), so a
//! tracer only overrides the events it cares about. File tracers additionally
//! override [`Tracer::flush`]/[`Tracer::close`]/[`Tracer::closed`].
//!
//! Internal literals in oxiz-sat are external (DIMACS) literals – there is no
//! `External` variable-mapping layer – so clauses are passed through verbatim.

/// How an UNSAT conclusion was reached (matches `ConclusionType` in
/// `tracer.hpp`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(i32)]
pub enum ConclusionType {
    /// The empty derived clause.
    Conflict = 1,
    /// A failing-assumption clause.
    Assumptions = 2,
    /// Failing-constraint assumption clauses.
    Constraint = 4,
}

pub const CONFLICT: ConclusionType = ConclusionType::Conflict;
pub const ASSUMPTIONS: ConclusionType = ConclusionType::Assumptions;
pub const CONSTRAINT: ConclusionType = ConclusionType::Constraint;

/// The abstract proof-tracer interface (`class Tracer`).
///
/// Mirrors `tracer.hpp`: every method carries the upstream signature and
/// defaults to a no-op so a tracer overrides only the events it needs.
#[allow(unused_variables)]
pub trait Tracer {
    // ======== lifecycle ========

    /// `closed` – whether a file tracer's backing file is closed (default
    /// `true` for in-memory tracers).
    fn closed(&self) -> bool {
        true
    }
    /// `close` – close the backing file (file tracers).
    fn close(&mut self, print: bool) {}
    /// `flush` – flush the backing file (file tracers).
    fn flush(&mut self, print: bool) {}

    // ======== basic events ========

    /// An original clause was added (`id`, redundant, clause, restored).
    fn add_original_clause(&mut self, id: i64, redundant: bool, clause: &[i32], restored: bool) {}

    /// A clause was derived (`id`, redundant, witness, clause, LRAT chain).
    /// A non-zero `witness` marks a RAT clause.
    fn add_derived_clause(
        &mut self,
        id: i64,
        redundant: bool,
        witness: i32,
        clause: &[i32],
        chain: &[i64],
    ) {
    }

    /// A clause was deleted (`id`, redundant, clause).
    fn delete_clause(&mut self, id: i64, redundant: bool, clause: &[i32]) {}

    /// An irredundant clause was demoted to redundant.
    fn demote_clause(&mut self, id: u64, clause: &[i32]) {}

    /// A clause is marked for later restoration (`weaken minus`).
    fn weaken_minus(&mut self, id: i64, clause: &[i32]) {}

    /// A clause was strengthened (a literal removed); report by id.
    fn strengthen(&mut self, id: i64) {}

    /// A clause is finalized (`id`, clause).
    fn finalize_clause(&mut self, id: i64, clause: &[i32]) {}

    /// The solver reports its final status (`status`, empty-clause id).
    fn report_status(&mut self, status: i32, id: i64) {}

    /// The proof begins; `id` is the first derived-clause id.
    fn begin_proof(&mut self, id: i64) {}

    // ======== incremental events ========

    /// A `solve` query begins (assumptions/constraints follow).
    fn solve_query(&mut self) {}

    /// An assumption literal was added.
    fn add_assumption(&mut self, lit: i32) {}

    /// A constraint clause was added.
    fn add_constraint(&mut self, clause: &[i32]) {}

    /// Assumptions and constraints are reset.
    fn reset_assumptions(&mut self) {}

    /// An assumption clause (the negation of a failing-assumption core).
    fn add_assumption_clause(&mut self, id: i64, clause: &[i32], chain: &[i64]) {}

    // ======== conclusions ========

    /// UNSAT conclusion (`conclusion`, relevant clause ids).
    fn conclude_unsat(&mut self, conclusion: ConclusionType, ids: &[i64]) {}

    /// SAT conclusion (the full model).
    fn conclude_sat(&mut self, model: &[i32]) {}

    /// UNKNOWN conclusion (the current trail).
    fn conclude_unknown(&mut self, trail: &[i32]) {}

    /// Two literals were found equivalent (`a ≡ b`).
    fn notify_equivalence(&mut self, a: i32, b: i32) {}
}
