//! Proof manager — faithful port of `proof.hpp` / `proof.cpp` / `proof.rs`.
//!
//! [`Proof`] is the central dispatcher: the solver reports every proof event
//! (original/derived/deleted clause, status, conclusion, in-place clause
//! rewriting via flush/strengthen, …) to it, and it fans the event out to
//! every attached [`Tracer`] (DRAT/LRAT file tracers). This is the single
//! choke-point design from upstream.
//!
//! In oxiz-sat internal literals are external (DIMACS) literals — there is no
//! `External` variable-mapping layer — so clauses pass through verbatim.
//!
//! # Clause-ID ownership
//!
//! The monotonic clause-id counter lives in the *solver* (it is shared with
//! the LRAT chain builders and the unit-clause id table). The in-place clause
//! rewriting helpers ([`Proof::flush_clause`], [`Proof::strengthen_clause`],
//! [`Proof::otfs_strengthen_clause`]) therefore take the freshly-allocated id
//! as an explicit argument rather than bumping an internal counter — the only
//! departure from upstream's `++internal->clause_id` inside `Proof`.

// The tracer API mirrors cadical's full `Tracer`/`Proof` surface verbatim; many
// methods/events are part of the public contract even before the solver emits
// them, so dead code here is expected.
#![allow(dead_code)]

pub mod drat;
pub mod lrat;
pub mod tracer;

// Legacy generic-over-`W` text writers (kept for API back-compat; the solver
// uses the tracers above).
mod legacy;

pub use drat::DratTracer;
pub use legacy::{DratWriter, LratWriter, ProofTrimmer};
pub use lrat::LratTracer;
pub use tracer::{ConclusionType, Tracer};

/// The proof manager (`class Proof`).
///
/// Holds the list of attached [`Tracer`]s plus per-call scratch buffers
/// (`clause`, `proof_chain`, `clause_id`, `redundant`, `witness`) that mirror
/// upstream's private state. Each public method stages a single event into the
/// scratch and fans it out.
pub struct Proof {
    tracers: Vec<Box<dyn Tracer + Send + Sync>>,
    // Scratch buffers mirroring upstream's `clause` / `proof_chain`.
    clause: Vec<i32>,
    proof_chain: Vec<i64>,
    clause_id: i64,
    redundant: bool,
    witness: i32,
}

impl Proof {
    /// `Proof::Proof`.
    pub fn new() -> Self {
        Self {
            tracers: Vec::new(),
            clause: Vec::new(),
            proof_chain: Vec::new(),
            clause_id: 0,
            redundant: false,
            witness: 0,
        }
    }

    /// Number of attached tracers.
    #[must_use]
    pub fn empty(&self) -> bool {
        self.tracers.is_empty()
    }

    /// `Proof::connect` — attach a tracer.
    pub fn connect(&mut self, tracer: Box<dyn Tracer + Send + Sync>) {
        self.tracers.push(tracer);
    }

    /// `Proof::disconnect` — remove all tracers. Upstream removes a specific
    /// `Tracer*`; pointer identity is not expressible for trait objects here,
    /// so we clear the lot (tracers are dropped with the solver).
    pub fn disconnect_all(&mut self) {
        self.tracers.clear();
    }

    // -- original clauses ---------------------------------------------

    /// `add_original_clause(id, redundant, clause)`.
    pub fn add_original_clause(&mut self, id: i64, redundant: bool, c: &[i32]) {
        self.clause.clear();
        self.clause.extend_from_slice(c);
        self.clause_id = id;
        self.redundant = redundant;
        self.fan_add_original_clause(false);
    }

    /// `add_external_original_clause(id, redundant, clause, restore)`.
    pub fn add_external_original_clause(
        &mut self,
        id: i64,
        redundant: bool,
        c: &[i32],
        restore: bool,
    ) {
        self.clause.clear();
        self.clause.extend_from_slice(c);
        self.clause_id = id;
        self.redundant = redundant;
        self.fan_add_original_clause(restore);
    }

    /// `delete_external_original_clause(id, redundant, clause)`.
    pub fn delete_external_original_clause(&mut self, id: i64, redundant: bool, c: &[i32]) {
        self.clause.clear();
        self.clause.extend_from_slice(c);
        self.clause_id = id;
        self.redundant = redundant;
        self.fan_delete_clause();
    }

    // -- derived clauses ----------------------------------------------

    /// `add_derived_empty_clause(id, chain)`.
    pub fn add_derived_empty_clause(&mut self, id: i64, chain: &[i64]) {
        self.clause.clear();
        self.proof_chain.clear();
        self.proof_chain.extend_from_slice(chain);
        self.clause_id = id;
        self.redundant = false;
        self.fan_add_derived_clause();
    }

    /// `add_derived_unit_clause(id, unit, chain)`.
    pub fn add_derived_unit_clause(&mut self, id: i64, unit: i32, chain: &[i64]) {
        self.clause.clear();
        self.clause.push(unit);
        self.proof_chain.clear();
        self.proof_chain.extend_from_slice(chain);
        self.clause_id = id;
        self.redundant = false;
        self.fan_add_derived_clause();
    }

    /// `add_derived_clause(id, redundant, clause, chain)`.
    pub fn add_derived_clause(&mut self, id: i64, redundant: bool, c: &[i32], chain: &[i64]) {
        self.clause.clear();
        self.clause.extend_from_slice(c);
        self.proof_chain.clear();
        self.proof_chain.extend_from_slice(chain);
        self.clause_id = id;
        self.redundant = redundant;
        self.fan_add_derived_clause();
    }

    /// `add_derived_rat_clause(id, redundant, witness, clause, chain)`.
    pub fn add_derived_rat_clause(
        &mut self,
        id: i64,
        redundant: bool,
        witness: i32,
        c: &[i32],
        chain: &[i64],
    ) {
        self.clause.clear();
        self.clause.extend_from_slice(c);
        self.proof_chain.clear();
        self.proof_chain.extend_from_slice(chain);
        self.clause_id = id;
        self.redundant = redundant;
        self.witness = witness;
        self.fan_add_derived_clause();
    }

    // -- deletion / weakening -----------------------------------------

    /// `delete_clause(id, redundant, clause)`.
    pub fn delete_clause(&mut self, id: i64, redundant: bool, c: &[i32]) {
        self.clause.clear();
        self.clause.extend_from_slice(c);
        self.clause_id = id;
        self.redundant = redundant;
        self.fan_delete_clause();
    }

    /// `delete_unit_clause(id, lit)`.
    pub fn delete_unit_clause(&mut self, id: i64, lit: i32) {
        self.clause.clear();
        self.clause.push(lit);
        self.clause_id = id;
        self.redundant = false;
        self.fan_delete_clause();
    }

    /// `weaken_minus(id, clause)`.
    pub fn weaken_minus(&mut self, id: i64, c: &[i32]) {
        self.clause.clear();
        self.clause.extend_from_slice(c);
        self.clause_id = id;
        for t in self.tracers.iter_mut() {
            t.weaken_minus(self.clause_id, &self.clause);
        }
        self.clause.clear();
        self.clause_id = 0;
    }

    /// `weaken_plus(id, clause)` = `weaken_minus` then `delete_clause`.
    pub fn weaken_plus(&mut self, id: i64, c: &[i32]) {
        self.weaken_minus(id, c);
        self.delete_clause(id, false, c);
    }

    // -- finalization -------------------------------------------------

    /// `finalize_clause(id, clause)`.
    pub fn finalize_clause(&mut self, id: i64, c: &[i32]) {
        self.clause.clear();
        self.clause.extend_from_slice(c);
        self.clause_id = id;
        for t in self.tracers.iter_mut() {
            t.finalize_clause(self.clause_id, &self.clause);
        }
        self.clause.clear();
        self.clause_id = 0;
    }

    /// `finalize_unit(id, lit)`.
    pub fn finalize_unit(&mut self, id: i64, lit: i32) {
        self.clause.clear();
        self.clause.push(lit);
        self.clause_id = id;
        for t in self.tracers.iter_mut() {
            t.finalize_clause(self.clause_id, &self.clause);
        }
        self.clause.clear();
        self.clause_id = 0;
    }

    // -- in-place clause rewriting (flush / strengthen) ---------------

    /// `flush_clause` — drop falsified literals from a clause for the proof.
    /// `new_id` is the freshly-allocated id for the rewritten clause (caller
    /// owns the monotonic counter); `kept` are the non-falsified literals;
    /// `chain` the LRAT hints.
    pub fn flush_clause(&mut self, new_id: i64, redundant: bool, kept: &[i32], chain: &[i64]) {
        self.clause.clear();
        self.clause.extend_from_slice(kept);
        self.proof_chain.clear();
        self.proof_chain.extend_from_slice(chain);
        self.clause_id = new_id;
        self.redundant = redundant;
        self.fan_add_derived_clause();
    }

    /// `strengthen_clause` — record a clause with one literal removed.
    /// `new_id` is the freshly-allocated id; `kept` the remaining literals;
    /// `chain` the LRAT hints.
    pub fn strengthen_clause(&mut self, new_id: i64, redundant: bool, kept: &[i32], chain: &[i64]) {
        self.clause.clear();
        self.clause.extend_from_slice(kept);
        self.proof_chain.clear();
        self.proof_chain.extend_from_slice(chain);
        self.clause_id = new_id;
        self.redundant = redundant;
        self.fan_add_derived_clause();
    }

    /// `otfs_strengthen_clause` — on-the-fly strengthening.
    pub fn otfs_strengthen_clause(
        &mut self,
        new_id: i64,
        redundant: bool,
        kept: &[i32],
        chain: &[i64],
    ) {
        self.clause.clear();
        self.clause.extend_from_slice(kept);
        self.proof_chain.clear();
        self.proof_chain.extend_from_slice(chain);
        self.clause_id = new_id;
        self.redundant = redundant;
        self.fan_add_derived_clause();
    }

    /// `strengthen(id)`.
    pub fn strengthen(&mut self, id: i64) {
        self.clause_id = id;
        for t in self.tracers.iter_mut() {
            t.strengthen(self.clause_id);
        }
        self.clause_id = 0;
    }

    // -- incremental / status / conclusions ---------------------------

    /// `add_assumption(lit)`.
    pub fn add_assumption(&mut self, lit: i32) {
        for t in self.tracers.iter_mut() {
            t.add_assumption(lit);
        }
    }

    /// `add_constraint(clause)`.
    pub fn add_constraint(&mut self, c: &[i32]) {
        for t in self.tracers.iter_mut() {
            t.add_constraint(c);
        }
    }

    /// `reset_assumptions()`.
    pub fn reset_assumptions(&mut self) {
        for t in self.tracers.iter_mut() {
            t.reset_assumptions();
        }
    }

    /// `add_assumption_clause(id, clause, chain)`.
    pub fn add_assumption_clause(&mut self, id: i64, c: &[i32], chain: &[i64]) {
        self.clause.clear();
        self.clause.extend_from_slice(c);
        self.proof_chain.clear();
        self.proof_chain.extend_from_slice(chain);
        self.clause_id = id;
        for t in self.tracers.iter_mut() {
            t.add_assumption_clause(self.clause_id, &self.clause, &self.proof_chain);
        }
        self.proof_chain.clear();
        self.clause.clear();
        self.clause_id = 0;
    }

    /// `report_status(status, id)`.
    pub fn report_status(&mut self, status: i32, id: i64) {
        for t in self.tracers.iter_mut() {
            t.report_status(status, id);
        }
    }

    /// `begin_proof(id)`.
    pub fn begin_proof(&mut self, id: i64) {
        for t in self.tracers.iter_mut() {
            t.begin_proof(id);
        }
    }

    /// `solve_query()`.
    pub fn solve_query(&mut self) {
        for t in self.tracers.iter_mut() {
            t.solve_query();
        }
    }

    /// `conclude_unsat(conclusion, ids)`.
    pub fn conclude_unsat(&mut self, conclusion: ConclusionType, ids: &[i64]) {
        for t in self.tracers.iter_mut() {
            t.conclude_unsat(conclusion, ids);
        }
    }

    /// `conclude_sat(model)`.
    pub fn conclude_sat(&mut self, model: &[i32]) {
        for t in self.tracers.iter_mut() {
            t.conclude_sat(model);
        }
    }

    /// `conclude_unknown(trail)`.
    pub fn conclude_unknown(&mut self, trail: &[i32]) {
        for t in self.tracers.iter_mut() {
            t.conclude_unknown(trail);
        }
    }

    /// `notify_equivalence(a, b)`.
    pub fn notify_equivalence(&mut self, a: i32, b: i32) {
        for t in self.tracers.iter_mut() {
            t.notify_equivalence(a, b);
        }
    }

    /// `flush` — flush every attached file tracer.
    pub fn flush(&mut self, print: bool) {
        for t in self.tracers.iter_mut() {
            t.flush(print);
        }
    }

    /// `close` — close every attached file tracer.
    pub fn close(&mut self, print: bool) {
        for t in self.tracers.iter_mut() {
            t.close(print);
        }
    }

    // -- private fan-outs (mirror upstream's private dispatchers) -----

    fn fan_add_original_clause(&mut self, restore: bool) {
        let (id, redundant) = (self.clause_id, self.redundant);
        let clause = std::mem::take(&mut self.clause);
        for t in self.tracers.iter_mut() {
            t.add_original_clause(id, redundant, &clause, restore);
        }
        self.clause_id = 0;
    }

    fn fan_add_derived_clause(&mut self) {
        let (id, redundant, witness) = (self.clause_id, self.redundant, self.witness);
        let clause = std::mem::take(&mut self.clause);
        let chain = std::mem::take(&mut self.proof_chain);
        for t in self.tracers.iter_mut() {
            t.add_derived_clause(id, redundant, witness, &clause, &chain);
        }
        self.clause_id = 0;
        self.witness = 0;
    }

    fn fan_delete_clause(&mut self) {
        let (id, redundant) = (self.clause_id, self.redundant);
        let clause = std::mem::take(&mut self.clause);
        for t in self.tracers.iter_mut() {
            t.delete_clause(id, redundant, &clause);
        }
        self.clause_id = 0;
    }

    // -- helpers used by the solver to gather a clause's external form --

    /// Push a literal onto the scratch clause buffer (mirrors
    /// `Proof::add_literal`). Kept `pub(super)` for the solver.
    #[inline]
    pub(super) fn push_lit(&mut self, lit: i32) {
        self.clause.push(lit);
    }

    /// Borrow the scratch clause as a slice (e.g. to hand a literal set to a
    /// delete/derived fan-out without re-allocating a `Vec`).
    #[inline]
    pub(super) fn scratch(&self) -> &[i32] {
        &self.clause
    }
}

impl Default for Proof {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Debug for Proof {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Proof")
            .field("tracers", &self.tracers.len())
            .field("clause_id", &self.clause_id)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, Mutex};

    /// A tracer that records every event it receives into a shared buffer.
    struct RecordingTracer {
        events: Arc<Mutex<Vec<String>>>,
    }
    impl Tracer for RecordingTracer {
        fn add_original_clause(&mut self, id: i64, _r: bool, _c: &[i32], _rest: bool) {
            self.events.lock().unwrap().push(format!("orig:{id}"));
        }
        fn add_derived_clause(&mut self, id: i64, _r: bool, _w: i32, c: &[i32], _ch: &[i64]) {
            self.events
                .lock()
                .unwrap()
                .push(format!("der:{id}:{}", c.len()));
        }
        fn delete_clause(&mut self, id: i64, _r: bool, _c: &[i32]) {
            self.events.lock().unwrap().push(format!("del:{id}"));
        }
        fn report_status(&mut self, status: i32, _id: i64) {
            self.events.lock().unwrap().push(format!("status:{status}"));
        }
    }

    #[test]
    fn fans_out_to_all_tracers() {
        let buf_a = Arc::new(Mutex::new(Vec::<String>::new()));
        let buf_b = Arc::new(Mutex::new(Vec::<String>::new()));
        let mut p = Proof::new();
        p.connect(Box::new(RecordingTracer {
            events: buf_a.clone(),
        }));
        p.connect(Box::new(RecordingTracer {
            events: buf_b.clone(),
        }));
        p.add_derived_clause(5, true, &[1, -2], &[1, 2]);
        p.delete_clause(5, true, &[]);
        p.report_status(20, 5);
        drop(p);
        let mut got: Vec<String> = buf_a.lock().unwrap().clone();
        got.extend(buf_b.lock().unwrap().iter().cloned());
        assert_eq!(
            got,
            vec![
                "der:5:2",
                "del:5",
                "status:20", //
                "der:5:2",
                "del:5",
                "status:20",
            ]
        );
    }
}
