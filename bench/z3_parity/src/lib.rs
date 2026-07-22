//! OxiZ vs Z3 parity-testing library.
//!
//! Hosts the shared types behind two independent consumers:
//!
//! - The curated benchmark-suite runner driven by `src/main.rs` (fixed
//!   `.smt2` corpora under `benchmarks/`, see `METHODOLOGY.md`).
//! - The deterministic differential-testing harness (`generator` +
//!   `difftest`), which generates random well-typed SMT-LIB2 scripts per
//!   logic and checks OxiZ's sat/unsat verdicts against a Z3 binary found
//!   on `PATH`. See `METHODOLOGY.md`'s "Differential Testing" section for
//!   usage.

pub mod comparator;
pub mod difftest;
pub mod generator;
pub mod history;
pub mod oxiz_runner;
pub mod z3_runner;

use comparator::MatchStatus;
use serde::{Deserialize, Serialize};
use std::time::Duration;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum SolverResult {
    Sat,
    Unsat,
    Unknown,
    Error(String),
    Timeout,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ParityResult {
    pub benchmark: String,
    pub logic: String,
    pub oxiz_result: SolverResult,
    pub z3_result: SolverResult,
    pub oxiz_time: Duration,
    pub z3_time: Duration,
    pub match_status: MatchStatus,
}
