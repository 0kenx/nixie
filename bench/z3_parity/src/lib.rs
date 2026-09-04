//! Nixie vs Z3 parity-testing library.
//!
//! Hosts the shared types behind two independent consumers:
//!
//! - The curated benchmark-suite runner driven by `src/main.rs` (fixed
//!   `.smt2` corpora under `benchmarks/`, see `METHODOLOGY.md`).
//! - The deterministic differential-testing harness (`generator` +
//!   `difftest`), which generates random well-typed SMT-LIB2 scripts per
//!   logic and checks Nixie's sat/unsat verdicts against a Z3 binary found
//!   on `PATH`. See `METHODOLOGY.md`'s "Differential Testing" section for
//!   usage.
//!
//! The benchmark-suite runner serialises a [`ParityReport`] - a versioned
//! envelope pairing the raw [`ParityResult`] list with a [`RunMetadata`]
//! header describing the environment that produced it.

pub mod comparator;
pub mod difftest;
pub mod generator;
pub mod history;
pub mod nixie_runner;
pub mod z3_runner;

use chrono::{Local, SecondsFormat};
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
    pub nixie_result: SolverResult,
    pub z3_result: SolverResult,
    pub nixie_time: Duration,
    pub z3_time: Duration,
    pub match_status: MatchStatus,
}

/// Schema version of the parity report written to `results*.json`.
///
/// Bumped only when the on-disk layout changes in a way an older reader cannot
/// handle, so consumers can reject a file they do not understand instead of
/// silently misreading it.
pub const SCHEMA_VERSION: u32 = 1;

/// Scratch output written by every run on every platform.
///
/// Git-ignored on purpose: it holds whichever machine ran the suite last, so
/// it is a convenience artifact, never a record. The record is the
/// per-environment snapshot named by [`env_results_file_name`].
pub const SCRATCH_RESULTS_FILE_NAME: &str = "results.json";

/// Name of the per-environment snapshot for the machine running this build,
/// e.g. `results.linux-x86_64.json` or `results.macos-aarch64.json`.
///
/// Only OS and architecture feed the name. Host name and user name are
/// deliberately excluded: these files are committed to a public repository and
/// must not carry the developer's machine identity.
pub fn env_results_file_name() -> String {
    format!(
        "results.{}-{}.json",
        std::env::consts::OS,
        std::env::consts::ARCH
    )
}

/// Environment header recorded alongside the results of a run.
///
/// A bare list of results is unattributable: the verdicts depend on which Z3
/// build produced the `z3_result` values and on the platform Nixie ran on, and
/// neither was recorded before this header existed.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RunMetadata {
    /// `CARGO_PKG_VERSION` of this harness, which mirrors the workspace version.
    pub nixie_version: String,
    /// Bare version of the Z3 binary that produced the `z3_result` values
    /// (e.g. `4.15.4`), captured at run time. `None` when no Z3 binary could be
    /// probed - never a guessed or documented value.
    pub z3_version: Option<String>,
    /// `std::env::consts::OS` of the machine that ran the suite.
    pub os: String,
    /// `std::env::consts::ARCH` of the machine that ran the suite.
    pub arch: String,
    /// Local time with UTC offset, RFC 3339 (e.g. `2026-07-31T13:40:00+07:00`).
    pub generated_at: String,
    /// Number of entries in the accompanying results list.
    pub benchmark_count: usize,
    /// Set only on files that were not produced by a live run (e.g. records
    /// migrated from the pre-metadata schema), spelling out which fields are
    /// reconstructed rather than measured. Absent on generated files.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub provenance: Option<String>,
}

impl RunMetadata {
    /// Capture the current environment for a run that produced
    /// `benchmark_count` results.
    pub fn capture(benchmark_count: usize) -> Self {
        Self {
            nixie_version: env!("CARGO_PKG_VERSION").to_string(),
            z3_version: z3_runner::z3_version(),
            os: std::env::consts::OS.to_string(),
            arch: std::env::consts::ARCH.to_string(),
            generated_at: Local::now().to_rfc3339_opts(SecondsFormat::Secs, false),
            benchmark_count,
            provenance: None,
        }
    }
}

/// A complete parity run: the versioned envelope actually written to disk.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ParityReport {
    pub schema_version: u32,
    pub metadata: RunMetadata,
    pub results: Vec<ParityResult>,
}

impl ParityReport {
    /// Wrap a finished run's results, capturing the environment as it is now.
    ///
    /// `benchmark_count` is derived from `results`, so the header can never
    /// disagree with the payload it describes.
    pub fn capture(results: Vec<ParityResult>) -> Self {
        Self {
            schema_version: SCHEMA_VERSION,
            metadata: RunMetadata::capture(results.len()),
            results,
        }
    }
}
