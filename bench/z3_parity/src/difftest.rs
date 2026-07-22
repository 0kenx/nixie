//! Differential-testing harness: generate random well-typed SMT-LIB2
//! scripts (via [`crate::generator`]), run them through both OxiZ and Z3
//! (via [`crate::oxiz_runner`] / [`crate::z3_runner`]), and compare
//! verdicts using the same [`crate::comparator`] logic the curated
//! benchmark suite in `main.rs` already relies on.
//!
//! This module is independent of `main.rs`'s benchmark-suite runner so it
//! can be driven both by ad-hoc `cargo test` runs and by the smoke/full
//! test entry points under `tests/`. See `METHODOLOGY.md`'s "Differential
//! Testing" section for how to invoke it.

use crate::SolverResult;
use crate::comparator::{MatchStatus, compare_results};
use crate::generator::{self, Logic};
use crate::oxiz_runner::run_oxiz;
use crate::z3_runner::run_z3;
use anyhow::{Context, Result};
use std::fs;
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

/// Outcome of running one generated case through both solvers.
#[derive(Debug, Clone)]
pub struct DiffCaseOutcome {
    pub logic: Logic,
    pub seed: u64,
    pub script: String,
    pub oxiz_result: SolverResult,
    pub z3_result: SolverResult,
    pub match_status: MatchStatus,
}

/// Persist a reproducing script under `std::env::temp_dir()` and return its
/// path. Callers use this to attach a concrete repro to a test failure
/// message; the file is intentionally left on disk (not cleaned up) so a
/// developer can re-run it directly against either solver.
pub fn save_repro(logic: Logic, seed: u64, script: &str) -> Result<PathBuf> {
    let dir = std::env::temp_dir().join("oxiz_difftest_repro");
    fs::create_dir_all(&dir)
        .with_context(|| format!("creating repro directory {}", dir.display()))?;
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let path = dir.join(format!(
        "{}_{seed}_{nanos}.smt2",
        logic.name().to_lowercase()
    ));
    fs::write(&path, script).with_context(|| format!("writing repro file {}", path.display()))?;
    Ok(path)
}

/// Generate the case for `(logic, seed)`, run it through both solvers, and
/// compare their verdicts.
pub fn run_case(logic: Logic, seed: u64) -> Result<DiffCaseOutcome> {
    let script = generator::generate_script(logic, seed);
    run_case_with_script(logic, seed, script)
}

fn run_case_with_script(logic: Logic, seed: u64, script: String) -> Result<DiffCaseOutcome> {
    let scratch_dir = std::env::temp_dir().join("oxiz_difftest_input");
    fs::create_dir_all(&scratch_dir)
        .with_context(|| format!("creating scratch directory {}", scratch_dir.display()))?;
    let file_path = scratch_dir.join(format!("{}_{seed}.smt2", logic.name().to_lowercase()));
    fs::write(&file_path, &script)
        .with_context(|| format!("writing scratch input {}", file_path.display()))?;

    let oxiz_result = run_oxiz(&file_path).context("running OxiZ on generated case")?;
    let z3_result = run_z3(&file_path).context("running Z3 on generated case")?;

    // Best-effort cleanup of the scratch input file; a failure to remove it
    // must never fail the differential test itself.
    let _ = fs::remove_file(&file_path);

    let match_status = compare_results(&oxiz_result, &z3_result);

    Ok(DiffCaseOutcome {
        logic,
        seed,
        script,
        oxiz_result,
        z3_result,
        match_status,
    })
}

/// Run `count` generated cases for `logic`. Each case's seed is derived
/// from `base_seed` and its index with a fixed odd multiplier, so the
/// whole batch is reproducible from a single `(base_seed, count)` pair
/// while avoiding the trivially-correlated seeds `base_seed, base_seed+1,
/// base_seed+2, ...` would produce.
pub fn run_cases(logic: Logic, base_seed: u64, count: u64) -> Result<Vec<DiffCaseOutcome>> {
    (0..count)
        .map(|i| {
            let seed = base_seed ^ i.wrapping_mul(0x9E37_79B9_7F4A_7C15);
            run_case(logic, seed)
        })
        .collect()
}

/// Partition of a batch of [`DiffCaseOutcome`]s. `mismatches` is what a
/// differential test should fail on; everything else is informational.
#[derive(Debug, Default)]
pub struct DiffSummary {
    pub mismatches: Vec<DiffCaseOutcome>,
    /// `Unknown` on either side, timeout, or a solver error: no parity
    /// evidence either way, not a bug signal on its own.
    pub skipped: usize,
    pub agreed: usize,
}

/// Bucket outcomes into agreed / skipped (non-decisive) / mismatched.
pub fn summarize(outcomes: Vec<DiffCaseOutcome>) -> DiffSummary {
    let mut summary = DiffSummary::default();
    for outcome in outcomes {
        match &outcome.match_status {
            MatchStatus::Wrong => summary.mismatches.push(outcome),
            MatchStatus::Correct => summary.agreed += 1,
            MatchStatus::Inconclusive | MatchStatus::Timeout | MatchStatus::Error => {
                summary.skipped += 1;
            }
        }
    }
    summary
}

/// Render a human-readable failure message for a non-empty set of
/// mismatches, saving a reproducing `.smt2` script for each one under
/// `std::env::temp_dir()`. Intended to be handed straight to `panic!`.
pub fn format_mismatch_report(mismatches: &[DiffCaseOutcome]) -> String {
    let mut msg = format!("{} OxiZ/Z3 verdict mismatch(es) found:\n", mismatches.len());
    for m in mismatches {
        let repro = save_repro(m.logic, m.seed, &m.script)
            .map(|p| p.display().to_string())
            .unwrap_or_else(|e| format!("<failed to save repro: {e}>"));
        msg.push_str(&format!(
            "  [{}] seed={} oxiz={:?} z3={:?} repro={}\n",
            m.logic, m.seed, m.oxiz_result, m.z3_result, repro
        ));
    }
    msg
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn summarize_buckets_correctly() {
        let make = |status: MatchStatus| DiffCaseOutcome {
            logic: Logic::QfLia,
            seed: 0,
            script: String::new(),
            oxiz_result: SolverResult::Sat,
            z3_result: SolverResult::Sat,
            match_status: status,
        };
        let outcomes = vec![
            make(MatchStatus::Correct),
            make(MatchStatus::Correct),
            make(MatchStatus::Wrong),
            make(MatchStatus::Inconclusive),
            make(MatchStatus::Timeout),
            make(MatchStatus::Error),
        ];
        let summary = summarize(outcomes);
        assert_eq!(summary.agreed, 2);
        assert_eq!(summary.mismatches.len(), 1);
        assert_eq!(summary.skipped, 3);
    }

    #[test]
    fn run_cases_is_deterministic_in_case_count() {
        // Without Z3 installed, run_case still generates+writes+attempts to
        // run both solvers; run_oxiz always works (pure library call), so
        // this exercises the OxiZ side and the seed-derivation logic even
        // in a Z3-less environment.
        let a = run_cases(Logic::QfLia, 42, 5).expect("run_cases should not error");
        let b = run_cases(Logic::QfLia, 42, 5).expect("run_cases should not error");
        assert_eq!(a.len(), 5);
        assert_eq!(b.len(), 5);
        for (x, y) in a.iter().zip(b.iter()) {
            assert_eq!(x.seed, y.seed);
            assert_eq!(x.script, y.script);
            assert_eq!(x.oxiz_result, y.oxiz_result);
        }
    }

    #[test]
    fn save_repro_writes_a_readable_file() {
        let script = "(set-logic QF_LIA)\n(check-sat)\n";
        let path = save_repro(Logic::QfLia, 999, script).expect("save_repro should succeed");
        let contents = fs::read_to_string(&path).expect("repro file should be readable");
        assert_eq!(contents, script);
        let _ = fs::remove_file(&path);
    }
}
