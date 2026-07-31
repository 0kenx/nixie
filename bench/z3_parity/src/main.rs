//! OxiZ vs Z3 differential-testing (parity) harness.
//!
//! Discovers SMT-LIB2 benchmarks under `benchmarks/<logic>/*.smt2` (relative
//! to this crate's manifest directory), runs each one through both the OxiZ
//! solver and a real `z3` binary, and compares the results to measure
//! correctness parity per logic. A summary table is printed to stdout and
//! full results are written into this crate's directory, twice:
//!
//! - `results.json` - scratch copy of the most recent run, git-ignored.
//! - `results.<os>-<arch>.json` - the tracked per-environment record, e.g.
//!   `results.linux-x86_64.json`. One file per platform, so a run on one
//!   machine can never clobber another platform's recorded verdicts.
//!
//! Both files carry identical content: a `schema_version`, a `metadata` header
//! naming the OxiZ version, the Z3 version actually probed, the OS/arch and
//! the run timestamp, and the `results` list itself.
//!
//! # Usage
//!
//! ```text
//! oxiz-z3-parity [--export-history <DIR>] [--out <FILE>]
//! ```
//!
//! `--export-history <DIR>` additionally exports a history snapshot of the run
//! to the given directory. `--out <FILE>` redirects the per-environment record
//! to `<FILE>`; the scratch `results.json` is written either way.

use anyhow::{Context, Result};
use colored::Colorize;
use rayon::prelude::*;
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;
use tabled::{Table, Tabled};

use oxiz_z3_parity::comparator::{MatchStatus, compare_results};
use oxiz_z3_parity::history;
use oxiz_z3_parity::oxiz_runner::run_oxiz;
use oxiz_z3_parity::z3_runner::run_z3;
use oxiz_z3_parity::{
    ParityReport, ParityResult, SCRATCH_RESULTS_FILE_NAME, env_results_file_name,
};

#[derive(Debug, Tabled)]
struct ResultRow {
    #[tabled(rename = "Logic")]
    logic: String,
    #[tabled(rename = "Total")]
    total: usize,
    #[tabled(rename = "Correct")]
    correct: usize,
    #[tabled(rename = "Wrong")]
    wrong: usize,
    #[tabled(rename = "Inconclusive")]
    inconclusive: usize,
    #[tabled(rename = "Timeout")]
    timeout: usize,
    #[tabled(rename = "Error")]
    error: usize,
    #[tabled(rename = "Parity %")]
    parity: String,
    #[tabled(rename = "Solved %")]
    solved: String,
}

/// Command-line options, parsed by hand: two optional flags do not justify a
/// CLI dependency in a benchmark harness.
#[derive(Debug, Default)]
struct CliArgs {
    /// `--export-history <DIR>`: directory to append a history snapshot to.
    export_history_dir: Option<PathBuf>,
    /// `--out <FILE>`: override for the per-environment record's path. The
    /// scratch `results.json` is unaffected.
    out_path: Option<PathBuf>,
}

/// Parse the flags this harness understands, leaving anything else alone (the
/// runner has always tolerated unknown arguments). A known flag missing its
/// value is an error rather than a silent no-op, so a typo cannot quietly cost
/// a full benchmark run its output path.
fn parse_args(args: &[String]) -> Result<CliArgs> {
    let mut parsed = CliArgs::default();
    let mut index = 1;

    while index < args.len() {
        match args[index].as_str() {
            "--export-history" => {
                let value = args
                    .get(index + 1)
                    .context("--export-history requires a directory argument")?;
                parsed.export_history_dir = Some(PathBuf::from(value));
                index += 2;
            }
            "--out" => {
                let value = args
                    .get(index + 1)
                    .context("--out requires a file path argument")?;
                parsed.out_path = Some(PathBuf::from(value));
                index += 2;
            }
            _ => index += 1,
        }
    }

    Ok(parsed)
}

fn discover_benchmarks(base_path: &Path) -> Result<Vec<(String, PathBuf)>> {
    let mut benchmarks = Vec::new();

    for logic_dir in fs::read_dir(base_path)? {
        let logic_dir = logic_dir?;
        if !logic_dir.path().is_dir() {
            continue;
        }

        let logic_name = logic_dir.file_name().to_string_lossy().to_string();

        for entry in fs::read_dir(logic_dir.path())? {
            let entry = entry?;
            let path = entry.path();

            if path.extension().and_then(|s| s.to_str()) == Some("smt2") {
                benchmarks.push((logic_name.clone(), path));
            }
        }
    }

    benchmarks.sort_by(|a, b| a.1.cmp(&b.1));
    Ok(benchmarks)
}

fn run_benchmark(logic: &str, path: &Path) -> Result<ParityResult> {
    println!("  Running: {}", path.display());

    // Run OxiZ
    let oxiz_start = Instant::now();
    let oxiz_result = run_oxiz(path)?;
    let oxiz_time = oxiz_start.elapsed();

    // Run Z3
    let z3_start = Instant::now();
    let z3_result = run_z3(path)?;
    let z3_time = z3_start.elapsed();

    // Compare results
    let match_status = compare_results(&oxiz_result, &z3_result);

    Ok(ParityResult {
        benchmark: path
            .file_name()
            .map(|n| n.to_string_lossy().to_string())
            .unwrap_or_else(|| String::from("<unknown>")),
        logic: logic.to_string(),
        oxiz_result,
        z3_result,
        oxiz_time,
        z3_time,
        match_status,
    })
}

fn generate_report(results: &[ParityResult]) {
    println!("\n{}", "=".repeat(80).bright_cyan());
    println!("{}", "Z3 PARITY TEST REPORT".bright_cyan().bold());
    println!("{}", "=".repeat(80).bright_cyan());

    // Group by logic
    let mut by_logic: HashMap<String, Vec<&ParityResult>> = HashMap::new();
    for result in results {
        by_logic
            .entry(result.logic.clone())
            .or_default()
            .push(result);
    }

    // Parity % is computed ONLY over "decisive" comparisons (both solvers
    // gave a definite Sat/Unsat answer, i.e. Correct or Wrong). Unknown
    // answers are reported separately as "Inconclusive" and never inflate
    // the parity number - a solver that always answers unknown scores
    // "N/A" parity, not 100%.
    let mut rows = Vec::new();
    let mut total_correct = 0;
    let mut total_wrong = 0;
    let mut total_inconclusive = 0;
    let mut total_timeout = 0;
    let mut total_error = 0;
    let mut total_tests = 0;

    for (logic, logic_results) in by_logic.iter() {
        let total = logic_results.len();
        let correct = logic_results
            .iter()
            .filter(|r| matches!(r.match_status, MatchStatus::Correct))
            .count();
        let wrong = logic_results
            .iter()
            .filter(|r| matches!(r.match_status, MatchStatus::Wrong))
            .count();
        let inconclusive = logic_results
            .iter()
            .filter(|r| matches!(r.match_status, MatchStatus::Inconclusive))
            .count();
        let timeout = logic_results
            .iter()
            .filter(|r| matches!(r.match_status, MatchStatus::Timeout))
            .count();
        let error = logic_results
            .iter()
            .filter(|r| matches!(r.match_status, MatchStatus::Error))
            .count();

        let decisive = correct + wrong;
        let parity = if decisive > 0 {
            format!("{:.1}%", (correct as f64 / decisive as f64) * 100.0)
        } else {
            "N/A".to_string()
        };
        let solved = if total > 0 {
            format!("{:.1}%", (decisive as f64 / total as f64) * 100.0)
        } else {
            "N/A".to_string()
        };

        total_correct += correct;
        total_wrong += wrong;
        total_inconclusive += inconclusive;
        total_timeout += timeout;
        total_error += error;
        total_tests += total;

        rows.push(ResultRow {
            logic: logic.clone(),
            total,
            correct,
            wrong,
            inconclusive,
            timeout,
            error,
            parity,
            solved,
        });
    }

    // Add total row
    let total_decisive = total_correct + total_wrong;
    let overall_parity = if total_decisive > 0 {
        format!(
            "{:.1}%",
            (total_correct as f64 / total_decisive as f64) * 100.0
        )
    } else {
        "N/A".to_string()
    };
    let overall_solved = if total_tests > 0 {
        format!(
            "{:.1}%",
            (total_decisive as f64 / total_tests as f64) * 100.0
        )
    } else {
        "N/A".to_string()
    };

    rows.push(ResultRow {
        logic: "TOTAL".to_string().bold().to_string(),
        total: total_tests,
        correct: total_correct,
        wrong: total_wrong,
        inconclusive: total_inconclusive,
        timeout: total_timeout,
        error: total_error,
        parity: overall_parity,
        solved: overall_solved,
    });

    println!("\n{}", Table::new(rows));
    println!(
        "\n{}",
        "Parity % = agreement rate over DECISIVE (Sat/Unsat) comparisons only.".dimmed()
    );
    println!(
        "{}",
        "Solved % = share of benchmarks where both solvers gave a decisive answer \
         (Unknown/Timeout/Error excluded)."
            .dimmed()
    );

    // Real soundness failures: both solvers gave a decisive answer and they
    // disagreed. These are the only results that indicate an actual bug.
    let wrong: Vec<_> = results
        .iter()
        .filter(|r| matches!(r.match_status, MatchStatus::Wrong))
        .collect();

    if !wrong.is_empty() {
        println!(
            "\n{}",
            "SOUNDNESS FAILURES (Sat vs Unsat disagreement):"
                .bright_red()
                .bold()
        );
        for failure in &wrong {
            println!(
                "\n  {} [{}]",
                failure.benchmark.bright_yellow(),
                failure.logic
            );
            println!(
                "    OxiZ:  {:?} ({:.3}s)",
                failure.oxiz_result,
                failure.oxiz_time.as_secs_f64()
            );
            println!(
                "    Z3:    {:?} ({:.3}s)",
                failure.z3_result,
                failure.z3_time.as_secs_f64()
            );
            println!("    Status: {:?}", failure.match_status);
        }
    }

    // Everything else that isn't a confirmed decisive match (Inconclusive,
    // Timeout, Error) is reported separately from soundness failures: it is
    // not evidence of a wrong answer, only of an unresolved comparison.
    let unresolved: Vec<_> = results
        .iter()
        .filter(|r| {
            matches!(
                r.match_status,
                MatchStatus::Inconclusive | MatchStatus::Timeout | MatchStatus::Error
            )
        })
        .collect();

    if !unresolved.is_empty() {
        println!(
            "\n{}",
            "UNRESOLVED (no parity evidence - Unknown/Timeout/Error):"
                .bright_yellow()
                .bold()
        );
        for entry in unresolved {
            println!("\n  {} [{}]", entry.benchmark.bright_yellow(), entry.logic);
            println!(
                "    OxiZ:  {:?} ({:.3}s)",
                entry.oxiz_result,
                entry.oxiz_time.as_secs_f64()
            );
            println!(
                "    Z3:    {:?} ({:.3}s)",
                entry.z3_result,
                entry.z3_time.as_secs_f64()
            );
            println!("    Status: {:?}", entry.match_status);
        }
    }

    println!("\n{}", "=".repeat(80).bright_cyan());
}

fn main() -> Result<()> {
    println!("{}", "OxiZ vs Z3 Parity Testing Suite".bright_cyan().bold());
    println!("{}\n", "=".repeat(80).bright_cyan());

    let args: Vec<String> = std::env::args().collect();
    let cli_args = parse_args(&args)?;

    let crate_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let benchmark_dir = crate_dir.join("benchmarks");

    if !benchmark_dir.exists() {
        anyhow::bail!("Benchmark directory not found: {}", benchmark_dir.display());
    }

    let benchmarks =
        discover_benchmarks(&benchmark_dir).context("Failed to discover benchmarks")?;

    println!("Found {} benchmarks\n", benchmarks.len());

    // Run benchmarks in parallel
    let results: Vec<ParityResult> = benchmarks
        .par_iter()
        .filter_map(|(logic, path)| match run_benchmark(logic, path) {
            Ok(result) => Some(result),
            Err(e) => {
                eprintln!("Error running {}: {}", path.display(), e);
                None
            }
        })
        .collect();

    // Wrap the run in its metadata header before anything is written: which
    // Z3 build answered, on which platform, when. Results without that header
    // cannot be attributed, and an unattributed file silently becomes
    // "whatever machine ran last".
    let report = ParityReport::capture(results);
    let report_json = serde_json::to_string_pretty(&report)?;

    // Both files land next to this crate's manifest rather than in the current
    // directory, so the tracked record always appears where it belongs no
    // matter where the harness was invoked from.
    let scratch_path = crate_dir.join(SCRATCH_RESULTS_FILE_NAME);
    let env_path = cli_args
        .out_path
        .unwrap_or_else(|| crate_dir.join(env_results_file_name()));

    fs::write(&scratch_path, &report_json)
        .with_context(|| format!("Failed to write {}", scratch_path.display()))?;
    fs::write(&env_path, &report_json)
        .with_context(|| format!("Failed to write {}", env_path.display()))?;

    println!(
        "\nResults saved to {} (scratch, git-ignored)",
        scratch_path.display()
    );
    println!("Per-environment record: {}", env_path.display());
    println!(
        "  OxiZ {} | Z3 {} | {}-{} | {}",
        report.metadata.oxiz_version,
        report
            .metadata
            .z3_version
            .as_deref()
            .unwrap_or("<not probed>"),
        report.metadata.os,
        report.metadata.arch,
        report.metadata.generated_at
    );

    // Generate report
    generate_report(&report.results);

    // Export history snapshot if requested
    if let Some(history_dir) = cli_args.export_history_dir {
        match history::export_to_history(&report.results, &history_dir) {
            Ok(path) => println!("History snapshot written: {}", path.display()),
            Err(e) => eprintln!("Warning: failed to write history snapshot: {e}"),
        }
    }

    Ok(())
}
