//! SMT-LIB benchmark suite tests
//!
//! This module provides infrastructure for testing oxiz against SMT-LIB benchmarks.
//! To run these tests, set the SMTLIB_BENCH_PATH environment variable to the path
//! containing SMT-LIB2 benchmark files.
//!
//! Example:
//!   SMTLIB_BENCH_PATH=/path/to/smtlib/benchmarks cargo test --test smtlib_benchmarks

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Get the path to the oxiz binary
fn oxiz_bin() -> PathBuf {
    let mut path = env::current_exe().expect("Failed to get current executable path");
    path.pop(); // Remove test executable name
    if path.ends_with("deps") {
        path.pop(); // Remove deps directory
    }
    path.push("oxiz");
    path
}

/// Get the SMT-LIB benchmark path from environment variable
fn get_benchmark_path() -> Option<PathBuf> {
    env::var("SMTLIB_BENCH_PATH").ok().map(PathBuf::from)
}

/// Run a single SMT-LIB2 file and return the result
fn run_smtlib_file(file: &Path) -> Result<(String, bool), String> {
    let output = Command::new(oxiz_bin())
        .arg(file)
        .arg("--quiet")
        .output()
        .map_err(|e| format!("Failed to execute oxiz: {}", e))?;

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let success = output.status.success();

    Ok((stdout, success))
}

/// Extract a SMT-LIB benchmark's declared expected status from its
/// `(set-info :status sat|unsat|unknown)` directive, if present.
///
/// Returns `None` for `unknown` (or if the directive is absent/unparsable),
/// since there is nothing concrete to check the solver's answer against in
/// that case.
fn expected_status(file: &Path) -> Option<String> {
    let content = fs::read_to_string(file).ok()?;
    for line in content.lines() {
        let trimmed = line.trim();
        if let Some(idx) = trimmed.find(":status") {
            let rest = trimmed[idx + ":status".len()..].trim_start();
            let word: String = rest
                .chars()
                .take_while(|c| !c.is_whitespace() && *c != ')')
                .collect();
            if word == "sat" || word == "unsat" {
                return Some(word);
            }
            return None;
        }
    }
    None
}

/// Extract oxiz's actual reported answer from its CLI stdout: the first line
/// that is exactly `sat`, `unsat`, or `unknown` (ignoring model output,
/// comments, and other surrounding text). Note this deliberately does *not*
/// use `str::contains`, since `"unsat".contains("sat")` is always true and
/// would make it impossible to tell the two answers apart.
fn actual_status(output: &str) -> Option<&'static str> {
    for line in output.lines() {
        match line.trim() {
            "sat" => return Some("sat"),
            "unsat" => return Some("unsat"),
            "unknown" => return Some("unknown"),
            _ => {}
        }
    }
    None
}

/// Collect all .smt2 files from a directory
fn collect_smt2_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();

    if let Ok(entries) = fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_file() && path.extension().and_then(|s| s.to_str()) == Some("smt2") {
                files.push(path);
            } else if path.is_dir() {
                files.extend(collect_smt2_files(&path));
            }
        }
    }

    files
}

#[test]
fn test_smtlib_benchmarks() {
    let bench_path = match get_benchmark_path() {
        Some(path) => path,
        None => {
            println!("Skipping SMT-LIB benchmark tests - SMTLIB_BENCH_PATH not set");
            println!("To run these tests, set SMTLIB_BENCH_PATH to your benchmark directory");
            return;
        }
    };

    if !bench_path.exists() {
        eprintln!("Benchmark path does not exist: {}", bench_path.display());
        return;
    }

    let files = collect_smt2_files(&bench_path);

    if files.is_empty() {
        println!("No .smt2 files found in {}", bench_path.display());
        return;
    }

    println!("Found {} SMT-LIB2 benchmark files", files.len());

    let mut passed = 0;
    let mut failed = 0;
    let mut errors = 0;

    for file in &files {
        match run_smtlib_file(file) {
            Ok((output, _success)) => {
                match actual_status(&output) {
                    Some(status) => {
                        // If the benchmark declares an expected sat/unsat
                        // status via `(set-info :status ...)`, the reported
                        // answer must actually match it. Previously "passed"
                        // only meant *some* sat/unsat/unknown substring
                        // appeared anywhere in the output -- since
                        // `"unsat".contains("sat")` is always true, a solver
                        // that confidently reported the wrong answer on
                        // every single benchmark still scored a 100% "pass"
                        // rate here.
                        match expected_status(file) {
                            Some(expected) if expected != status => {
                                failed += 1;
                                println!(
                                    "Wrong answer for {}: expected {}, got {}",
                                    file.display(),
                                    expected,
                                    status
                                );
                            }
                            _ => passed += 1,
                        }
                    }
                    None if output.contains("(error") => {
                        errors += 1;
                        println!("Error in {}: {}", file.display(), output);
                    }
                    None => {
                        failed += 1;
                        println!("Unexpected output from {}: {}", file.display(), output);
                    }
                }
            }
            Err(e) => {
                errors += 1;
                println!("Failed to run {}: {}", file.display(), e);
            }
        }
    }

    println!("\nBenchmark Results:");
    println!("  Total files: {}", files.len());
    println!("  Passed: {}", passed);
    println!("  Failed: {}", failed);
    println!("  Errors: {}", errors);
    println!(
        "  Success rate: {:.2}%",
        (passed as f64 / files.len() as f64) * 100.0
    );

    // Unlike before, a wrong sat/unsat answer (as opposed to an "unknown" or
    // a run-time error, both of which are honest and remain non-fatal here)
    // now actually fails this test -- that is the entire point of running
    // against benchmarks with a known expected status.
    assert_eq!(
        failed, 0,
        "{failed} benchmark(s) produced an incorrect or unparseable result; see the \
         per-file output above for details"
    );
}

#[test]
fn test_qf_lia_benchmarks() {
    let bench_path = match get_benchmark_path() {
        Some(mut path) => {
            path.push("QF_LIA");
            path
        }
        None => {
            println!("Skipping QF_LIA benchmark tests - SMTLIB_BENCH_PATH not set");
            return;
        }
    };

    if !bench_path.exists() {
        println!(
            "QF_LIA benchmark path does not exist: {}",
            bench_path.display()
        );
        return;
    }

    let files = collect_smt2_files(&bench_path);
    println!("Found {} QF_LIA benchmark files", files.len());

    for file in files.iter().take(10) {
        // Test first 10 files
        match run_smtlib_file(file) {
            Ok((output, _)) => {
                println!("{}: {}", file.display(), output.trim());
            }
            Err(e) => {
                println!("{}: Error - {}", file.display(), e);
            }
        }
    }
}

#[test]
fn test_qf_uf_benchmarks() {
    let bench_path = match get_benchmark_path() {
        Some(mut path) => {
            path.push("QF_UF");
            path
        }
        None => {
            println!("Skipping QF_UF benchmark tests - SMTLIB_BENCH_PATH not set");
            return;
        }
    };

    if !bench_path.exists() {
        println!(
            "QF_UF benchmark path does not exist: {}",
            bench_path.display()
        );
        return;
    }

    let files = collect_smt2_files(&bench_path);
    println!("Found {} QF_UF benchmark files", files.len());

    for file in files.iter().take(10) {
        // Test first 10 files
        match run_smtlib_file(file) {
            Ok((output, _)) => {
                println!("{}: {}", file.display(), output.trim());
            }
            Err(e) => {
                println!("{}: Error - {}", file.display(), e);
            }
        }
    }
}
