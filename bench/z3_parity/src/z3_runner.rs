use crate::SolverResult;
use anyhow::{Context, Result};
use std::path::Path;
use std::process::Command;

const Z3_TIMEOUT_SECS: u64 = 60;

/// Common Z3 installation locations to probe, in order.
const Z3_PATHS: [&str; 4] = [
    "/opt/homebrew/bin/z3", // macOS Homebrew
    "/usr/local/bin/z3",    // macOS/Linux manual install
    "/usr/bin/z3",          // Linux package manager
    "z3",                   // PATH
];

/// Locate a usable `z3` binary, if any is installed.
///
/// Used both by [`run_z3`] and by the differential tests below so that the
/// tests can self-skip (rather than being permanently `#[ignore]`d) when no
/// Z3 binary is available, and actually run as real differential tests
/// whenever one is.
fn find_z3() -> Option<&'static str> {
    Z3_PATHS
        .iter()
        .find(|path| Command::new(path).arg("--version").output().is_ok())
        .copied()
}

/// Public probe for callers outside this module (e.g. the differential
/// testing entry points under `tests/`) that need to self-skip when no Z3
/// binary is reachable, mirroring the `skip_if_no_z3!` behavior used by the
/// tests in this file.
pub fn is_z3_available() -> bool {
    find_z3().is_some()
}

pub fn run_z3(smt2_file: &Path) -> Result<SolverResult> {
    let z3_path = find_z3().context("Z3 not found. Please install Z3 and ensure it's in PATH")?;

    let output = Command::new(z3_path)
        .arg("-smt2")
        .arg(smt2_file)
        .arg(format!("-T:{}", Z3_TIMEOUT_SECS))
        .output()
        .context("Failed to execute Z3")?;

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // Check for errors in stdout (Z3 outputs errors to stdout with "(error ...)" prefix)
    // Note: Z3 may still output "sat"/"unsat" even when there are errors
    if stdout.contains("(error ") || !output.status.success() {
        // Extract error messages from stdout
        let error_lines: Vec<&str> = stdout
            .lines()
            .filter(|line| line.starts_with("(error "))
            .collect();

        let error_msg = if !error_lines.is_empty() {
            error_lines.join("\n")
        } else if !stderr.is_empty() {
            stderr.to_string()
        } else {
            format!("Z3 failed with exit code: {:?}", output.status.code())
        };

        return Ok(SolverResult::Error(error_msg));
    }

    // Parse Z3 output for result
    let result = if stdout.contains("unsat") {
        SolverResult::Unsat
    } else if stdout.contains("sat") && !stdout.contains("unsat") {
        SolverResult::Sat
    } else if stdout.contains("unknown") || stdout.contains("timeout") {
        SolverResult::Unknown
    } else {
        SolverResult::Error(format!("Unexpected Z3 output: {}", stdout.trim()))
    };

    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    /// Differential tests below self-skip when no Z3 binary is available,
    /// instead of being hard `#[ignore]`d. This means `cargo test` in this
    /// crate automatically exercises real differential testing against Z3
    /// whenever Z3 happens to be installed (e.g. in a dev environment or a
    /// CI image with Z3 present), with no `--ignored` flag required, while
    /// still never failing a run where Z3 is absent.
    macro_rules! skip_if_no_z3 {
        () => {
            if find_z3().is_none() {
                eprintln!(
                    "skipping: Z3 not found in {:?} or PATH (install Z3 to run this differential test)",
                    &Z3_PATHS[..Z3_PATHS.len() - 1]
                );
                return Ok(());
            }
        };
    }

    #[test]
    fn test_z3_sat() -> Result<()> {
        skip_if_no_z3!();
        let mut file = NamedTempFile::new()?;
        writeln!(file, "(set-logic QF_LIA)")?;
        writeln!(file, "(declare-const x Int)")?;
        writeln!(file, "(assert (= x 42))")?;
        writeln!(file, "(check-sat)")?;

        let result = run_z3(file.path())?;
        assert_eq!(result, SolverResult::Sat);
        Ok(())
    }

    #[test]
    fn test_z3_unsat() -> Result<()> {
        skip_if_no_z3!();
        let mut file = NamedTempFile::new()?;
        writeln!(file, "(set-logic QF_LIA)")?;
        writeln!(file, "(declare-const x Int)")?;
        writeln!(file, "(assert (< x 0))")?;
        writeln!(file, "(assert (> x 0))")?;
        writeln!(file, "(check-sat)")?;

        let result = run_z3(file.path())?;
        assert_eq!(result, SolverResult::Unsat);
        Ok(())
    }

    /// Regression test: `find_z3` must not panic or hang when no Z3 binary
    /// exists anywhere on `PATH` or the well-known install locations; it
    /// should return `None` so callers (including the tests above) can
    /// gracefully skip rather than erroring out.
    #[test]
    fn test_find_z3_does_not_panic() {
        let _ = find_z3();
    }
}
