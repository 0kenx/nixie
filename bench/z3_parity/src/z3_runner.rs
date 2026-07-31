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

/// Raw first line of `z3 --version` for the binary `find_z3` resolves (the
/// same one [`run_z3`] uses), e.g. `"Z3 version 4.15.4 - 64 bit"`.
///
/// `None` when no Z3 binary is reachable or the probe itself failed.
pub fn z3_version_raw() -> Option<String> {
    let z3_path = find_z3()?;
    let output = Command::new(z3_path).arg("--version").output().ok()?;
    if !output.status.success() {
        return None;
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    stdout
        .lines()
        .next()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(|line| line.to_string())
}

/// Bare version of the Z3 binary that [`run_z3`] would use, e.g. `"4.15.4"`.
///
/// Z3 verdicts move between releases (Ubuntu's `apt` ships 4.13.3 while the
/// recorded baseline is 4.15.4), so a parity record that does not name the Z3
/// build it was measured against cannot attribute a disagreement to either
/// solver. Recorded per run for exactly that reason.
///
/// When the `--version` output carries no recognisable dotted version the raw
/// line is returned unchanged rather than a guess, so the recorded value is
/// always something that was actually observed.
pub fn z3_version() -> Option<String> {
    let raw = z3_version_raw()?;
    Some(parse_z3_version(&raw).unwrap_or(raw))
}

/// Extract the bare version token (`4.15.4`) from a `z3 --version` line
/// (`Z3 version 4.15.4 - 64 bit`).
fn parse_z3_version(raw: &str) -> Option<String> {
    raw.split_whitespace()
        .find(|token| {
            token.starts_with(|c: char| c.is_ascii_digit())
                && token.contains('.')
                && token.chars().all(|c| c.is_ascii_digit() || c == '.')
        })
        .map(|token| token.to_string())
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

    #[test]
    fn test_parse_z3_version() {
        assert_eq!(
            parse_z3_version("Z3 version 4.15.4 - 64 bit"),
            Some("4.15.4".to_string())
        );
        // The version Ubuntu's apt ships, which the baseline is NOT measured
        // against - it must parse just as cleanly so the mismatch is visible.
        assert_eq!(
            parse_z3_version("Z3 version 4.13.3 - 64 bit"),
            Some("4.13.3".to_string())
        );
    }

    /// Unrecognised output must never be coerced into a plausible-looking
    /// version: callers record the raw line instead, so a metadata header can
    /// only ever claim a version that was actually observed.
    #[test]
    fn test_parse_z3_version_rejects_unrecognized_output() {
        assert_eq!(parse_z3_version("no version here"), None);
        assert_eq!(parse_z3_version(""), None);
    }

    /// The live probe may only report a version when a Z3 binary is actually
    /// reachable, and never an empty one - a metadata header must not be able
    /// to claim a version out of thin air.
    #[test]
    fn test_z3_version_never_invents_a_version() {
        if let Some(version) = z3_version() {
            assert!(is_z3_available());
            assert!(!version.trim().is_empty());
        }
    }
}
