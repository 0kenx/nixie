//! QF_NIA counterexample fixture suite (`bench/qf_nia_ce/`).
//!
//! Pure math SMT-LIB2 instances. Each file carries `;; expected: sat|unsat`.
//! Every fixture is checked for an exact match — no gap allowlist.

use oxiz_solver::{Context, SolverResult};
use std::path::{Path, PathBuf};

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../bench/qf_nia_ce")
}

fn run_smt2(path: &Path) -> SolverResult {
    let source =
        std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let mut ctx = Context::new();
    match ctx.execute_script(&source) {
        Ok(outputs) => {
            for line in outputs.iter().rev() {
                match line.trim() {
                    "sat" => return SolverResult::Sat,
                    "unsat" => return SolverResult::Unsat,
                    "unknown" => return SolverResult::Unknown,
                    _ => {}
                }
            }
            SolverResult::Unknown
        }
        Err(e) => panic!("execute {}: {e}", path.display()),
    }
}

fn expected_from_file(path: &Path) -> Option<SolverResult> {
    let source = std::fs::read_to_string(path).ok()?;
    for line in source.lines().take(12) {
        let lower = line.to_lowercase();
        if !(lower.contains("expected:") || lower.contains("expected :")) {
            continue;
        }
        if lower.contains("unsat") {
            return Some(SolverResult::Unsat);
        }
        if lower.contains("unknown") {
            return Some(SolverResult::Unknown);
        }
        if lower.contains("sat") {
            return Some(SolverResult::Sat);
        }
    }
    None
}

fn collect_fixtures() -> Vec<PathBuf> {
    let dir = fixture_dir();
    assert!(dir.is_dir(), "missing fixture dir {}", dir.display());
    let mut paths: Vec<_> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("read_dir {}: {e}", dir.display()))
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "smt2"))
        .collect();
    paths.sort();
    assert!(!paths.is_empty(), "no .smt2 in {}", dir.display());
    paths
}

fn classify(exp: SolverResult, actual: SolverResult) -> &'static str {
    match (exp, actual) {
        (e, a) if e == a => "ok",
        (SolverResult::Sat, SolverResult::Unsat) | (SolverResult::Unsat, SolverResult::Sat) => {
            "wrong"
        }
        (_, SolverResult::Unknown) => "unknown",
        (SolverResult::Unknown, _) => "unexpected_decisive",
        _ => "mismatch",
    }
}

#[test]
fn qf_nia_ce_all_fixtures() {
    let mut rows = Vec::new();
    let mut exact = 0usize;
    let mut wrong = 0usize;
    let mut unknown = 0usize;
    let mut other = 0usize;

    for path in collect_fixtures() {
        let name = path
            .file_name()
            .unwrap()
            .to_string_lossy()
            .into_owned();
        let exp = expected_from_file(&path)
            .unwrap_or_else(|| panic!("{name}: missing ;; expected: sat|unsat"));
        let actual = run_smt2(&path);
        let tag = classify(exp, actual);
        match tag {
            "ok" => exact += 1,
            "wrong" => wrong += 1,
            "unknown" => unknown += 1,
            _ => other += 1,
        }
        rows.push((name, exp, actual, tag));
    }

    let total = rows.len();
    eprintln!("qf_nia_ce: {exact}/{total} exact  wrong={wrong}  unknown={unknown}  other={other}");
    for (name, exp, actual, tag) in &rows {
        eprintln!("  {tag:<10} {name:<40} expected={exp:?} got={actual:?}");
    }

    let failures: Vec<String> = rows
        .iter()
        .filter(|(_, _, _, tag)| *tag != "ok")
        .map(|(name, exp, actual, tag)| format!("{name}: expected {exp:?}, got {actual:?} [{tag}]"))
        .collect();

    assert!(
        failures.is_empty(),
        "qf_nia_ce: {exact}/{total} exact, {} gap(s):\n{}",
        failures.len(),
        failures.join("\n")
    );
}
