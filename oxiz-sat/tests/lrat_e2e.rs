//! End-to-end LRAT proof generation + `lrat-check` verification.
//!
//! These tests build a small UNSAT formula, solve it with LRAT proof logging
//! enabled, write the matching DIMACS file, and shell out to the bundled
//! `lrat-check` to confirm `c VERIFIED`. They are gated on the `LratCheck`
//! env var pointing at a built `lrat-check` binary (set by the CI script) so
//! they no-op where the checker isn't available.

#![cfg(test)]

use oxiz_sat::{Lit, Solver, SolverResult};
use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

/// Path to a built `lrat-check` binary (override via `LRAT_CHECK`). If none
/// is found, lazily compile the vendored `oxiz-sat/tools/lrat-check.c` so the
/// test is self-contained in CI.
fn lrat_check_bin() -> Option<PathBuf> {
    use std::sync::OnceLock;
    static BIN: OnceLock<Option<PathBuf>> = OnceLock::new();
    BIN.get_or_init(|| {
        if let Ok(p) = std::env::var("LRAT_CHECK") {
            return Some(PathBuf::from(p));
        }
        for c in ["/tmp/lrat-check", "./lrat-check", "../lrat-check"] {
            let p = PathBuf::from(c);
            if p.exists() {
                return Some(p);
            }
        }
        build_vendored_lrat_check()
    })
    .clone()
}

fn build_vendored_lrat_check() -> Option<PathBuf> {
    let src = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tools/lrat-check.c");
    if !src.exists() {
        return None;
    }
    let bin = std::env::temp_dir().join("oxiz-lrat-check-bin");
    let src_mtime = std::fs::metadata(&src).ok()?.modified().ok()?;
    let bin_mtime = std::fs::metadata(&bin).ok().and_then(|m| m.modified().ok());
    if bin.is_file() && bin_mtime.is_some_and(|t| t >= src_mtime) {
        return Some(bin);
    }
    let status = std::process::Command::new("cc")
        .args(["-O2", "-o"])
        .arg(&bin)
        .arg(&src)
        .status()
        .ok()?;
    if status.success() { Some(bin) } else { None }
}

/// Solve `clauses` (over `nvars` variables) with LRAT logging to `lrat_path`,
/// and write the DIMACS formula to `cnf_path` in the *same* clause order so
/// `lrat-check`'s file-position numbering matches the solver's original-clause
/// ids.
fn solve_unsat_with_lrat(
    nvars: usize,
    clauses: &[Vec<i32>],
    cnf_path: &std::path::Path,
    lrat_path: &std::path::Path,
    binary: bool,
) -> SolverResult {
    let mut cnf = fs::File::create(cnf_path).unwrap();
    writeln!(cnf, "p cnf {nvars} {}", clauses.len()).unwrap();
    for c in clauses {
        for &l in c {
            write!(cnf, "{l} ").unwrap();
        }
        writeln!(cnf, "0").unwrap();
    }
    drop(cnf);

    let mut solver = Solver::new();
    solver.ensure_vars(nvars);
    if binary {
        solver.enable_lrat_proof_binary(lrat_path).unwrap();
    } else {
        solver.enable_lrat_proof(lrat_path).unwrap();
    }
    for c in clauses {
        solver.add_clause(c.iter().map(|&l| Lit::from_dimacs(l)));
    }
    let res = solver.solve();
    solver.disable_proof();
    res
}

fn assert_verified(nvars: usize, clauses: &[Vec<i32>], binary: bool) {
    let Some(checker) = lrat_check_bin() else {
        eprintln!("lrat-check not found; skipping LRAT verification test");
        return;
    };
    use std::sync::atomic::{AtomicU64, Ordering};
    static SEQ: AtomicU64 = AtomicU64::new(0);
    let seq = SEQ.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("oxiz_lrat_e2e_{}_{seq}", std::process::id()));
    let _ = fs::create_dir_all(&dir);
    let cnf = dir.join("in.cnf");
    let lrat = dir.join(if binary { "out.clrat" } else { "out.lrat" });

    let res = solve_unsat_with_lrat(nvars, clauses, &cnf, &lrat, binary);
    assert_eq!(res, SolverResult::Unsat, "expected UNSAT");

    // `lrat-check` is text-only; for binary proofs, decode to text first (this
    // also validates the binary varint encoding end-to-end).
    let check_path = if binary {
        let text = dir.join("out.lrat");
        let bytes = fs::read(&lrat).expect("read clrat");
        fs::write(&text, decode_binary_lrat(&bytes)).expect("write decoded lrat");
        text
    } else {
        lrat.clone()
    };

    let output = Command::new(&checker)
        .arg(&cnf)
        .arg(&check_path)
        .output()
        .expect("failed to run lrat-check");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    if !stdout.contains("VERIFIED") || output.status.code() != Some(0) {
        panic!(
            "lrat-check did NOT verify (binary={binary}):\n--- stdout ---\n{stdout}\n--- stderr ---\n{stderr}\n--- lrat ---\n{}",
            fs::read_to_string(&check_path).unwrap_or_default()
        );
    }
    let _ = fs::remove_dir_all(&dir);
}

/// Decode a binary LRAT proof to its text form (mirrors the encoding in
/// `proof::lrat::LratTracer`).
fn decode_binary_lrat(bytes: &[u8]) -> String {
    fn varint(bytes: &[u8], i: &mut usize) -> u64 {
        let mut x = 0u64;
        let mut shift = 0u32;
        loop {
            let b = bytes[*i];
            *i += 1;
            x |= ((b & 0x7f) as u64) << shift;
            if b & 0x80 == 0 {
                return x;
            }
            shift += 7;
        }
    }
    fn dec_lit(x: u64) -> i32 {
        let idx = (x / 2) as i32;
        if x & 1 == 1 { -idx } else { idx }
    }
    fn dec_id(x: u64) -> i64 {
        let a = (x / 2) as i64;
        if x & 1 == 1 { -a } else { a }
    }
    let mut out = String::new();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'a' => {
                i += 1;
                let id = dec_id(varint(bytes, &mut i));
                out.push_str(&format!("{id} "));
                loop {
                    let l = dec_lit(varint(bytes, &mut i));
                    out.push_str(&format!("{l} "));
                    if l == 0 {
                        break;
                    }
                }
                loop {
                    let h = dec_id(varint(bytes, &mut i));
                    out.push_str(&format!("{h} "));
                    if h == 0 {
                        break;
                    }
                }
                out.push('\n');
            }
            b'd' => {
                i += 1;
                out.push_str("0 d ");
                loop {
                    let h = dec_id(varint(bytes, &mut i));
                    out.push_str(&format!("{h} "));
                    if h == 0 {
                        break;
                    }
                }
                out.push('\n');
            }
            other => panic!("unexpected binary LRAT byte {other:#x} at {i}"),
        }
    }
    out
}

#[test]
fn lrat_text_2var_unsat() {
    // All four sign combinations of x1,x2 → UNSAT.
    assert_verified(
        2,
        &[vec![1, 2], vec![1, -2], vec![-1, 2], vec![-1, -2]],
        false,
    );
}

#[test]
fn lrat_binary_2var_unsat() {
    assert_verified(
        2,
        &[vec![1, 2], vec![1, -2], vec![-1, 2], vec![-1, -2]],
        true,
    );
}

#[test]
fn lrat_text_php3() {
    // Pigeonhole 3 into 2: UNSAT. Clauses: each pigeon in some hole (rows),
    // no two pigeons share a hole (columns). Variables p_{i,h}=i*2+h (1-based).
    let n = 3; // pigeons
    let m = 2; // holes
    let var = |i: usize, h: usize| -> i32 { (1 + (i * m + h)) as i32 };
    let mut clauses = Vec::new();
    for i in 0..n {
        clauses.push((0..m).map(|h| var(i, h)).collect());
    }
    for h in 0..m {
        for i1 in 0..n {
            for i2 in (i1 + 1)..n {
                clauses.push(vec![-var(i1, h), -var(i2, h)]);
            }
        }
    }
    assert_verified(n * m, &clauses, false);
}
