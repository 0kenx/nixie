//! Minimal solver-level reproducer for the wide-integer-literal failures.
//!
//! Builds the terms directly with `nixie-core`, with no TLA+ involved, so the
//! finding is actionable for the solver rather than filtered through the front
//! end. See `docs/studies/2026-09-13-lia-wide-literal-arithmetic.md`.

use nixie_core::TermManager;
use nixie_solver::{Solver, SolverResult};
use num_bigint::BigInt;

fn check(label: &str, lit: &str) {
    let Ok(v) = lit.parse::<BigInt>() else {
        println!("{label}: unparsable");
        return;
    };
    let mut tm = TermManager::new();
    let a = tm.mk_int(v.clone());
    let one = tm.mk_int(1);
    let sum = tm.mk_add([a, one]);
    let expected = tm.mk_int(v + 1);
    let claim = tm.mk_eq(sum, expected);
    // `(x + 1) = (x + 1)` is valid, so its negation must be unsatisfiable.
    let negated = tm.mk_not(claim);
    let mut s = Solver::new();
    s.assert(negated, &mut tm);
    let r = s.check(&mut tm);
    let verdict = match r {
        SolverResult::Unsat => "Unsat (correct)",
        SolverResult::Sat => "Sat (WRONG: the claim is valid)",
        SolverResult::Unknown => "Unknown (incomplete)",
    };
    println!("{label:26} {verdict}");
}

fn main() {
    check("2^62 - 1", "4611686018427387903");
    check("i64::MAX - 1", "9223372036854775806");
    check("i64::MAX", "9223372036854775807");
    check("2^64 - 1", "18446744073709551615");
    check("2^96 - 1", "79228162514264337593543950335");
}
