//! Regression tests for the MBQI finite-exhaustion `Satisfied` soundness
//! gates (2026-09, the CLEARSY/00779 false-`sat` class).
//!
//! `MBQIResult::Satisfied` may conclude `sat` from "no counterexample found"
//! only when the counterexample enumeration **provably covered every value
//! the completed model can exhibit** for each bound sort.  Three gates, each
//! of which failed open before this fix and is pinned here:
//!
//! 1. **Truncated pool replacement** — the injected candidate pool (ground
//!    terms of the problem) used to *replace* the model-derived candidates
//!    and was then truncated to 10 entries.  CLEARSY/00779 enumerated 10 of
//!    a 2405-term pool over a model with 2270 distinct `U` values while the
//!    exhaustion check counted an 8-value universe: `sat` for a goal z3
//!    refutes (`:status unsat`).  The pool now merges *after* the required
//!    values, and the coverage verdict is recorded per sort per round.
//!
//! 2. **Universe undercount** — the "universe" the old check counted is a
//!    `MAX_UNIVERSE_SIZE`-truncated *sample* (8 of 2270 values).  The
//!    required set is now harvested untruncated from assignments, function
//!    tables and the universe.
//!
//! 3. **Vacuous / out-of-kind coverage** — a constants-only goal over `U`
//!    yielded an empty required set (vacuously "covered"), and the refactor
//!    initially let infinite sorts (`Int`) claim exhaustion over their model
//!    values.  Only `Bool` and uninterpreted sorts can be exhaustive at all,
//!    and an uninterpreted sort with no harvestable values records *not
//!    covered* (SMT-LIB domains are non-empty: no values found is a harvest
//!    failure, not an empty domain).

use nixie_solver::Context;

fn run(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script)
        .expect("script should parse and run")
}

fn last_status(output: &[String]) -> &str {
    output
        .iter()
        .rev()
        .find(|line| {
            let t = line.trim();
            matches!(t, "sat" | "unsat" | "unknown")
        })
        .map(String::as_str)
        .unwrap_or("<no verdict>")
}

/// Twelve distinct `U` constants; the negated existential needs exactly
/// `c12`, which never fits a 10-entry truncated candidate list.  The goal is
/// `unsat`; the pre-fix solver printed `sat` from vacuously-covered finite
/// exhaustion.  Any decisive answer must be the right one.
#[test]
fn truncated_pool_over_uninterpreted_sort_is_never_wrong() {
    let consts: Vec<String> = (1..=12)
        .map(|i| format!("(declare-const c{i} U)"))
        .collect();
    let distinct = format!(
        "(assert (distinct {}))",
        (1..=12)
            .map(|i| format!("c{i}"))
            .collect::<Vec<_>>()
            .join(" ")
    );
    let script = format!(
        "(set-logic UF)\n(declare-sort U 0)\n{}\n{}\n(assert (not (exists ((l U)) (= l c12))))\n(check-sat)\n",
        consts.join("\n"),
        distinct
    );
    let output = run(&script);
    assert_ne!(last_status(&output), "sat");
}

/// The CLEARSY shape at CLEARSY scale-in-miniature: a `mem` table whose
/// falsifying value sits late in the pool.  Ground pins make the goal
/// `unsat`; the falsifier must be found by search or the exhaustion must
/// refuse to certify – never a `sat`.
#[test]
fn late_falsifier_in_big_pool_is_never_sat() {
    let consts: Vec<String> = (1..=12)
        .map(|i| format!("(declare-const c{i} U)"))
        .collect();
    let distinct = format!(
        "(assert (distinct {}))",
        (1..=12)
            .map(|i| format!("c{i}"))
            .collect::<Vec<_>>()
            .join(" ")
    );
    let script = format!(
        "(set-logic UF)\n(declare-sort U 0)\n{}\n{}\n(declare-fun mem (U U) Bool)\n(declare-const g U)\n(assert (= g c11))\n(assert (mem c12 g))\n(assert (not (exists ((l U)) (mem l g))))\n(check-sat)\n",
        consts.join("\n"),
        distinct
    );
    let output = run(&script);
    assert_eq!(last_status(&output), "unsat");
}

/// A genuinely exhaustive small domain still earns its `sat`: two constants,
/// `P` true on both, `∀x. P x` holds in the model and the enumeration
/// covers the whole (2-element) domain.
#[test]
fn small_exhaustive_domain_still_sat() {
    let output = run(r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-const c1 U)
        (declare-const c2 U)
        (declare-fun P (U) Bool)
        (assert (forall ((x U)) (P x)))
        (assert (P c1))
        (assert (P c2))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "sat");
}

/// Exhaustive small domain with a falsifier: `∀x. x = c1` is refuted by the
/// distinct `c2`, and the enumeration must find it.
#[test]
fn small_exhaustive_domain_falsifier_is_unsat() {
    let output = run(r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-const c1 U)
        (declare-const c2 U)
        (assert (distinct c1 c2))
        (assert (forall ((x U)) (= x c1)))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "unsat");
}

/// Infinite domains must never claim exhaustion, whatever model values they
/// carry: `∀x:Int. x ≤ 7` is falsified at 8, outside any model-value sample,
/// and the goal is `unsat` only through real arithmetic reasoning – never a
/// sampled `sat`.
#[test]
fn infinite_sort_never_claims_exhaustion() {
    let output = run(r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (= (f 0) 0))
        (assert (forall ((x Int)) (<= (f x) 7)))
        (assert (>= (f 8) 8))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "unsat");
}

/// Empty-domain seeding must not manufacture exhaustion coverage: a
/// sort whose only visible elements are the synthetic `u!i` seeds of
/// model completion may not conclude `Satisfied` while the problem's own
/// declared constants of that sort sit outside the truncated candidate
/// list.  (The seeding landed together with the `pool_covered` guard in
/// `build_candidate_lists`; this pin is the CLEARSY shape over a seeded
/// sort.)
#[test]
fn seeded_empty_domain_does_not_vacuously_satisfy() {
    let output = run(r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun P (U) Bool)
        (declare-const c1 U)
        (declare-const c2 U)
        (assert (forall ((x U)) (P x)))
        (assert (not (P c1)))
        (assert (not (P c2)))
        (check-sat)
    "#);
    assert_eq!(last_status(&output), "unsat");
}

/// The original file, kept as an end-to-end guard: `:status unsat`, z3
/// `unsat`; nixie must never print `sat` for it (honest `unknown` until
/// E-matching gains the missing depth).
#[test]
#[ignore = "external corpus: run with the SMT-LIB checkout present"]
fn clearsy_00779_is_never_sat() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../smt-lib/non-incremental/UF/20190906-CLEARSY/0016/00779.smt2"
    );
    let Ok(source) = std::fs::read_to_string(path) else {
        eprintln!("corpus file absent; skipping");
        return;
    };
    let output = run(&source);
    assert_ne!(last_status(&output), "sat");
}
