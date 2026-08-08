//! Known-unsound SMT-LIB instances — soundness regression guards.
//!
//! These five instances are UNSAT (verified by z3) on which some oxiz build
//! has answered `sat`. They are checked in as guards so a future change can
//! never silently (re)introduce the wrong verdict without a test going red.
//!
//! Each test asserts only **soundness** — the solver must not answer `sat` on
//! an UNSAT instance. It does *not* require the solver to reach `unsat`: oz
//! times out on some of these (notably `vhard7`), and `unknown`/timeout is a
//! sound answer. Pinning `!= sat` is the soundness bar; reaching `unsat` is a
//! separate completeness goal (see INTEGRATION_NOTES.md).
//!
//! The instances and their status (differential run vs z3, sample seed
//! 20260807, release builds) at the time these were added:
//!
//! | instance | logic | z3 | main | integrate(0.3.2) | status |
//! |----------|-------|----|------|------------------|--------|
//! | vhard7            | QF_UFIDL | unsat | —(timeout) | **sat** | FIXED on this branch (collect_ground_subterms `let` descent); test is live |
//! | bench_679         | QF_BV    | unsat | sat | sat | pre-existing main BV bug (bvule/bvshl path); v0.3.2 correct → port candidate; `#[ignore]` |
//! | ext_con_064_002_0512 | QF_BV  | unsat | sat | sat | pre-existing main BV bug; `#[ignore]` |
//! | storecomm_t3_np_sf_ni_00010_001 | QF_AUFLIA | unsat | sat | sat | pre-existing main bug; `#[ignore]` |
//! | xs_8_13           | QF_UFLIA | unsat | sat | sat | pre-existing main bug; `#[ignore]` |
//!
//! The four `#[ignore]`d tests are pre-existing on `main` (not introduced by
//! the 0.3.2 integration) and are kept as documented known-failing guards:
//! un-ignoring them is the acceptance criterion for the respective follow-up
//! fix, not something this integration owes.

use oxiz_solver::{Context, SolverResult};

/// Read an SMT-LIB file relative to the workspace root and solve it under a
/// wall-clock budget, returning the solver's verdict (or `Unknown` on timeout
/// / parse error). `rel` is relative to the workspace root (`smt-lib/...`).
fn solve_file(rel: &str, timeout_ms: u64) -> SolverResult {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../");
    let full = format!("{path}{rel}");
    let Ok(script) = std::fs::read_to_string(&full) else {
        eprintln!("skipping {rel}: file not present (smt-lib not checked out?)");
        return SolverResult::Unknown;
    };
    let mut ctx = Context::new();
    ctx.set_timeout_ms(timeout_ms);
    let outputs = ctx.execute_script(&script).unwrap_or_default();
    for tok in outputs.iter().rev() {
        match tok.trim() {
            "sat" => return SolverResult::Sat,
            "unsat" => return SolverResult::Unsat,
            "unknown" => return SolverResult::Unknown,
            _ => {}
        }
    }
    SolverResult::Unknown
}

/// Soundness bar for a known-UNSAT instance: never answer `sat`.
fn assert_not_sat(label: &str, rel: &str, timeout_ms: u64) {
    let res = solve_file(rel, timeout_ms);
    assert_ne!(
        res,
        SolverResult::Sat,
        "{label}: solver answered sat on a z3-UNSAT instance (soundness bug). \
         verdict={res:?}; expected unsat (z3) — unknown/timeout is acceptable."
    );
}

const TIMEOUT_MS: u64 = 6_000;
/// Longer budget for the `#[ignore]`d pre-existing cases: their wrong-`sat`
/// arrives late (e.g. `ext_con_064` at ~8s in release), so a short budget
/// would return `unknown` first and silently miss the bug. These don't run
/// in the normal suite, so the extra wall-clock is paid only under
/// `--ignored`.
const IGNORED_TIMEOUT_MS: u64 = 10_000;

// ─── vhard7: the branch regression. MUST pass. ───────────────────────────
//
// `git bisect` on vhard7 localizes the branch's wrong-Sat to 0c526e9c, whose
// `collect_ground_subterms` treated `let` as opaque — so the mux axioms for
// the `ite`s inside vhard7's wrapping `let` were never emitted. Fixed in
// bb73c30c (descend into `let`, keep `Forall`/`Exists` opaque). oz (=v0.3.2)
// still returns the wrong `sat` here; main times out. This test pins that the
// fix stays in: a regression to the `let`-opaque walk makes vhard7 answer
// `sat` in well under the budget.
#[test]
fn vhard7_is_not_sat() {
    assert_not_sat(
        "vhard7",
        "smt-lib/non-incremental/QF_UFIDL/mathsat/EufLaArithmetic/vhard/vhard7.smt2",
        TIMEOUT_MS,
    );
}

// ─── Pre-existing on main (also wrong on integrate). Known-failing guards. ─

#[ignore = "pre-existing main BV soundness bug: bench_679 (bvule/bvshl-heavy) \
            returns sat where z3 says unsat. v0.3.2 answers unsat correctly, so \
            this is a port candidate (diff main vs v0.3.2 on the BV comparison/ \
            shift encoding). NOT introduced by the 0.3.2 integration; un-ignore \
            when that BV path is ported/fixed."]
#[test]
fn bench_679_is_not_sat() {
    assert_not_sat(
        "bench_679",
        "smt-lib/non-incremental/QF_BV/sage/app9/bench_679.smt2",
        IGNORED_TIMEOUT_MS,
    );
}

#[ignore = "pre-existing main BV soundness bug: ext_con_064_002_0512 returns \
            sat where z3 says unsat (release-mode manifestation, ~8s; also wrong \
            on integrate and v0.3.2). NOTE: in a debug build this test currently \
            returns `unknown` before the wrong-`sat` is reached (debug is too slow \
            to hit the bad state inside the budget), so it only fails under \
            `--release` or a much larger budget — the guard is real but \
            release-only for this instance. Un-ignore when fixed."]
#[test]
fn ext_con_064_is_not_sat() {
    assert_not_sat(
        "ext_con_064_002_0512",
        "smt-lib/non-incremental/QF_BV/bruttomesso/core/ext_con_064_002_0512.smt2",
        IGNORED_TIMEOUT_MS,
    );
}

#[ignore = "pre-existing main soundness bug: storecomm_t3_np_sf_ni_00010_001 \
            (QF_AUFLIA) returns sat where z3 says unsat. Also wrong on integrate \
            and v0.3.2. Un-ignore when fixed."]
#[test]
fn storecomm_t3_is_not_sat() {
    assert_not_sat(
        "storecomm_t3",
        "smt-lib/non-incremental/QF_AUFLIA/storecomm/storecomm_t3_np_sf_ni_00010_001.cvc.smt2",
        IGNORED_TIMEOUT_MS,
    );
}

#[ignore = "pre-existing main soundness bug: xs_8_13 (QF_UFLIA) returns sat \
            where z3 says unsat. Also wrong on integrate and v0.3.2. \
            Un-ignore when fixed."]
#[test]
fn xs_8_13_is_not_sat() {
    assert_not_sat(
        "xs_8_13",
        "smt-lib/non-incremental/QF_UFLIA/wisas/xs_8_13.smt2",
        IGNORED_TIMEOUT_MS,
    );
}
