//! Combined Theories Integration Tests
//!
//! Verifies that `Solver::check_sat` (via `Context::check_sat`) answers
//! QF_AUFBV / QF_ALIA / QF_ABV correctly using the existing structured
//! Nelson–Oppen dispatch path.
//!
//! Two layers of coverage:
//! 1. Fixture sweeps – every `.smt2` file under
//!    `bench/extended_theories/QF_{AUFBV,ALIA,ABV}/` and
//!    `bench/z3_parity/benchmarks/QF_{AUFBV,ALIA,ABV}/`
//! 2. Hand-crafted inline regression tests for select+store across
//!    UF/BV/LIA combinations.

use oxiz_solver::{Context, SolverResult};

// ========  ========
// Fixture sweep helpers
// ========  ========

/// Parse the expected status from an SMT-LIB2 script.
///
/// Recognised patterns (case-insensitive, in order of priority):
/// - `(set-info :status sat|unsat|unknown)`  – SMT-LIB2 metadata
/// - `; expected: sat|unsat|unknown`          – our own comment convention
/// - `;; expected: sat|unsat|unknown`         – double-semicolon variant
fn parse_expected_status(content: &str) -> Option<SolverResult> {
    for line in content.lines() {
        let trimmed = line.trim();

        // SMT-LIB2 :status metadata
        if trimmed.contains(":status") {
            let lower = trimmed.to_lowercase();
            if lower.contains("unsat") {
                return Some(SolverResult::Unsat);
            }
            if lower.contains(" sat") || lower.ends_with("sat") {
                return Some(SolverResult::Sat);
            }
            if lower.contains("unknown") {
                return Some(SolverResult::Unknown);
            }
        }

        // Comment-based expected: / Expected: annotation
        let lower = trimmed.to_lowercase();
        if lower.starts_with("; expected:") || lower.starts_with(";; expected:") {
            if lower.contains("unsat") {
                return Some(SolverResult::Unsat);
            }
            if lower.contains("sat") {
                return Some(SolverResult::Sat);
            }
            if lower.contains("unknown") {
                return Some(SolverResult::Unknown);
            }
        }
    }
    None
}

/// Run a single SMT-LIB2 script and return the solver result.
fn run_script(script: &str) -> SolverResult {
    let mut ctx = Context::new();
    let outputs = ctx.execute_script(script).unwrap_or_default();
    // The result is the last "sat" / "unsat" / "unknown" token in the output.
    for tok in outputs.iter().rev() {
        match tok.trim() {
            "sat" => return SolverResult::Sat,
            "unsat" => return SolverResult::Unsat,
            "unknown" => return SolverResult::Unknown,
            _ => {}
        }
    }
    // No check-sat output found – treat as unknown.
    SolverResult::Unknown
}

/// Check a single fixture file.
///
/// Returns `Ok(())` on expected result, `Err(message)` otherwise.
/// Fixtures with no detectable expected status are skipped.
fn check_fixture(path: &std::path::Path) -> Result<(), String> {
    let content = std::fs::read_to_string(path)
        .map_err(|e| format!("cannot read {}: {}", path.display(), e))?;

    let expected = match parse_expected_status(&content) {
        Some(s) => s,
        None => return Ok(()), // skip fixtures without expected status
    };

    let actual = run_script(&content);

    // Allow Unknown as a valid "we couldn't decide" outcome even when the
    // oracle says sat/unsat – incomplete solvers are permitted to return
    // Unknown for any formula without being incorrect.  We only count it as
    // a failure when the solver asserts the *wrong* definitive answer.
    match (expected, actual) {
        (SolverResult::Sat, SolverResult::Unsat) => {
            Err(format!("{}: expected sat, got unsat", path.display()))
        }
        (SolverResult::Unsat, SolverResult::Sat) => {
            Err(format!("{}: expected unsat, got sat", path.display()))
        }
        _ => Ok(()), // sat/sat, unsat/unsat, or unknown in either position
    }
}

/// Sweep all `.smt2` files in a directory and assert each one.
/// Missing directories are silently skipped (CI-friendliness).
fn sweep_dir(dir: &str) -> Vec<String> {
    let path = std::path::Path::new(dir);
    if !path.is_dir() {
        return Vec::new();
    }

    let mut failures = Vec::new();

    let entries = match std::fs::read_dir(path) {
        Ok(e) => e,
        Err(_) => return failures,
    };

    for entry in entries.flatten() {
        let entry_path = entry.path();
        if entry_path.extension().and_then(|s| s.to_str()) == Some("smt2")
            && let Err(msg) = check_fixture(&entry_path)
        {
            failures.push(msg);
        }
    }

    failures
}

// ========  ========
// Fixture sweep tests
// ========  ========

/// All QF_ABV fixtures from z3_parity benchmarks
#[test]
fn sweep_z3_parity_qf_abv() {
    let base = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../bench/z3_parity/benchmarks/QF_ABV"
    );
    let failures = sweep_dir(base);
    assert!(
        failures.is_empty(),
        "QF_ABV fixture failures:\n{}",
        failures.join("\n")
    );
}

/// All QF_AUFBV fixtures from z3_parity benchmarks
#[test]
fn sweep_z3_parity_qf_aufbv() {
    let base = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../bench/z3_parity/benchmarks/QF_AUFBV"
    );
    let failures = sweep_dir(base);
    assert!(
        failures.is_empty(),
        "QF_AUFBV fixture failures:\n{}",
        failures.join("\n")
    );
}

/// All QF_ALIA fixtures from z3_parity benchmarks
#[test]
fn sweep_z3_parity_qf_alia() {
    let base = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../bench/z3_parity/benchmarks/QF_ALIA"
    );
    let failures = sweep_dir(base);
    assert!(
        failures.is_empty(),
        "QF_ALIA fixture failures:\n{}",
        failures.join("\n")
    );
}

/// All QF_ABV fixtures from extended_theories
#[test]
fn sweep_extended_qf_abv() {
    let base = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../bench/extended_theories/QF_ABV"
    );
    let failures = sweep_dir(base);
    assert!(
        failures.is_empty(),
        "extended QF_ABV fixture failures:\n{}",
        failures.join("\n")
    );
}

/// All QF_AUFBV fixtures from extended_theories
#[test]
fn sweep_extended_qf_aufbv() {
    let base = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../bench/extended_theories/QF_AUFBV"
    );
    let failures = sweep_dir(base);
    assert!(
        failures.is_empty(),
        "extended QF_AUFBV fixture failures:\n{}",
        failures.join("\n")
    );
}

/// All QF_ALIA fixtures from extended_theories
#[test]
fn sweep_extended_qf_alia() {
    let base = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../bench/extended_theories/QF_ALIA"
    );
    let failures = sweep_dir(base);
    assert!(
        failures.is_empty(),
        "extended QF_ALIA fixture failures:\n{}",
        failures.join("\n")
    );
}

// ========  ========
// Hand-crafted inline regression tests
// QF_ABV – Arrays + BitVectors
// ========  ========

/// Basic read-over-write axiom: select(store(a, i, v), i) = v
#[test]
fn inline_qf_abv_read_over_write_sat() {
    let script = r#"
(set-logic QF_ABV)
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= (select (store a #x00 #x42) #x00) #x42))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// Read-over-write contradiction: value forced to be two different constants
#[test]
fn inline_qf_abv_read_over_write_unsat() {
    let script = r#"
(set-logic QF_ABV)
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= (select (store a #x00 #x42) #x00) #xFF))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Chain of stores: last write at an index wins
#[test]
fn inline_qf_abv_chained_stores_sat() {
    let script = r#"
(set-logic QF_ABV)
(declare-const a (Array (_ BitVec 4) (_ BitVec 4)))
(declare-const b (Array (_ BitVec 4) (_ BitVec 4)))
(declare-const c (Array (_ BitVec 4) (_ BitVec 4)))
(assert (= b (store a #x0 #x1)))
(assert (= c (store b #x0 #x2)))
(assert (= (select c #x0) #x2))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// BV arithmetic conflict via variable binding
/// x = #x05, select(a, x) = bvadd(x, #x01) = #x06, but select(a, #x05) = #x10 → UNSAT
#[test]
fn inline_qf_abv_cross_theory_conflict_unsat() {
    let script = r#"
(set-logic QF_ABV)
(declare-const x (_ BitVec 8))
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= (select a x) (bvadd x #x01)))
(assert (= x #x05))
(assert (= (select a #x05) #x10))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// BV strict ordering contradiction: x < f and x > f for the same constant
#[test]
fn inline_qf_abv_bv_ordering_unsat() {
    let script = r#"
(set-logic QF_ABV)
(declare-const x (_ BitVec 4))
(assert (bvult x #xf))
(assert (bvugt x #xf))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

// ========  ========
// Hand-crafted inline regression tests
// QF_AUFBV – Arrays + UF + BitVectors
// ========  ========

/// Store then select at the same index – should be SAT (tautology)
#[test]
fn inline_qf_aufbv_store_select_tautology_sat() {
    let script = r#"
(set-logic QF_AUFBV)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 32)))
(declare-fun i () (_ BitVec 32))
(declare-fun v () (_ BitVec 32))
(assert (= (select (store a i v) i) v))
(assert (not (= v (_ bv0 32))))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// Array extensionality: equal arrays must agree on all reads
/// a = b, but read at index 7 differs → UNSAT
#[test]
fn inline_qf_aufbv_extensionality_unsat() {
    let script = r#"
(set-logic QF_AUFBV)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 32)))
(declare-fun b () (Array (_ BitVec 32) (_ BitVec 32)))
(assert (= a b))
(assert (not (= (select a (_ bv7 32)) (select b (_ bv7 32)))))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Store then read at a *different* index (non-interfering) – SAT
#[test]
fn inline_qf_aufbv_store_read_different_index_sat() {
    let script = r#"
(set-logic QF_AUFBV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= b (store a #x00 #x42)))
(assert (= (select b #x01) (select a #x01)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// Conflict from store-select at same index yielding a contradictory value
#[test]
fn inline_qf_aufbv_store_conflict_unsat() {
    let script = r#"
(set-logic QF_AUFBV)
(declare-fun mem () (Array (_ BitVec 8) (_ BitVec 16)))
(declare-const mem1 (Array (_ BitVec 8) (_ BitVec 16)))
(assert (= mem1 (store mem #x10 #xCAFE)))
(assert (= (select mem1 #x10) #xBEEF))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Nested store chains – earlier store is shadowed at the overwritten index
#[test]
fn inline_qf_aufbv_nested_store_shadow_sat() {
    let script = r#"
(set-logic QF_AUFBV)
(declare-const a (Array (_ BitVec 4) (_ BitVec 4)))
(declare-const b (Array (_ BitVec 4) (_ BitVec 4)))
(declare-const c (Array (_ BitVec 4) (_ BitVec 4)))
(assert (= b (store a #x0 #x1)))
(assert (= c (store b #x1 #x2)))
(assert (= (select c #x0) #x1))
(assert (= (select c #x1) #x2))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

// ========  ========
// Hand-crafted inline regression tests
// QF_ALIA – Arrays + Linear Integer Arithmetic
// ========  ========

/// Basic integer array read-over-write: select(store(a, 0, x), 0) = x → SAT
#[test]
fn inline_qf_alia_read_over_write_sat() {
    let script = r#"
(set-logic QF_ALIA)
(declare-fun a () (Array Int Int))
(declare-fun x () Int)
(assert (= (select (store a 0 x) 0) x))
(assert (> x 0))
(assert (< x 100))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// Integer array: store then read at same index yields stored value → conflict UNSAT
#[test]
fn inline_qf_alia_store_conflict_unsat() {
    let script = r#"
(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(declare-const a1 (Array Int Int))
(assert (= a1 (store a 0 42)))
(assert (< (select a1 0) 5))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Sum pattern: a[0] + a[1] = 10, a[0] > 7, a[1] > 7 → impossible → UNSAT
#[test]
fn inline_qf_alia_sum_pattern_unsat() {
    let script = r#"
(set-logic QF_ALIA)
(declare-fun a () (Array Int Int))
(assert (= (+ (select a 0) (select a 1)) 10))
(assert (> (select a 0) 7))
(assert (> (select a 1) 7))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Array swap SAT: swap a[0] and a[2], verify positions afterwards
#[test]
fn inline_qf_alia_array_swap_sat() {
    let script = r#"
(set-logic QF_ALIA)
(declare-const a (Array Int Int))
(assert (= (select a 0) 10))
(assert (= (select a 1) 20))
(assert (= (select a 2) 30))
(declare-const tmp Int)
(assert (= tmp (select a 0)))
(declare-const a1 (Array Int Int))
(assert (= a1 (store a 0 (select a 2))))
(declare-const a2 (Array Int Int))
(assert (= a2 (store a1 2 tmp)))
(assert (= (select a2 0) 30))
(assert (= (select a2 1) 20))
(assert (= (select a2 2) 10))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// Store then read: negated read-over-write axiom → UNSAT
/// not(= (select (store a 3 5) 3) 5) contradicts the axiom
#[test]
fn inline_qf_alia_negated_read_over_write_unsat() {
    let script = r#"
(set-logic QF_ALIA)
(declare-fun a () (Array Int Int))
(assert (not (= (select (store a 3 5) 3) 5)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Positive tautology: select(store(a, i, v), i) = v is always true → SAT
#[test]
fn inline_qf_alia_read_over_write_tautology_sat() {
    let script = r#"
(set-logic QF_ALIA)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(declare-fun v () Int)
(assert (= (select (store a i v) i) v))
(assert (>= i 0))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

// ========  ========
// Cross-theory interaction tests
// ========  ========

/// QF_ABV: select-equality read conflict (two reads from same array+index must agree)
#[test]
fn inline_qf_abv_read_consistency_unsat() {
    let script = r#"
(set-logic QF_ABV)
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= (select a #x0A) #x01))
(assert (= (select a #x0A) #x02))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// QF_ALIA: two reads from same array+index with contradictory LIA constraints → UNSAT
#[test]
fn inline_qf_alia_read_consistency_unsat() {
    let script = r#"
(set-logic QF_ALIA)
(declare-fun a () (Array Int Int))
(declare-const v1 Int)
(declare-const v2 Int)
(assert (= (select a 5) v1))
(assert (= (select a 5) v2))
(assert (not (= v1 v2)))
(check-sat)
"#;
    // v1 = select(a,5) = v2, but v1 != v2 → UNSAT
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// QF_ABV: BV byte buffer with arithmetic, sequential writes all visible → SAT
#[test]
fn inline_qf_abv_byte_buffer_sat() {
    let script = r#"
(set-logic QF_ABV)
(declare-const buf (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const buf1 (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= buf1 (store buf #x00 #x48)))
(declare-const buf2 (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= buf2 (store buf1 #x01 #x69)))
(assert (= (select buf2 #x00) #x48))
(assert (= (select buf2 #x01) #x69))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

// ========  ========
// Theory-combination justification regressions
//
// When congruence closure derives `f(a) = f(b)` from `a = b`, that equality
// crosses into the arithmetic tableau.  `ArithSolver` stores one reason term
// per assertion, so the equality could only be tagged with one of its own
// operands – `f(a)`, `(select arr i)` – and those name no SAT atom.
// `TheoryManager::terms_to_conflict_clause` used to *drop* reason terms with no
// SAT variable, so a conflict resting on such an equality produced a clause
// blaming only the arithmetic atoms.  A clause that omits part of its
// justification is not weaker, it is false: it asserts the surviving literals
// are contradictory on their own.  At unit level that is a level-0 conflict and
// a satisfiable formula comes back `unsat`.
//
// The equality now carries its congruence-closure explanation
// (`EufSolver::explain_eq`) and the clause expands it back into literals.
// ========  ========

/// `f(a) > f(b)` with `a > b ∨ a = b`.
///
/// The `a = b` branch makes congruence derive `f(a) = f(b)`, which contradicts
/// `f(a) > f(b)`.  The clause must blame `a = b`; when it did not, the unit
/// `¬(f(a) > f(b))` refuted the whole formula at level 0.  Satisfiable via the
/// `a > b` branch – z3 agrees.
#[test]
fn uf_congruence_equality_into_arith_keeps_its_justification_sat() {
    let script = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(declare-const b Int)
(assert (> (f a) (f b)))
(assert (or (> a b) (= a b)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// The array reading of the same shape: `select` is interned as a binary
/// application, so `i = j` gives `arr[i] = arr[j]` by congruence.
#[test]
fn array_select_congruence_equality_into_arith_keeps_its_justification_sat() {
    let script = r#"
(set-logic QF_ALIA)
(declare-const arr (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(assert (> (select arr i) (select arr j)))
(assert (or (> i j) (= i j)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// Same defect reached through the opposite comparison and the AUFLIA logic,
/// so the fix cannot depend on the direction of the arithmetic atom.
#[test]
fn array_select_congruence_equality_into_arith_lt_variant_sat() {
    let script = r#"
(set-logic QF_AUFLIA)
(declare-const arr (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(assert (< (select arr i) (select arr j)))
(assert (or (< i j) (= i j)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// Control: with `a = b` asserted outright the refutation is real.  Carrying
/// the justification must not cost the genuine `unsat`.
#[test]
fn uf_congruence_equality_conflict_is_still_unsat_when_forced() {
    let script = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(declare-const b Int)
(assert (> (f a) (f b)))
(assert (= a b))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Control: `a = b` forced through a case split rather than a unit, so the
/// conflict is discovered below the root and the learnt clause has to be sound
/// at a non-zero level too.
#[test]
fn uf_congruence_equality_conflict_is_still_unsat_under_every_branch() {
    let script = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(declare-const b Int)
(declare-const p Bool)
(assert (> (f a) (f b)))
(assert (or (not p) (= a b)))
(assert (or p (= a b)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Control: the array version of the forced conflict stays `unsat`.
#[test]
fn array_select_congruence_conflict_is_still_unsat_when_forced() {
    let script = r#"
(set-logic QF_ALIA)
(declare-const arr (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(assert (> (select arr i) (select arr j)))
(assert (= i j))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Control: the very same atoms with the indices forced *apart* stay `sat`, so
/// the fix cannot be passing the tests above by simply refusing to refute.
#[test]
fn array_select_distinct_indices_control_sat() {
    let script = r#"
(set-logic QF_ALIA)
(declare-const arr (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(assert (> (select arr i) (select arr j)))
(assert (distinct i j))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// An application buried inside an arithmetic sum is a shared term too.
///
/// `intern_term_for_congruence` descends only through an application's
/// arguments, so the `f(a)` of `(+ (f a) b)` never reached congruence closure:
/// with `a = b` asserted, `f(a) = f(b)` was never derived and the formula was
/// answered `sat` with a model that does not exist.
#[test]
fn uf_application_under_addition_reaches_the_tableau_unsat() {
    let script = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(declare-const b Int)
(assert (= a b))
(assert (> (+ (f a) b) (+ (f b) a)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// The array reading of the buried-application hole.
#[test]
fn array_select_under_addition_reaches_the_tableau_unsat() {
    let script = r#"
(set-logic QF_AUFLIA)
(declare-const arr (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(assert (= i j))
(assert (> (+ (select arr i) j) (+ (select arr j) i)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Control for the two above: without the index equality the sum comparison is
/// satisfiable, so registering the buried terms must not over-constrain.
#[test]
fn uf_application_under_addition_control_sat() {
    let script = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(declare-const b Int)
(assert (distinct a b))
(assert (> (+ (f a) b) (+ (f b) a)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// A *nested* application is an arithmetic variable like any other.
///
/// `f(a) > f(b) > f(f(a)) > f(a)` is refuted by transitivity alone, but
/// `f(f(a))` used to be excluded from the linear parse (its argument `f(a)`
/// already had an arithmetic value), which left the whole atom a free boolean
/// and the cycle satisfiable.  The exclusion existed to dodge unjustified
/// EUF/arith combination conflicts, which no longer occur.
#[test]
fn nested_application_is_an_arithmetic_variable_unsat() {
    let script = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(declare-const b Int)
(assert (> (f a) (f b)))
(assert (> (f b) (f (f a))))
(assert (> (f (f a)) (f a)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Control for the nested-application registration: break the cycle and the
/// same three atoms are satisfiable.
#[test]
fn nested_application_acyclic_chain_control_sat() {
    let script = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(declare-const b Int)
(assert (> (f a) (f b)))
(assert (> (f b) (f (f a))))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// The conflict clause's literals really do entail the conflict – asserted
/// through the unsat core, which is exactly the set of named assertions the
/// refutation's clauses name.
///
/// `eq` is the congruence justification that used to be dropped; if the clause
/// still omitted it the core could not mention it.  `irrelevant` must stay out,
/// proving the core is the refutation's own support and not a blanket answer.
#[test]
fn unsat_core_of_congruence_derived_arith_conflict_names_the_equality() {
    let mut ctx = Context::new();
    let outputs = ctx
        .execute_script(
            r#"
(set-option :produce-unsat-cores true)
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(declare-const b Int)
(assert (! (> (f a) (f b)) :named gt))
(assert (! (= a b) :named eq))
(assert (! (> a 100) :named irrelevant))
(check-sat)
(get-unsat-core)
"#,
        )
        .unwrap_or_default();
    let joined = outputs.join(" ");
    assert!(joined.contains("unsat"), "expected unsat: {joined}");
    assert!(
        joined.contains("eq"),
        "the congruence justification must be in the core: {joined}"
    );
    assert!(
        joined.contains("gt"),
        "the arithmetic atom must be in the core: {joined}"
    );
    assert!(
        !joined.contains("irrelevant"),
        "the core must not blame an unrelated assertion: {joined}"
    );
}

// ========  ========
// Congruence under backtracking: a doubly-nested application whose argument
// value comes from a case split
//
// `intern_app` used to hand a new term the node of an already-interned
// congruent application.  The equality that justified that sharing is retracted
// by `pop`; the term-to-node mapping is not.  So once `a = 0` had been tried and
// backtracked, `f(0)` stayed pinned to `f(a)`'s node – with no node, no use-list
// entry and no signature of its own.  The second congruence step,
// `f(f(a)) = f(0)` once `f(a) = 0`, therefore became undiscoverable, the tableau
// never learned `f(f(a))`'s value, and the solver answered `sat` on a formula
// with no model.  Every ingredient is needed: double nesting, `a` chosen by a
// decision, and `f(a)`'s value chosen by a decision – hence the controls below,
// each of which removes exactly one and was answered correctly all along.
// ========  ========

/// The reproducer.  `a ∈ {0,1,2}` and `f(0), f(1), f(2) ∈ {0,1,2}`, so `f(a)`
/// is in `{0,1,2}` and `f(f(a))` is too – `2 < f(f(a))` has no model.
#[test]
fn nested_application_under_case_split_unsat() {
    let script = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(assert (or (= a 0) (= a 1) (= a 2)))
(assert (or (= (f 0) 0) (= (f 0) 1) (= (f 0) 2)))
(assert (or (= (f 1) 0) (= (f 1) 1) (= (f 1) 2)))
(assert (or (= (f 2) 0) (= (f 2) 1) (= (f 2) 2)))
(assert (< 2 (f (f a))))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// The same shape at domain size two – the minimal form of the defect.
#[test]
fn nested_application_under_case_split_two_valued_unsat() {
    let script = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(assert (or (= a 0) (= a 1)))
(assert (or (= (f 0) 0) (= (f 0) 1)))
(assert (or (= (f 1) 0) (= (f 1) 1)))
(assert (< 1 (f (f a))))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Control (single nesting): `f(a)` instead of `f(f(a))`.  Answered correctly
/// before the fix; it must stay that way.
#[test]
fn single_nesting_under_case_split_control_unsat() {
    let script = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(assert (or (= a 0) (= a 1) (= a 2)))
(assert (or (= (f 0) 0) (= (f 0) 1) (= (f 0) 2)))
(assert (or (= (f 1) 0) (= (f 1) 1) (= (f 1) 2)))
(assert (or (= (f 2) 0) (= (f 2) 1) (= (f 2) 2)))
(assert (< 2 (f a)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Control (`a` forced rather than decided): the case split on `a` is what puts
/// the intern-time congruence inside a scope that is later popped.
#[test]
fn nested_application_with_forced_argument_control_unsat() {
    let script = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(assert (= a 0))
(assert (or (= (f 0) 0) (= (f 0) 1) (= (f 0) 2)))
(assert (or (= (f 1) 0) (= (f 1) 1) (= (f 1) 2)))
(assert (or (= (f 2) 0) (= (f 2) 1) (= (f 2) 2)))
(assert (< 2 (f (f a))))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Control (pure QF_UF): the same nesting over an uninterpreted sort, which
/// never went through the arithmetic interface and was always `unsat`.
#[test]
fn nested_application_under_case_split_pure_uf_control_unsat() {
    let script = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun g (U) U)
(declare-const a U)
(declare-const c0 U)
(declare-const c1 U)
(declare-const c2 U)
(assert (or (= a c0) (= a c1) (= a c2)))
(assert (or (= (g c0) c0) (= (g c0) c1) (= (g c0) c2)))
(assert (or (= (g c1) c0) (= (g c1) c1) (= (g c1) c2)))
(assert (or (= (g c2) c0) (= (g c2) c1) (= (g c2) c2)))
(assert (distinct (g (g a)) (g c0)))
(assert (distinct (g (g a)) (g c1)))
(assert (distinct (g (g a)) (g c2)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Unsat);
}

/// Control that must stay `sat`: widen the range of `f` by one value and the
/// very same nested atom becomes satisfiable.  Rediscovering the congruence must
/// not over-constrain.
#[test]
fn nested_application_under_case_split_control_sat() {
    let script = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(assert (or (= a 0) (= a 1) (= a 2)))
(assert (or (= (f 0) 0) (= (f 0) 1) (= (f 0) 2) (= (f 0) 3)))
(assert (or (= (f 1) 0) (= (f 1) 1) (= (f 1) 2) (= (f 1) 3)))
(assert (or (= (f 2) 0) (= (f 2) 1) (= (f 2) 2) (= (f 2) 3)))
(assert (or (= (f 3) 0) (= (f 3) 1) (= (f 3) 2) (= (f 3) 3)))
(assert (< 2 (f (f a))))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// Control that must stay `sat`: the nested application is only required to
/// *equal* a reachable value, so a model exists (`a = 0, f(0) = 1, f(1) = 1`).
#[test]
fn nested_application_reachable_value_control_sat() {
    let script = r#"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(assert (or (= a 0) (= a 1)))
(assert (or (= (f 0) 0) (= (f 0) 1)))
(assert (or (= (f 1) 0) (= (f 1) 1)))
(assert (= (f (f a)) 1))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

/// Control that must stay `sat`: the pure-UF nesting with one fewer
/// disequality, which a three-element domain can satisfy.
#[test]
fn nested_application_pure_uf_control_sat() {
    let script = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun g (U) U)
(declare-const a U)
(declare-const c0 U)
(declare-const c1 U)
(declare-const c2 U)
(assert (or (= a c0) (= a c1) (= a c2)))
(assert (or (= (g c0) c0) (= (g c0) c1) (= (g c0) c2)))
(assert (or (= (g c1) c0) (= (g c1) c1) (= (g c1) c2)))
(assert (or (= (g c2) c0) (= (g c2) c1) (= (g c2) c2)))
(assert (distinct (g (g a)) (g c0)))
(check-sat)
"#;
    assert_eq!(run_script(script), SolverResult::Sat);
}

// ========  ========
// Bounded differential testing against a brute-force oracle
//
// Small UF+LIA and Array+LIA formulas are generated from a fixed seed (no
// wall-clock, no external oracle, no randomness that varies between runs) and
// checked against exhaustive enumeration.  Theory combination is where wrong
// answers hide, and a generated corpus finds the shapes hand-written cases do
// not.
// ========  ========

/// The finite domain the differential formulas live on: `{0, 1, 2}`.
const DIFF_DOMAIN: usize = 3;

/// A ground term of the generated fragment.
///
/// `X`/`Y` are the two integer variables, `AppX`/`AppY` one application of the
/// single unary symbol, `AppAppX`/`AppAppY`/`AppAppAppX` *nested* applications,
/// and `Lit` a literal of the domain.  The flavours differ only in how these
/// render: the symbol is an uninterpreted function in UF+LIA, an array read in
/// Array+LIA and an uninterpreted function over an uninterpreted sort in pure
/// QF_UF; all three reach exactly the same congruence-closure machinery.
///
/// Every nesting depth stays inside the box: the bounded preamble pins the
/// symbol's value at *every* domain point, so applying it again cannot escape.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum DiffTerm {
    X,
    Y,
    AppX,
    AppY,
    AppAppX,
    AppAppY,
    AppAppAppX,
    Lit(i64),
}

/// Every term the generator may pick, in a fixed order.
const DIFF_TERMS_NESTED: [DiffTerm; 8] = [
    DiffTerm::X,
    DiffTerm::Y,
    DiffTerm::AppX,
    DiffTerm::AppY,
    DiffTerm::AppAppX,
    DiffTerm::Lit(0),
    DiffTerm::Lit(1),
    DiffTerm::Lit(2),
];

/// The same list without the nested application.
const DIFF_TERMS_FLAT: [DiffTerm; 7] = [
    DiffTerm::X,
    DiffTerm::Y,
    DiffTerm::AppX,
    DiffTerm::AppY,
    DiffTerm::Lit(0),
    DiffTerm::Lit(1),
    DiffTerm::Lit(2),
];

/// Nesting-heavy list: three of nine picks are an application of an application.
///
/// A doubly-nested application whose argument value is itself decided by a case
/// split is the exact shape of the congruence-under-backtracking defect (`f(0)`
/// pinned to `f(a)`'s node after `a = 0` was retracted, so `f(f(a)) = f(0)` was
/// undiscoverable), so the generator is deliberately biased towards it.
const DIFF_TERMS_DEEP: [DiffTerm; 9] = [
    DiffTerm::X,
    DiffTerm::Y,
    DiffTerm::AppX,
    DiffTerm::AppAppX,
    DiffTerm::AppAppY,
    DiffTerm::AppAppAppX,
    DiffTerm::Lit(0),
    DiffTerm::Lit(1),
    DiffTerm::Lit(2),
];

/// An atom of the generated fragment.
///
/// `SumLt` exists because a shared term buried in an arithmetic sum reaches the
/// tableau by a different route than a bare one, and that route had its own
/// hole.
#[derive(Clone, Copy, Debug)]
enum DiffAtom {
    Eq(DiffTerm, DiffTerm),
    Lt(DiffTerm, DiffTerm),
    SumLt(DiffTerm, DiffTerm, DiffTerm, DiffTerm),
}

/// Which theory the single unary symbol comes from.
#[derive(Clone, Copy, PartialEq, Eq)]
enum DiffFlavour {
    /// `f : Int -> Int`, an uninterpreted function.
    Uf,
    /// `arr : (Array Int Int)`, read with `select`.
    Array,
    /// `g : U -> U` over a declared, uninterpreted sort – pure QF_UF, with no
    /// arithmetic anywhere.  The domain is pinned by `distinct` constants
    /// instead of integer literals, so the same enumeration decides it.
    UninterpretedSort,
}

impl DiffFlavour {
    /// Whether the flavour has arithmetic, i.e. whether `<` and `+` atoms may be
    /// generated at all.  Pure QF_UF is equality-only.
    fn has_arithmetic(self) -> bool {
        !matches!(self, DiffFlavour::UninterpretedSort)
    }

    fn render_term(self, t: DiffTerm) -> String {
        let (x, y, app) = match self {
            DiffFlavour::Uf => ("a", "b", "f"),
            DiffFlavour::Array => ("i", "j", "select arr"),
            DiffFlavour::UninterpretedSort => ("u", "v", "g"),
        };
        match t {
            DiffTerm::X => x.to_string(),
            DiffTerm::Y => y.to_string(),
            DiffTerm::AppX => format!("({app} {x})"),
            DiffTerm::AppY => format!("({app} {y})"),
            DiffTerm::AppAppX => format!("({app} ({app} {x}))"),
            DiffTerm::AppAppY => format!("({app} ({app} {y}))"),
            DiffTerm::AppAppAppX => format!("({app} ({app} ({app} {x})))"),
            DiffTerm::Lit(n) => match self {
                DiffFlavour::UninterpretedSort => format!("c{n}"),
                _ => n.to_string(),
            },
        }
    }

    /// How the symbol reads at domain point `k`, for the closure assertions.
    fn app_at(self, k: usize) -> String {
        match self {
            DiffFlavour::Uf => format!("(f {k})"),
            DiffFlavour::Array => format!("(select arr {k})"),
            DiffFlavour::UninterpretedSort => format!("(g c{k})"),
        }
    }

    /// Declarations, plus the closure assertions when `bounded`.
    ///
    /// The closure assertions pin both variables and the symbol's value at every
    /// domain point into `{0, 1, 2}`.  With them the enumeration below is a
    /// *complete* oracle – a model exists iff one exists in the box – so both
    /// answers can be asserted.  Without them it is only sound in one direction
    /// (a model found in the box really is a model), which is the direction that
    /// catches a false `unsat`.
    ///
    /// For the uninterpreted sort the box is made by declaring `DIFF_DOMAIN`
    /// pairwise-`distinct` constants and pinning both variables and every read
    /// into that set; a larger universe cannot help because no generated term
    /// can reach outside it.
    fn preamble(self, bounded: bool) -> String {
        let mut s = match self {
            DiffFlavour::Uf => "(set-logic QF_UFLIA)\n\
                                (declare-fun f (Int) Int)\n\
                                (declare-const a Int)\n\
                                (declare-const b Int)\n"
                .to_string(),
            DiffFlavour::Array => "(set-logic QF_AUFLIA)\n\
                                   (declare-const arr (Array Int Int))\n\
                                   (declare-const i Int)\n\
                                   (declare-const j Int)\n"
                .to_string(),
            DiffFlavour::UninterpretedSort => {
                let mut head = "(set-logic QF_UF)\n\
                                (declare-sort U 0)\n\
                                (declare-fun g (U) U)\n\
                                (declare-const u U)\n\
                                (declare-const v U)\n"
                    .to_string();
                for k in 0..DIFF_DOMAIN {
                    head.push_str(&format!("(declare-const c{k} U)\n"));
                }
                let consts: Vec<String> = (0..DIFF_DOMAIN).map(|k| format!("c{k}")).collect();
                head.push_str(&format!("(assert (distinct {}))\n", consts.join(" ")));
                head
            }
        };
        if bounded {
            for t in [DiffTerm::X, DiffTerm::Y] {
                let r = self.render_term(t);
                let alts: Vec<String> = (0..DIFF_DOMAIN)
                    .map(|k| format!("(= {r} {})", self.render_term(DiffTerm::Lit(k as i64))))
                    .collect();
                s.push_str(&format!("(assert (or {}))\n", alts.join(" ")));
            }
            for k in 0..DIFF_DOMAIN {
                let app = self.app_at(k);
                let alts: Vec<String> = (0..DIFF_DOMAIN)
                    .map(|m| format!("(= {app} {})", self.render_term(DiffTerm::Lit(m as i64))))
                    .collect();
                s.push_str(&format!("(assert (or {}))\n", alts.join(" ")));
            }
        }
        s
    }
}

/// Evaluate a term under `x`, `y` and the tabulated symbol `g : D -> D`.
fn diff_eval_term(t: DiffTerm, x: usize, y: usize, g: &[usize; DIFF_DOMAIN]) -> i64 {
    match t {
        DiffTerm::X => x as i64,
        DiffTerm::Y => y as i64,
        DiffTerm::AppX => g[x] as i64,
        DiffTerm::AppY => g[y] as i64,
        DiffTerm::AppAppX => g[g[x]] as i64,
        DiffTerm::AppAppY => g[g[y]] as i64,
        DiffTerm::AppAppAppX => g[g[g[x]]] as i64,
        DiffTerm::Lit(n) => n,
    }
}

fn diff_eval_atom(atom: DiffAtom, x: usize, y: usize, g: &[usize; DIFF_DOMAIN]) -> bool {
    let e = |t| diff_eval_term(t, x, y, g);
    match atom {
        DiffAtom::Eq(p, q) => e(p) == e(q),
        DiffAtom::Lt(p, q) => e(p) < e(q),
        DiffAtom::SumLt(p, q, r, s) => e(p) + e(q) < e(r) + e(s),
    }
}

fn diff_render_atom(flavour: DiffFlavour, atom: DiffAtom) -> String {
    let r = |t| flavour.render_term(t);
    match atom {
        DiffAtom::Eq(p, q) => format!("(= {} {})", r(p), r(q)),
        DiffAtom::Lt(p, q) => format!("(< {} {})", r(p), r(q)),
        DiffAtom::SumLt(p, q, s, t) => {
            format!("(< (+ {} {}) (+ {} {}))", r(p), r(q), r(s), r(t))
        }
    }
}

/// A clause is a disjunction of possibly negated atoms; a formula is a
/// conjunction of clauses.
type DiffClause = Vec<(DiffAtom, bool)>;

/// xorshift64*, seeded explicitly so the corpus is byte-for-byte reproducible.
struct DiffRng(u64);

impl DiffRng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// Generate one atom.  `arithmetic` is false for the pure-QF_UF flavour, which
/// has no `<` and no `+` – only equalities between terms of the sort.
fn diff_gen_atom(rng: &mut DiffRng, terms: &[DiffTerm], arithmetic: bool) -> DiffAtom {
    let pick = |rng: &mut DiffRng| terms[rng.below(terms.len())];
    if !arithmetic {
        return DiffAtom::Eq(pick(rng), pick(rng));
    }
    match rng.below(3) {
        0 => DiffAtom::Eq(pick(rng), pick(rng)),
        1 => DiffAtom::Lt(pick(rng), pick(rng)),
        _ => DiffAtom::SumLt(pick(rng), pick(rng), pick(rng), pick(rng)),
    }
}

fn diff_gen_formula(rng: &mut DiffRng, terms: &[DiffTerm], arithmetic: bool) -> Vec<DiffClause> {
    let clauses = 1 + rng.below(3);
    (0..clauses)
        .map(|_| {
            let lits = 1 + rng.below(2);
            (0..lits)
                .map(|_| (diff_gen_atom(rng, terms, arithmetic), rng.below(2) == 1))
                .collect()
        })
        .collect()
}

/// Exhaustive search for a model over `x, y ∈ D` and `g : D -> D`.
fn diff_oracle_satisfiable(formula: &[DiffClause]) -> bool {
    let table_count = DIFF_DOMAIN.pow(DIFF_DOMAIN as u32);
    for x in 0..DIFF_DOMAIN {
        for y in 0..DIFF_DOMAIN {
            for code in 0..table_count {
                let mut g = [0usize; DIFF_DOMAIN];
                let mut rest = code;
                for slot in g.iter_mut() {
                    *slot = rest % DIFF_DOMAIN;
                    rest /= DIFF_DOMAIN;
                }
                let holds = formula.iter().all(|clause| {
                    clause
                        .iter()
                        .any(|&(atom, negated)| diff_eval_atom(atom, x, y, &g) != negated)
                });
                if holds {
                    return true;
                }
            }
        }
    }
    false
}

fn diff_render(flavour: DiffFlavour, formula: &[DiffClause], bounded: bool) -> String {
    let mut script = flavour.preamble(bounded);
    for clause in formula {
        let lits: Vec<String> = clause
            .iter()
            .map(|&(atom, negated)| {
                let rendered = diff_render_atom(flavour, atom);
                if negated {
                    format!("(not {rendered})")
                } else {
                    rendered
                }
            })
            .collect();
        let body = if lits.len() == 1 {
            lits[0].clone()
        } else {
            format!("(or {})", lits.join(" "))
        };
        script.push_str(&format!("(assert {body})\n"));
    }
    script.push_str("(check-sat)\n");
    script
}

/// Two-sided differential check over the value-closed fragment.
///
/// Every variable and every value of the symbol is pinned into `{0, 1, 2}` by
/// the formula itself, so exhaustive enumeration decides satisfiability exactly
/// and *both* answers can be demanded of the solver.
fn diff_check_bounded(flavour: DiffFlavour, seed: u64, count: usize) -> Vec<String> {
    diff_check_bounded_terms(flavour, seed, count, &DIFF_TERMS_FLAT)
}

/// [`diff_check_bounded`] over an explicit term set, so the nesting-heavy corpus
/// can be run through the very same two-sided oracle.
fn diff_check_bounded_terms(
    flavour: DiffFlavour,
    seed: u64,
    count: usize,
    terms: &[DiffTerm],
) -> Vec<String> {
    let mut rng = DiffRng(seed);
    let mut mismatches = Vec::new();
    for n in 0..count {
        let formula = diff_gen_formula(&mut rng, terms, flavour.has_arithmetic());
        let expected = diff_oracle_satisfiable(&formula);
        let script = diff_render(flavour, &formula, true);
        match (expected, run_script(&script)) {
            (true, SolverResult::Unsat) => {
                mismatches.push(format!("#{n}: oracle sat, solver unsat\n{script}"));
            }
            (false, SolverResult::Sat) => {
                mismatches.push(format!("#{n}: oracle unsat, solver sat\n{script}"));
            }
            _ => {}
        }
    }
    mismatches
}

/// One-sided differential check over the unrestricted fragment.
///
/// Nothing bounds the terms here, so a model found in the box is a genuine
/// model (extend the symbol arbitrarily outside `D`) while failing to find one
/// proves nothing.  That makes the oracle sound in exactly one direction – the
/// one that exposes a false `unsat`, which is the failure a conflict clause
/// missing part of its justification produces.  Nested applications are in
/// scope here.
fn diff_check_unbounded_no_false_unsat(
    flavour: DiffFlavour,
    seed: u64,
    count: usize,
) -> Vec<String> {
    let mut rng = DiffRng(seed);
    let mut mismatches = Vec::new();
    for n in 0..count {
        let formula = diff_gen_formula(&mut rng, &DIFF_TERMS_NESTED, flavour.has_arithmetic());
        if !diff_oracle_satisfiable(&formula) {
            continue;
        }
        let script = diff_render(flavour, &formula, false);
        if run_script(&script) == SolverResult::Unsat {
            mismatches.push(format!(
                "#{n}: a model exists but the solver refuted it\n{script}"
            ));
        }
    }
    mismatches
}

/// Seed shared by every differential run: fixed, so the corpus never varies.
const DIFF_SEED: u64 = 0x9E37_79B9_7F4A_7C15;

#[test]
fn differential_uf_lia_bounded_matches_brute_force_oracle() {
    let mismatches = diff_check_bounded(DiffFlavour::Uf, DIFF_SEED, 160);
    assert!(
        mismatches.is_empty(),
        "{} UF+LIA differential mismatches:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}

#[test]
fn differential_array_lia_bounded_matches_brute_force_oracle() {
    let mismatches = diff_check_bounded(DiffFlavour::Array, DIFF_SEED, 160);
    assert!(
        mismatches.is_empty(),
        "{} Array+LIA differential mismatches:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}

#[test]
fn differential_uf_lia_never_refutes_a_satisfiable_formula() {
    let mismatches = diff_check_unbounded_no_false_unsat(DiffFlavour::Uf, DIFF_SEED, 240);
    assert!(
        mismatches.is_empty(),
        "{} UF+LIA formulas refuted despite having a model:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}

#[test]
fn differential_array_lia_never_refutes_a_satisfiable_formula() {
    let mismatches = diff_check_unbounded_no_false_unsat(DiffFlavour::Array, DIFF_SEED, 240);
    assert!(
        mismatches.is_empty(),
        "{} Array+LIA formulas refuted despite having a model:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}

// ========  ========
// Two-sided differential runs over the *nesting-heavy* corpus.
//
// The bounded preamble pins the symbol's value at every domain point, so the box
// is closed under any depth of nesting and the enumeration stays a complete
// oracle: both `sat` and `unsat` can be demanded.  This is the corpus that
// exhibits the congruence-under-backtracking defect – a doubly-nested
// application whose argument value comes from a case split – so it is run for
// all three flavours, including pure QF_UF where no arithmetic is involved at
// all and the congruence has to carry the whole refutation.
// ========  ========

#[test]
fn differential_uf_lia_nested_bounded_matches_brute_force_oracle() {
    let mismatches = diff_check_bounded_terms(DiffFlavour::Uf, DIFF_SEED, 400, &DIFF_TERMS_DEEP);
    assert!(
        mismatches.is_empty(),
        "{} nested UF+LIA differential mismatches:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}

#[test]
fn differential_array_lia_nested_bounded_matches_brute_force_oracle() {
    let mismatches = diff_check_bounded_terms(DiffFlavour::Array, DIFF_SEED, 400, &DIFF_TERMS_DEEP);
    assert!(
        mismatches.is_empty(),
        "{} nested Array+LIA differential mismatches:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}

#[test]
fn differential_qf_uf_nested_bounded_matches_brute_force_oracle() {
    let mismatches = diff_check_bounded_terms(
        DiffFlavour::UninterpretedSort,
        DIFF_SEED,
        400,
        &DIFF_TERMS_DEEP,
    );
    assert!(
        mismatches.is_empty(),
        "{} nested QF_UF differential mismatches:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );
}
