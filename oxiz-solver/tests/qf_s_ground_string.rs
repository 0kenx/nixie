//! End-to-end QF_S regression tests for the ground string decision procedure.
//!
//! Each test runs a complete SMT-LIB2 script through [`Context::execute_script`]
//! (the same path the CLI uses) and asserts the `(check-sat)` verdict matches
//! Z3's answer. The seven satisfiable cases exercise the model-construction and
//! verification wiring added for the `qf_s` benchmark family; the three
//! unsatisfiable cases pin the definite-conflict detectors so the new SAT path
//! never masks a genuine refutation.
//!
//! Every satisfiable answer here is backed by a concrete model that the ground
//! solver verified against all assertions before answering `sat`, so these are
//! sound certificates — not free-Boolean guesses.

use oxiz_solver::Context;

/// Run a script and return the single `(check-sat)` verdict it produces.
fn check_sat_verdict(script: &str) -> String {
    let mut ctx = Context::new();
    let output = ctx.execute_script(script).expect("script executes");
    output
        .into_iter()
        .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .expect("script contained a (check-sat)")
}

// ── Satisfiable: basic concatenation with pinned operands ──────────────
#[test]
fn string_01_basic_concat_pinned() {
    let verdict = check_sat_verdict(
        r#"(set-logic QF_S)
           (declare-const x String)
           (declare-const y String)
           (declare-const z String)
           (assert (= (str.++ x y) "hello"))
           (assert (= x "hel"))
           (assert (= y "lo"))
           (check-sat)"#,
    );
    assert_eq!(verdict, "sat");
}

// ── Unsatisfiable: chain concatenation length conflict ─────────────────
#[test]
fn string_02_chain_concat_length_conflict() {
    let verdict = check_sat_verdict(
        r#"(set-logic QF_S)
           (declare-const a String)
           (declare-const b String)
           (declare-const c String)
           (assert (= (str.++ a b c) "abc"))
           (assert (= (str.len a) 2))
           (assert (= (str.len b) 2))
           (assert (= (str.len c) 1))
           (check-sat)"#,
    );
    assert_eq!(verdict, "unsat");
}

// ── Satisfiable: split a constant by known operand lengths ─────────────
#[test]
fn string_03_length_split() {
    let verdict = check_sat_verdict(
        r#"(set-logic QF_S)
           (declare-const s String)
           (declare-const t String)
           (assert (= (str.len s) 5))
           (assert (= (str.len t) 3))
           (assert (= (str.++ s t) "worldfoo"))
           (check-sat)"#,
    );
    assert_eq!(verdict, "sat");
}

// ── Unsatisfiable: contradictory length vs. concrete value ─────────────
#[test]
fn string_04_length_value_conflict() {
    let verdict = check_sat_verdict(
        r#"(set-logic QF_S)
           (declare-const x String)
           (assert (= (str.len x) 10))
           (assert (= x "short"))
           (check-sat)"#,
    );
    assert_eq!(verdict, "unsat");
}

// ── Satisfiable: contains + prefix + length lower bound ────────────────
#[test]
fn string_05_contains_prefix_length() {
    let verdict = check_sat_verdict(
        r#"(set-logic QF_S)
           (declare-const s String)
           (assert (str.contains s "test"))
           (assert (str.prefixof "my" s))
           (assert (>= (str.len s) 6))
           (check-sat)"#,
    );
    assert_eq!(verdict, "sat");
}

// ── Satisfiable: suffix + contains + length upper bound ────────────────
#[test]
fn string_06_suffix_contains_length() {
    let verdict = check_sat_verdict(
        r#"(set-logic QF_S)
           (declare-const text String)
           (assert (str.suffixof ".txt" text))
           (assert (str.contains text "file"))
           (assert (<= (str.len text) 15))
           (check-sat)"#,
    );
    assert_eq!(verdict, "sat");
}

// ── Satisfiable: replace on a pinned constant string ───────────────────
#[test]
fn string_07_replace_pinned() {
    let verdict = check_sat_verdict(
        r#"(set-logic QF_S)
           (declare-const input String)
           (declare-const output String)
           (assert (= output (str.replace input "old" "new")))
           (assert (= input "the old way"))
           (assert (= output "the new way"))
           (check-sat)"#,
    );
    assert_eq!(verdict, "sat");
}

// ── Unsatisfiable: replace_all changes the string ──────────────────────
#[test]
fn string_08_replace_all_conflict() {
    let verdict = check_sat_verdict(
        r#"(set-logic QF_S)
           (declare-const s String)
           (declare-const result String)
           (assert (= result (str.replace_all s "a" "b")))
           (assert (= s "banana"))
           (assert (= result "banana"))
           (check-sat)"#,
    );
    assert_eq!(verdict, "unsat");
}

// ── Satisfiable: regex ".*digit-digit-digit" + prefix + exact length ───
#[test]
fn string_09_regex_digits_prefix_length() {
    let verdict = check_sat_verdict(
        r#"(set-logic QF_S)
           (declare-const phone String)
           (assert (str.in_re phone
               (re.++
                   (re.* re.allchar)
                   (re.++ (re.range "0" "9")
                          (re.++ (re.range "0" "9")
                                 (re.range "0" "9"))))))
           (assert (= (str.len phone) 10))
           (assert (str.prefixof "call" phone))
           (check-sat)"#,
    );
    assert_eq!(verdict, "sat");
}

// ── Satisfiable: lowercase regex + length range + contains ─────────────
#[test]
fn string_10_regex_lowercase_range_contains() {
    let verdict = check_sat_verdict(
        r#"(set-logic QF_S)
           (declare-const word String)
           (assert (str.in_re word
               (re.++
                   (re.range "a" "z")
                   (re.++
                       (re.range "a" "z")
                       (re.++
                           (re.range "a" "z")
                           (re.* (re.range "a" "z")))))))
           (assert (>= (str.len word) 3))
           (assert (<= (str.len word) 8))
           (assert (str.contains word "test"))
           (check-sat)"#,
    );
    assert_eq!(verdict, "sat");
}

// ── Soundness guard: a genuine contradiction over string atoms must not
//    be masked into a spurious `sat` by the new model-construction path. ─
#[test]
fn contains_contradiction_is_not_sat() {
    let verdict = check_sat_verdict(
        r#"(set-logic QF_S)
           (declare-const s String)
           (assert (= s "abc"))
           (assert (str.contains s "xyz"))
           (check-sat)"#,
    );
    assert_ne!(verdict, "sat");
}

// ── Soundness guard: an unsatisfiable regex intersection must not be
//    reported `sat` (digit AND lowercase letter is empty). ──────────────
#[test]
fn empty_regex_intersection_is_not_sat() {
    let verdict = check_sat_verdict(
        r#"(set-logic QF_S)
           (declare-const c String)
           (assert (str.in_re c (re.range "0" "9")))
           (assert (str.in_re c (re.range "a" "z")))
           (assert (= (str.len c) 1))
           (check-sat)"#,
    );
    assert_ne!(verdict, "sat");
}
