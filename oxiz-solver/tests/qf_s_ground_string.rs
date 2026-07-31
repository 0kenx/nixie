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

/// Run a script and return every response line it produces.
fn script_output(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script).expect("script executes")
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

// ══════════════════════════════════════════════════════════════════════
// Issue #14 — trivially unsatisfiable string equalities reported `sat`,
// and string values missing from `(get-value ...)` / `(get-model)`.
// Every case goes through `Context::execute_script`, the entry point the
// reporter used.
// ══════════════════════════════════════════════════════════════════════

/// A term forced to two different string constants is refuted by constant
/// propagation alone — directly (`s = "x" ∧ s = "y"`), through an equality
/// chain, or between two bare literals.
#[test]
fn test_issue_14_string_eq_conflict_unsat() {
    assert_eq!(
        check_sat_verdict(
            r#"(set-logic QF_S)
               (declare-const s String)
               (assert (= s "x"))
               (assert (= s "y"))
               (check-sat)"#,
        ),
        "unsat"
    );

    // Same conflict reached through a chain of equalities.
    assert_eq!(
        check_sat_verdict(
            r#"(set-logic QF_S)
               (declare-const a String)
               (declare-const b String)
               (assert (= a "p"))
               (assert (= b "q"))
               (assert (= a b))
               (check-sat)"#,
        ),
        "unsat"
    );

    // Two distinct literals equated directly.
    assert_eq!(
        check_sat_verdict(
            r#"(set-logic QF_S)
               (assert (= "x" "y"))
               (check-sat)"#,
        ),
        "unsat"
    );
}

/// A concatenation against a constant target is refuted when a pinned leading
/// or trailing operand is not a prefix / suffix of that target, without ever
/// guessing the unknown operand.
#[test]
fn test_issue_14_concat_prefix_conflict_unsat() {
    // "a" ++ s = "bcd" requires "bcd" to start with "a".
    assert_eq!(
        check_sat_verdict(
            r#"(set-logic QF_S)
               (declare-const s String)
               (assert (= (str.++ "a" s) "bcd"))
               (check-sat)"#,
        ),
        "unsat"
    );

    // s ++ "z" = "abc" requires "abc" to end with "z".
    assert_eq!(
        check_sat_verdict(
            r#"(set-logic QF_S)
               (declare-const s String)
               (assert (= (str.++ s "z") "abc"))
               (check-sat)"#,
        ),
        "unsat"
    );

    // The known prefix and suffix together are longer than the target.
    assert_eq!(
        check_sat_verdict(
            r#"(set-logic QF_S)
               (declare-const s String)
               (assert (= (str.++ "abc" (str.++ s "def")) "abcdef!"))
               (check-sat)"#,
        ),
        "unsat"
    );
}

/// `(get-value (s))` reports the string a satisfiable formula forces, instead
/// of echoing the constant back unevaluated.
#[test]
fn test_issue_14_get_value_string() {
    // Plain equality (decided by the CDCL(T) path — no string-theory atom).
    let output = script_output(
        r#"(set-logic QF_S)
           (declare-const s String)
           (assert (= s "353"))
           (check-sat)
           (get-value (s))"#,
    );
    assert_eq!(output, vec!["sat".to_string(), "((s \"353\"))".to_string()]);

    // Concatenation (decided by the ground string model construction path).
    let output = script_output(
        r#"(set-logic QF_S)
           (declare-const s String)
           (assert (= (str.++ "* " s) "* 353"))
           (check-sat)
           (get-value (s))"#,
    );
    assert_eq!(output, vec!["sat".to_string(), "((s \"353\"))".to_string()]);
}

/// `(get-model)` reports a `String`-sorted constant with sort `String` and a
/// real string value.
#[test]
fn test_issue_14_get_model_string_sort() {
    let output = script_output(
        r#"(set-logic QF_S)
           (declare-const s String)
           (assert (= (str.++ "* " s) "* 353"))
           (check-sat)
           (get-model)"#,
    );
    assert_eq!(output.first().map(String::as_str), Some("sat"));
    let model = output.get(1).expect("(get-model) produced a response");
    assert!(
        model.contains("(define-fun s () String \"353\")"),
        "unexpected model: {model}"
    );

    // A string constant left unconstrained still gets a valid ground value of
    // its own sort, never the invalid `?` placeholder or a wrong sort.
    let output = script_output(
        r#"(set-logic QF_S)
           (declare-const s String)
           (declare-const t String)
           (declare-const p Bool)
           (assert (= s "a"))
           (assert p)
           (check-sat)
           (get-model)"#,
    );
    let model = output.get(1).expect("(get-model) produced a response");
    assert!(
        model.contains("(define-fun s () String \"a\")"),
        "unexpected model: {model}"
    );
    assert!(
        model.contains("(define-fun t () String \"\")"),
        "unexpected model: {model}"
    );
    assert!(
        !model.contains('?'),
        "invalid placeholder in model: {model}"
    );
}

/// Soundness guard for the conflict detectors extended above: a string fact
/// that only holds inside a disjunct or under a negation is *conditional*, and
/// must never drive a refutation.
#[test]
fn test_issue_14_conditional_string_facts_not_unsat() {
    // Satisfiable with x = "short" (the second disjunct).
    assert_ne!(
        check_sat_verdict(
            r#"(set-logic QF_S)
               (declare-const x String)
               (assert (or (= (str.len x) 10) (= x "short")))
               (check-sat)"#,
        ),
        "unsat"
    );

    // Satisfiable with s = "x" (or s = "y").
    assert_ne!(
        check_sat_verdict(
            r#"(set-logic QF_S)
               (declare-const s String)
               (assert (or (= s "x") (= s "y")))
               (check-sat)"#,
        ),
        "unsat"
    );

    // x = "short" has length 5, so `len(x) != 10` is satisfied, not violated.
    assert_ne!(
        check_sat_verdict(
            r#"(set-logic QF_S)
               (declare-const x String)
               (assert (= x "short"))
               (assert (not (= (str.len x) 10)))
               (check-sat)"#,
        ),
        "unsat"
    );
}

// ══════════════════════════════════════════════════════════════════════
// Issue #23 — an implication with a provably false premise, and the two
// layers it is built from.  The premise `(= (str.++ (str.substr "aba" 3 1)
// "bb") "")` is false because the out-of-range substring is `""`, so the
// implication is vacuously true for every `s0`.
// ══════════════════════════════════════════════════════════════════════

/// The verbatim reproducer: `sat`, matching Z3.
///
/// Nothing may harvest the antecedent's concat equation as an unconditional
/// fact — doing so refutes `(= (str.++ … "bb") "")`, which is indeed false, and
/// turns the vacuously true implication into a spurious `unsat`.
#[test]
fn test_issue_23_false_premise_implication() {
    assert_eq!(
        check_sat_verdict(
            r#"(set-logic QF_S)
               (declare-const s0 String)
               (assert (=> (= (str.++ (str.substr "aba" 3 1) "bb") "")
                           (distinct "b" (str.++ s0 "b"))))
               (check-sat)"#,
        ),
        "sat"
    );
}

/// `(str.substr "aba" 3 1)` starts past the end of a length-3 string, so
/// SMT-LIB gives it the empty string.  `(get-value ...)` pins the actual value,
/// not merely that `""` is consistent with it.
#[test]
fn test_issue_23_substr_out_of_range() {
    assert_eq!(
        check_sat_verdict(
            r#"(set-logic QF_S)
               (assert (= (str.substr "aba" 3 1) ""))
               (check-sat)"#,
        ),
        "sat"
    );

    let output = script_output(
        r#"(set-logic QF_S)
           (declare-const s String)
           (assert (= s (str.substr "aba" 3 1)))
           (check-sat)
           (get-value (s))"#,
    );
    assert_eq!(output, vec!["sat".to_string(), "((s \"\"))".to_string()]);

    // The whole antecedent is then `(= "bb" "")`, which is genuinely false.
    assert_eq!(
        check_sat_verdict(
            r#"(set-logic QF_S)
               (assert (= (str.++ (str.substr "aba" 3 1) "bb") ""))
               (check-sat)"#,
        ),
        "unsat"
    );
}

/// The implication's consequent is satisfiable on its own: any `s0` other than
/// `""` makes `(str.++ s0 "b")` differ from `"b"`.
///
/// The model builder pins a variable only from an equality, a length bound or a
/// regular constraint; `s0` has none of those, so it defaults to `""` — the one
/// value the disequality forbids.  The verdict must still be `sat`, with a
/// witness that really satisfies the disequality.
#[test]
fn test_issue_23_distinct_concat_sat() {
    let output = script_output(
        r#"(set-logic QF_S)
           (declare-const s0 String)
           (assert (distinct "b" (str.++ s0 "b")))
           (check-sat)
           (get-value (s0))"#,
    );
    assert_eq!(output.first().map(String::as_str), Some("sat"));
    let value = output.get(1).expect("(get-value) produced a response");
    assert!(
        !value.contains("(s0 \"\")"),
        "witness must not be the empty string: {value}"
    );

    // A bare disequality against a constant, and one between two concatenations
    // over two independently free variables.
    assert_eq!(
        check_sat_verdict(
            r#"(set-logic QF_S)
               (declare-const s0 String)
               (assert (distinct s0 ""))
               (check-sat)"#,
        ),
        "sat"
    );
    assert_eq!(
        check_sat_verdict(
            r#"(set-logic QF_S)
               (declare-const a String)
               (declare-const b String)
               (assert (distinct (str.++ a "x") (str.++ b "x")))
               (check-sat)"#,
        ),
        "sat"
    );
}

// ══════════════════════════════════════════════════════════════════════
// Ground refutation — the other half of the ground string procedure.
//
// A fully ground string formula has no variables, so it is decidable: it
// is either `sat` or `unsat`, never `unknown`.  oxiz could already
// *evaluate* every operator (that is how the `sat` direction is
// certified) but had no path from "this assertion evaluates to false" to
// `unsat`, so every ground refutation degraded to `unknown` — the gap
// left open when issue #23 was fixed.
//
// Each operator below is tested in **both polarities**: the true ground
// fact must be `sat`, and its negation must be `unsat`.  The SMT-LIB rule
// each case pins is named in the comment; several are counter-intuitive.
// ══════════════════════════════════════════════════════════════════════

/// Assert `formula`, then assert its negation, and check both verdicts.
/// Every `formula` passed here is a *true* ground fact.
fn assert_ground_fact(formula: &str) {
    let positive = format!("(set-logic QF_S)\n(assert {formula})\n(check-sat)");
    let negative = format!("(set-logic QF_S)\n(assert (not {formula}))\n(check-sat)");
    assert_eq!(
        check_sat_verdict(&positive),
        "sat",
        "true ground fact must be sat: {formula}"
    );
    assert_eq!(
        check_sat_verdict(&negative),
        "unsat",
        "negation of a true ground fact must be unsat: {formula}"
    );
}

/// `str.substr s m n`: `min(n, |s| - m)` characters from `m` when
/// `0 <= m < |s|` and `n > 0`; the **empty string** in every other case —
/// `m < 0`, `m >= |s|` (issue #23's shape) and `n <= 0` alike.
#[test]
fn test_ground_substr_out_of_range_negation_unsat() {
    // The verbatim reporter formula: `(str.substr "aba" 3 1)` starts at
    // index 3 of a length-3 string, so it is `""` and the negation is unsat.
    assert_eq!(
        check_sat_verdict(
            r#"(set-logic QF_S)
               (assert (not (= (str.substr "aba" 3 1) "")))
               (check-sat)"#,
        ),
        "unsat"
    );

    assert_ground_fact(r#"(= (str.substr "abcde" 1 3) "bcd")"#); // in range
    assert_ground_fact(r#"(= (str.substr "abcde" 3 99) "de")"#); // length past end
    assert_ground_fact(r#"(= (str.substr "aba" 3 1) "")"#); // start == |s|
    assert_ground_fact(r#"(= (str.substr "aba" 7 1) "")"#); // start > |s|
    assert_ground_fact(r#"(= (str.substr "abc" (- 1) 2) "")"#); // negative start
    assert_ground_fact(r#"(= (str.substr "abc" 1 (- 2)) "")"#); // negative length
    assert_ground_fact(r#"(= (str.substr "abc" 1 0) "")"#); // zero length
    assert_ground_fact(r#"(= (str.substr "" 0 1) "")"#); // empty source
}

/// A length of `i64::MAX` used to overflow the `start + length` clamp and
/// abort the process; an index too large for `i64` is simply out of range.
#[test]
fn test_ground_substr_extreme_indices() {
    assert_ground_fact(r#"(= (str.substr "abc" 1 9223372036854775807) "bc")"#);
    assert_ground_fact(r#"(= (str.substr "abc" 92233720368547758070 1) "")"#);
    assert_ground_fact(r#"(= (str.substr "abc" (- 92233720368547758070) 1) "")"#);
}

/// `str.++` folds, and `str.len` counts code points.
#[test]
fn test_ground_concat_and_len() {
    assert_ground_fact(r#"(= (str.++ "ab" "cd") "abcd")"#);
    assert_ground_fact(r#"(= (str.++ "a" "" "b") "ab")"#);
    assert_ground_fact(r#"(= (str.len "hello") 5)"#);
    assert_ground_fact(r#"(= (str.len "") 0)"#);
    assert_ground_fact(r#"(= (str.len (str.++ "ab" "cde")) 5)"#);
}

/// `str.at s i` is `(str.substr s i 1)`, so an index below `0` or at/past
/// the end yields `""` rather than being undefined.
#[test]
fn test_ground_at_out_of_range() {
    assert_ground_fact(r#"(= (str.at "abc" 1) "b")"#);
    assert_ground_fact(r#"(= (str.at "abc" 3) "")"#);
    assert_ground_fact(r#"(= (str.at "abc" (- 1)) "")"#);
}

/// `str.indexof s t m`: the smallest `n >= m` with `t` occurring at `n`,
/// provided `0 <= m <= |s|`; `-1` otherwise.  The empty needle occurs at
/// every position, so the answer is `m` itself — including `m = |s|` —
/// while `m = |s| + 1` is out of range and gives `-1`.
#[test]
fn test_ground_indexof_not_found() {
    assert_ground_fact(r#"(= (str.indexof "abc" "z" 0) (- 1))"#); // absent needle
    assert_ground_fact(r#"(= (str.indexof "ab" "abc" 0) (- 1))"#); // needle longer than haystack
    assert_ground_fact(r#"(= (str.indexof "abc" "a" (- 1)) (- 1))"#); // negative offset
    assert_ground_fact(r#"(= (str.indexof "abc" "" 4) (- 1))"#); // offset past |s|
}

/// The in-range half of `str.indexof`, including the empty-needle rule.
#[test]
fn test_ground_indexof_found() {
    assert_ground_fact(r#"(= (str.indexof "abcabc" "abc" 0) 0)"#);
    assert_ground_fact(r#"(= (str.indexof "abcabc" "abc" 1) 3)"#);
    assert_ground_fact(r#"(= (str.indexof "abc" "" 2) 2)"#); // empty needle at offset
    assert_ground_fact(r#"(= (str.indexof "abc" "" 3) 3)"#); // empty needle at |s|
}

/// `str.contains` / `str.prefixof` / `str.suffixof`; the empty word is a
/// substring, a prefix and a suffix of every string.
#[test]
fn test_ground_contains_prefixof_suffixof() {
    assert_ground_fact(r#"(str.contains "hello" "ell")"#);
    assert_ground_fact(r#"(not (str.contains "hello" "xyz"))"#);
    assert_ground_fact(r#"(str.contains "hello" "")"#);
    assert_ground_fact(r#"(str.prefixof "he" "hello")"#);
    assert_ground_fact(r#"(not (str.prefixof "lo" "hello"))"#);
    assert_ground_fact(r#"(str.prefixof "" "hello")"#);
    assert_ground_fact(r#"(str.suffixof "lo" "hello")"#);
    assert_ground_fact(r#"(not (str.suffixof "he" "hello"))"#);
}

/// `str.replace` rewrites the **leftmost** occurrence only and leaves the
/// string alone when the pattern is absent.  The empty pattern is the
/// asymmetric case: it occurs at position 0, so `str.replace` yields
/// `t' ++ s`, whereas `str.replace_all` is defined to return `s` unchanged.
#[test]
fn test_ground_replace_and_replace_all() {
    assert_ground_fact(r#"(= (str.replace "aaa" "a" "b") "baa")"#);
    assert_ground_fact(r#"(= (str.replace "abc" "z" "y") "abc")"#);
    assert_ground_fact(r#"(= (str.replace "abc" "" "X") "Xabc")"#);
    assert_ground_fact(r#"(= (str.replace_all "aaa" "a" "b") "bbb")"#);
    assert_ground_fact(r#"(= (str.replace_all "abc" "" "X") "abc")"#);
    assert_ground_fact(r#"(= (str.replace_all "abc" "z" "y") "abc")"#);
}

/// `str.to_int` is `-1` for anything that is not a non-empty word of
/// digits — `""`, `"12a"` and even `"-7"` (the sign is not a digit) — while
/// leading zeros are allowed.  `str.from_int` is `""` for negatives, has no
/// leading zeros, and maps `0` to `"0"`.
#[test]
fn test_ground_to_int_and_from_int() {
    assert_ground_fact(r#"(= (str.to_int "42") 42)"#);
    assert_ground_fact(r#"(= (str.to_int "0042") 42)"#);
    assert_ground_fact(r#"(= (str.to_int "") (- 1))"#);
    assert_ground_fact(r#"(= (str.to_int "12a") (- 1))"#);
    assert_ground_fact(r#"(= (str.to_int "-7") (- 1))"#);
    assert_ground_fact(r#"(= (str.from_int 42) "42")"#);
    assert_ground_fact(r#"(= (str.from_int 0) "0")"#);
    assert_ground_fact(r#"(= (str.from_int (- 3)) "")"#);
    assert_ground_fact(r#"(= (int.to.str 7) "7")"#); // legacy spelling
}

/// Ground `str.in_re` membership over the regex sublanguage the project
/// implements.
#[test]
fn test_ground_in_re_membership() {
    assert_ground_fact(r#"(str.in_re "abc" (str.to_re "abc"))"#);
    assert_ground_fact(r#"(not (str.in_re "abd" (str.to_re "abc")))"#);
    assert_ground_fact(r#"(str.in_re "aaa" (re.* (str.to_re "a")))"#);
    assert_ground_fact(r#"(str.in_re "5" (re.range "0" "9"))"#);
    assert_ground_fact(r#"(str.in_re "b" (re.union (str.to_re "a") (str.to_re "b")))"#);
    assert_ground_fact(r#"(str.in_re "ab" (re.++ (str.to_re "a") (re.+ (str.to_re "b"))))"#);
    assert_ground_fact(r#"(not (str.in_re "a" re.none))"#);
    assert_ground_fact(r#"(str.in_re "anything" re.all)"#);
}

/// Operators composed with each other still fold to a single value.
#[test]
fn test_ground_nested_operator_composition() {
    assert_ground_fact(r#"(= (str.len (str.substr "abcde" 1 3)) 3)"#);
    assert_ground_fact(r#"(= (str.substr "hello" (str.indexof "hello" "ll" 0) 2) "ll")"#);
    assert_ground_fact(r#"(= (str.to_int (str.from_int 15)) 15)"#);
    assert_ground_fact(r#"(str.contains (str.replace "foobar" "bar" "baz") "baz")"#);
}

/// `str.<` / `str.<=`: the lexicographic order induced by the **code-point**
/// order on characters, both operators `:chainable`.  A proper prefix is
/// strictly smaller, `""` is the minimum, and the order does not change at the
/// UTF-8 encoding-length boundaries (`U+007F`/`U+0080`, `U+07FF`/`U+0800`).
#[test]
fn test_ground_lexicographic_order() {
    assert_ground_fact(r#"(str.< "abc" "abd")"#);
    assert_ground_fact(r#"(not (str.< "abd" "abc"))"#);
    assert_ground_fact(r#"(str.< "ab" "abc")"#);
    assert_ground_fact(r#"(not (str.< "abc" "abc"))"#);
    assert_ground_fact(r#"(str.< "" "a")"#);
    assert_ground_fact(r#"(not (str.< "a" ""))"#);
    assert_ground_fact(r#"(str.<= "abc" "abc")"#);
    assert_ground_fact(r#"(str.<= "abc" "abd")"#);
    assert_ground_fact(r#"(not (str.<= "abd" "abc"))"#);
    assert_ground_fact(r#"(str.<= "" "")"#);
    // Code-point order across the UTF-8 encoding-length boundaries.
    assert_ground_fact(r#"(str.< "\u{7f}" "\u{80}")"#);
    assert_ground_fact(r#"(str.< "\u{7ff}" "\u{800}")"#);
    assert_ground_fact(r#"(str.< "\u{ffff}" "\u{10000}")"#);
    // Chainable: `(str.< a b c)` is `(and (str.< a b) (str.< b c))`.
    assert_ground_fact(r#"(str.< "a" "b" "c")"#);
    assert_ground_fact(r#"(not (str.< "a" "c" "b"))"#);
    assert_ground_fact(r#"(str.<= "a" "a" "b")"#);
}

/// The order's structural identities hold for *symbolic* operands too:
/// irreflexivity of `<`, reflexivity of `<=`, and `""` being the minimum.
/// These are the only symbolic `str.<` shapes the solver decides.
#[test]
fn test_symbolic_lexicographic_identities() {
    for (body, expected) in [
        (r#"(str.< x x)"#, "unsat"),
        (r#"(not (str.<= x x))"#, "unsat"),
        (r#"(str.< x "")"#, "unsat"),
        (r#"(not (str.<= "" x))"#, "unsat"),
        (r#"(str.<= x x)"#, "sat"),
        (r#"(str.<= "" x)"#, "sat"),
    ] {
        let script =
            format!("(set-logic QF_S)\n(declare-const x String)\n(assert {body})\n(check-sat)");
        assert_eq!(
            check_sat_verdict(&script),
            expected,
            "symbolic order identity: {body}"
        );
    }
}

/// `str.to_code` is the code point of a **singleton** string and `-1` for
/// everything else — `""` and any two-character string alike.  `str.from_code`
/// is the singleton string for a code point in `[0, 0x2FFFF]` and `""` outside
/// that range.
#[test]
fn test_ground_char_code_conversions() {
    assert_ground_fact(r#"(= (str.to_code "A") 65)"#);
    assert_ground_fact(r#"(= (str.to_code "") (- 1))"#);
    assert_ground_fact(r#"(= (str.to_code "AB") (- 1))"#);
    assert_ground_fact(r#"(= (str.to_code "\u{2ffff}") 196607)"#);

    assert_ground_fact(r#"(= (str.from_code 65) "A")"#);
    assert_ground_fact(r#"(= (str.len (str.from_code 0)) 1)"#);
    assert_ground_fact(r#"(= (str.from_code 196607) "\u{2ffff}")"#);
    // One past the alphabet, and negative: the empty string.
    assert_ground_fact(r#"(= (str.from_code 196608) "")"#);
    assert_ground_fact(r#"(= (str.from_code (- 1)) "")"#);
    // Round trip on a representable code point.
    assert_ground_fact(r#"(= (str.to_code (str.from_code 97)) 97)"#);
}

/// A UTF-16 surrogate is inside the theory's alphabet but is not a Unicode
/// scalar value, so OxiZ's `char`-backed strings cannot hold it.  Folding it
/// to `""` would be a *wrong* answer (the theory says the result has length
/// 1), so the term stays unevaluated and the verdict degrades to `unknown` —
/// never to `sat` or `unsat`.
#[test]
fn test_from_code_surrogate_is_unknown_not_wrong() {
    for body in [
        r#"(= (str.len (str.from_code 55296)) 1)"#,
        r#"(= (str.from_code 55296) "")"#,
        r#"(= (str.len (str.from_code 57343)) 1)"#,
    ] {
        let script = format!("(set-logic QF_S)\n(assert {body})\n(check-sat)");
        assert_eq!(
            check_sat_verdict(&script),
            "unknown",
            "a surrogate code point must not be decided: {body}"
        );
    }
}

/// `str.replace_re` replaces the **shortest leftmost** match — which is the
/// *empty* match at position 0 whenever the language contains `""`, so the
/// replacement is prepended.  `str.replace_re_all` replaces every shortest
/// **non-empty** match left to right, so an empty-matching regex leaves the
/// string alone.
///
/// Reference: the SMT-LIB Unicode Strings theory; Z3's `seq_rewriter.cpp`
/// folds neither operator, so these are cases where OxiZ decides more than Z3.
#[test]
fn test_ground_replace_re() {
    // Plain literal pattern: first match only, vs. every match.
    assert_ground_fact(r#"(= (str.replace_re "abcabc" (str.to_re "b") "X") "aXcabc")"#);
    assert_ground_fact(r#"(= (str.replace_re_all "abcabc" (str.to_re "b") "X") "aXcaXc")"#);
    // No match anywhere leaves the subject unchanged (both operators).
    assert_ground_fact(r#"(= (str.replace_re "abc" (str.to_re "z") "X") "abc")"#);
    assert_ground_fact(r#"(= (str.replace_re_all "abc" (str.to_re "z") "X") "abc")"#);
    assert_ground_fact(r#"(= (str.replace_re "abc" re.none "X") "abc")"#);
    assert_ground_fact(r#"(= (str.replace_re_all "abc" re.none "X") "abc")"#);
    // Empty-matching regex: prepend for `replace_re`, no-op for `replace_re_all`.
    assert_ground_fact(r#"(= (str.replace_re "abc" (str.to_re "") "X") "Xabc")"#);
    assert_ground_fact(r#"(= (str.replace_re_all "abc" (str.to_re "") "X") "abc")"#);
    assert_ground_fact(r#"(= (str.replace_re "" (str.to_re "") "X") "X")"#);
    assert_ground_fact(r#"(= (str.replace_re_all "" (str.to_re "") "X") "")"#);
    // `re.*` is nullable, so the shortest leftmost match is empty.
    assert_ground_fact(r#"(= (str.replace_re "aaa" (re.* (str.to_re "a")) "X") "Xaaa")"#);
    assert_ground_fact(r#"(= (str.replace_re_all "aaa" (re.* (str.to_re "a")) "X") "XXX")"#);
    // `re.+` is not nullable: shortest match is one character.
    assert_ground_fact(r#"(= (str.replace_re "aaab" (re.+ (str.to_re "a")) "X") "Xaab")"#);
    assert_ground_fact(r#"(= (str.replace_re_all "aaab" (re.+ (str.to_re "a")) "X") "XXXb")"#);
    // Leftmost first, then shortest: position 1 wins, and "b" beats "bc".
    assert_ground_fact(
        r#"(= (str.replace_re "abcabc" (re.union (str.to_re "bc") (str.to_re "b")) "X") "aXcabc")"#,
    );
    // A union containing `""`: `replace_re_all` skips the empty alternative.
    assert_ground_fact(
        r#"(= (str.replace_re_all "abc" (re.union (str.to_re "") (str.to_re "b")) "X") "aXc")"#,
    );
    // `re.allchar` matches exactly one character at every position.
    assert_ground_fact(r#"(= (str.replace_re_all "abc" re.allchar "X") "XXX")"#);
    // `re.all` is nullable, so `replace_re` prepends.
    assert_ground_fact(r#"(= (str.replace_re "abc" re.all "X") "Xabc")"#);
    // `re.range` and composition with other string operators.
    assert_ground_fact(r#"(= (str.replace_re_all "a1b2" (re.range "0" "9") "!") "a!b!")"#);
    assert_ground_fact(r#"(= (str.len (str.replace_re "abc" (str.to_re "b") "XY")) 4)"#);
}

/// A ground conflict is still found when it is one conjunct of a larger
/// assertion, at any depth of the `And` / `Or` / `Not` spine — and a
/// `distinct` is refuted as soon as two of its operands are known equal,
/// even with a free variable among the rest.
#[test]
fn test_ground_conflict_inside_boolean_structure() {
    // Conjunct of a top-level `and`, with a variable in the other conjunct.
    assert_eq!(
        check_sat_verdict(
            r#"(set-logic QF_S)
               (declare-const s String)
               (assert (and (str.contains s "q") (= (str.len "ab") 3)))
               (check-sat)"#,
        ),
        "unsat"
    );

    // `(not (or …))` distributes the negation over both disjuncts.
    assert_eq!(
        check_sat_verdict(
            r#"(set-logic QF_S)
               (declare-const s String)
               (assert (not (or (str.contains s "q") (= (str.len "ab") 2))))
               (check-sat)"#,
        ),
        "unsat"
    );

    // Two operands of the `distinct` are the same string.
    assert_eq!(
        check_sat_verdict(
            r#"(set-logic QF_S)
               (declare-const s String)
               (assert (distinct (str.substr "aba" 3 1) "" s))
               (check-sat)"#,
        ),
        "unsat"
    );
}

// ══════════════════════════════════════════════════════════════════════
// Controls for the ground refutation.
//
// The refutation may only ever turn `unknown` into a *justified* `unsat`.
// Two ways it could go wrong: reading a value into a variable, or treating
// a conditionally asserted formula as unconditional.  Every case below is
// satisfiable, so `unsat` is a soundness bug.
// ══════════════════════════════════════════════════════════════════════

/// A ground-false fact behind a polarity boundary — `Or`, `Implies`, `Ite`,
/// `Xor`, a Bool-sorted `Eq`, or de Morgan's `(not (and …))` — is
/// *conditional* and must never drive a refutation.
#[test]
fn test_control_conditional_ground_facts_not_unsat() {
    // `(str.substr "aba" 3 1)` is `""`, so the first disjunct is false; the
    // formula is satisfied by `p`.
    for body in [
        r#"(or (= (str.substr "aba" 3 1) "x") p)"#,
        r#"(=> p (= (str.len "ab") 3))"#,
        r#"(ite p (= (str.len "ab") 3) true)"#,
        r#"(= p (= (str.len "ab") 3))"#,
        r#"(not (and (= (str.len "ab") 2) q))"#,
        r#"(xor p (= (str.len "ab") 3))"#,
        r#"(not (or (and (= (str.len "ab") 3) p) q))"#,
    ] {
        let script = format!(
            "(set-logic ALL)\n(declare-const p Bool)\n(declare-const q Bool)\n\
             (assert {body})\n(check-sat)"
        );
        assert_ne!(
            check_sat_verdict(&script),
            "unsat",
            "conditional ground fact drove a refutation: {body}"
        );
    }

    // Issue #23's original reproducer stays `sat`: the premise is a genuinely
    // false ground fact, so the implication is vacuously true.
    assert_eq!(
        check_sat_verdict(
            r#"(set-logic QF_S)
               (declare-const s0 String)
               (assert (=> (= (str.++ (str.substr "aba" 3 1) "bb") "")
                           (distinct "b" (str.++ s0 "b"))))
               (check-sat)"#,
        ),
        "sat"
    );
}

/// Formulas that mention a string *variable* have no closed sub-term to
/// fold, so their verdicts are exactly what they were before the ground
/// refutation existed — `sat` or `unknown`, never `unsat`.
#[test]
fn test_control_variable_formulas_unaffected() {
    for body in [
        r#"(= (str.len s) 3)"#,
        r#"(str.contains s "abc")"#,
        r#"(= (str.substr s 0 2) "ab")"#,
        r#"(= (str.indexof s "a" 0) 2)"#,
        r#"(= (str.replace s "a" "b") "xbx")"#,
        r#"(str.in_re s (re.+ (re.range "a" "z")))"#,
        r#"(= (str.to_int s) 42)"#,
        r#"(= (str.++ s "b") (str.++ "a" "b"))"#,
        r#"(distinct s (str.substr "aba" 3 1))"#,
        // A *true* ground conjunct alongside a variable constraint leaves the
        // variable constraint to the ordinary machinery.
        r#"(and (= (str.len s) 3) (= (str.len "ab") 2))"#,
        r#"(and (= (str.len "ab") 2) (str.contains s "q"))"#,
        // The operators added with the symbolic `str.<` / code-conversion /
        // `replace_re` work: every one of these is satisfiable, so `unsat`
        // would be a soundness bug.
        r#"(str.< s "abc")"#,
        r#"(str.< "abc" s)"#,
        r#"(str.<= s "abc")"#,
        r#"(str.<= "abc" s)"#,
        r#"(not (str.< s "abc"))"#,
        r#"(not (str.<= s "abc"))"#,
        r#"(= (str.to_code s) 65)"#,
        r#"(= (str.to_code s) (- 1))"#,
        r#"(not (= (str.to_code s) 65))"#,
        r#"(= (str.replace_re s (str.to_re "b") "X") "aXc")"#,
        r#"(= (str.replace_re_all s (str.to_re "b") "X") "aXc")"#,
        r#"(not (= (str.replace_re s (str.to_re "b") "X") "aXc"))"#,
        r#"(= (str.replace_re "abc" (str.to_re "b") s) "aXc")"#,
        // A symbolic *regex* operand: the theory cannot compile it, so the
        // verdict must degrade to `unknown` rather than to a guess.
        r#"(= (str.replace_re "abc" (str.to_re s) "X") "aXc")"#,
    ] {
        let script =
            format!("(set-logic QF_S)\n(declare-const s String)\n(assert {body})\n(check-sat)");
        assert_ne!(
            check_sat_verdict(&script),
            "unsat",
            "satisfiable formula over a string variable was refuted: {body}"
        );
    }
}

/// Directly asserted *true* ground facts stay `sat`; the refutation must
/// not fire on the polarity it is not looking at.
#[test]
fn test_control_true_ground_facts_stay_sat() {
    for body in [
        r#"(and (= (str.len "ab") 2) (str.contains "abc" "b"))"#,
        r#"(not (= (str.len "ab") 3))"#,
        r#"(not (not (= (str.len "ab") 2)))"#,
        r#"(distinct "a" "b")"#,
        r#"(or (= (str.len "ab") 3) (= (str.len "ab") 2))"#,
        // The new operators, in the polarity `assert_ground_fact` does not
        // reach on its own (a *false* fact under a `not`).
        r#"(not (str.< "abd" "abc"))"#,
        r#"(not (= (str.to_code "ab") 65))"#,
        r#"(not (= (str.from_code 65) "B"))"#,
        r#"(not (= (str.replace_re "abc" (str.to_re "b") "X") "abc"))"#,
        r#"(not (= (str.replace_re_all "abc" (str.to_re "") "X") "Xabc"))"#,
    ] {
        let script = format!("(set-logic QF_S)\n(assert {body})\n(check-sat)");
        assert_eq!(
            check_sat_verdict(&script),
            "sat",
            "true ground fact was not reported sat: {body}"
        );
    }
}

/// The symbolic uses of the newly wired operators produce a **verified**
/// model, not a free-Boolean guess: `sat` here means the ground solver found
/// a witness and evaluated every assertion under it.
#[test]
fn test_symbolic_string_operators_produce_verified_models() {
    // `str.<`: the repair search finds `x = "", y = "a"` (or similar).
    assert_eq!(
        check_sat_verdict(
            r#"(set-logic QF_S)
               (declare-const x String)
               (declare-const y String)
               (assert (str.< x y))
               (check-sat)"#,
        ),
        "sat"
    );

    // Two strict bounds with no literal witness between them: the repair
    // search reaches `"abb"` extended by a fresh character.
    assert_eq!(
        check_sat_verdict(
            r#"(set-logic QF_S)
               (declare-const x String)
               (assert (str.< "abb" x))
               (assert (str.< x "abc"))
               (check-sat)"#,
        ),
        "sat"
    );

    // `(= (str.to_code x) 65)` is witnessed by `x = "A"`.
    let output = script_output(
        r#"(set-logic QF_S)
           (declare-const x String)
           (assert (= (str.to_code x) 65))
           (check-sat)
           (get-model)"#,
    );
    assert!(
        output.iter().any(|line| line == "sat"),
        "expected sat, got {output:?}"
    );
    assert!(
        output
            .iter()
            .any(|line| line.contains("define-fun x") && line.contains("\"A\"")),
        "the witness must be the singleton string for code point 65: {output:?}"
    );

    // `str.replace_re` over a variable subject, with the model published.
    let output = script_output(
        r#"(set-logic QF_S)
           (declare-const x String)
           (assert (= (str.replace_re x (str.to_re "b") "X") "aXc"))
           (check-sat)
           (get-model)"#,
    );
    assert!(
        output.iter().any(|line| line == "sat"),
        "expected sat, got {output:?}"
    );
    assert!(
        output.iter().any(|line| line.contains("define-fun x")),
        "a verified witness must be published as a model: {output:?}"
    );
}
