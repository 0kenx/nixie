//! Regression tests for the independently-reimplemented lookup-table
//! flattening / domain-first branching fixes (upstream PR #32 against
//! cool-japan/oxiz) and the equality-logic transitivity preprocessor
//! (upstream PR #33).
//!
//! Lower-level, mechanism-specific tests live next to the code they
//! exercise:
//! * `nixie-solver/src/solver/encode/finite_map_ite/tests.rs` -- spine
//!   detection and the index/domain bookkeeping in isolation
//!   (`lookup_index_terms` is crate-private and unreachable from here).
//! * `nixie-solver/src/solver/eq_skeleton/tests.rs` -- purity-detection edge
//!   cases and, critically, the post-solve re-verification actually
//!   refusing a deliberately inconsistent assignment (the model backstop's
//!   *firing* path, which needs white-box access to force).
//!
//! This file covers the fixes whose defining property is only visible
//! end-to-end: does the *whole solver*, driven exactly as an SMT-LIB2 client
//! would drive it, answer `sat`/`unsat` correctly, and does `get-value`
//! still resolve the terms a user actually wrote (not the internal
//! rewritten form).

use nixie_solver::{Context, Solver, SolverConfig, SolverResult};

/// Run `script` through a fresh [`Context`], returning its output lines.
fn run(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script)
        .expect("script should parse and run")
}

// ======== PR #32 -- lookup-table flattening ========

/// A 5-key lookup spine, pinned at a key that is *not* the first arm: `sat`,
/// and `get-value` on the *original* `ite` expression the user wrote (not
/// some internal rewritten form) must still resolve to that key's value.
/// `Model::eval` walks the term structure directly from the model's constant
/// values, independent of whatever internal rewrite `flatten_lookup_spines`
/// performed at encode time, so this is a genuine end-to-end check of the
/// flattening's semantics, not just of the final SAT/UNSAT bit.
#[test]
fn test_pr32_lookup_spine_get_value_matches_original_ite() {
    let script = r#"
        (declare-const idx Int)
        (define-fun table ((i Int)) Int
          (ite (= i 1) 100
          (ite (= i 2) 200
          (ite (= i 3) 300
          (ite (= i 4) 400
          999)))))
        (assert (= idx 3))
        (check-sat)
        (get-value ((table idx)))
    "#;
    let output = run(script);
    assert_eq!(output[0], "sat");
    assert!(
        output[1].contains("300"),
        "idx = 3 must select the third arm's value via the ORIGINAL ite expression: {}",
        output[1]
    );
}

/// The default (fallthrough) branch of a flattened spine must still be
/// reachable: an index outside every key must select it, not silently drop
/// to some other arm.
#[test]
fn test_pr32_lookup_spine_default_branch_is_reachable() {
    let script = r#"
        (declare-const idx Int)
        (define-fun table ((i Int)) Int
          (ite (= i 1) 100
          (ite (= i 2) 200
          (ite (= i 3) 300
          (ite (= i 4) 400
          999)))))
        (assert (= idx 42))
        (check-sat)
        (get-value ((table idx)))
    "#;
    let output = run(script);
    assert_eq!(output[0], "sat");
    assert!(
        output[1].contains("999"),
        "an index matching no key must select the default branch: {}",
        output[1]
    );
}

/// Forcing the result to a value that does *not* belong to the key the index
/// is pinned to must be `unsat` -- the flattened defining implications are
/// still a complete, bidirectional-enough description of the table (the
/// disjoint-arm case is exercised by `test_pr32_at_most_one_key_holds_at_once`
/// in the unit tests; this pins the *value* side).
#[test]
fn test_pr32_lookup_spine_wrong_value_at_pinned_key_is_unsat() {
    let script = r#"
        (declare-const idx Int)
        (declare-const r Int)
        (assert (= r
          (ite (= idx 1) 100
          (ite (= idx 2) 200
          (ite (= idx 3) 300
          (ite (= idx 4) 400
          999))))))
        (assert (= idx 2))
        (assert (not (= r 200)))
        (check-sat)
    "#;
    assert_eq!(run(script), vec!["unsat"]);
}

/// The companion `sat` control for the previous test: the same table, the
/// same pin, but the *correct* value asserted instead.
#[test]
fn test_pr32_lookup_spine_correct_value_at_pinned_key_is_sat() {
    let script = r#"
        (declare-const idx Int)
        (declare-const r Int)
        (assert (= r
          (ite (= idx 1) 100
          (ite (= idx 2) 200
          (ite (= idx 3) 300
          (ite (= idx 4) 400
          999))))))
        (assert (= idx 2))
        (assert (= r 200))
        (check-sat)
    "#;
    assert_eq!(run(script), vec!["sat"]);
}

/// A short (2-arm) equality-`ite` chain sits below `MIN_LOOKUP_ARMS` and is
/// left to the generic `eliminate_nonbool_ite` muxer; it must still solve
/// correctly, both the reachable and default branch.
#[test]
fn test_pr32_short_ite_chain_still_solves_correctly() {
    let sat = run(r#"
        (declare-const idx Int)
        (declare-const r Int)
        (assert (= r (ite (= idx 1) 10 (ite (= idx 2) 20 0))))
        (assert (= idx 1))
        (assert (= r 10))
        (check-sat)
    "#);
    assert_eq!(sat, vec!["sat"]);

    let unsat = run(r#"
        (declare-const idx Int)
        (declare-const r Int)
        (assert (= r (ite (= idx 1) 10 (ite (= idx 2) 20 0))))
        (assert (= idx 1))
        (assert (= r 20))
        (check-sat)
    "#);
    assert_eq!(unsat, vec!["unsat"]);
}

/// The "aliasing-gate" scenario: an `ite`-heavy `QF_UF` formula that has NO
/// equality-`ite` lookup table anywhere (every guard is a plain Boolean, not
/// an `(= idx k)` comparison) must be completely unaffected by
/// `flatten_lookup_spines` and still solve correctly. This is the shape
/// upstream's own validation regression was found on (firewire-style
/// `ite`-over-uninterpreted-constants nests without any table): nothing here
/// should ever register a lookup index or pay for domain bookkeeping that
/// does not apply, and the formula's actual (unrelated) unsatisfiability
/// must still be found.
#[test]
fn test_pr32_ite_heavy_formula_without_tables_is_unaffected() {
    let script = r#"
        (declare-sort U 0)
        (declare-const u1 U)
        (declare-const u2 U)
        (declare-const u3 U)
        (declare-fun f (U) U)
        (declare-fun g (U) U)
        (declare-const p Bool)
        (declare-const q Bool)
        (assert (= (g u1) (f (ite p (ite q u2 u3) (ite q u3 u2)))))
        (assert (not p))
        (assert q)
        (assert (not (= (g u1) (f u2))))
        (check-sat)
    "#;
    // (not p), q selects the else-branch's then-branch: u3. g(u1) = f(u3),
    // which does not contradict g(u1) != f(u2) -- genuinely sat.
    assert_eq!(run(script), vec!["sat"]);

    let script_unsat = r#"
        (declare-sort U 0)
        (declare-const u1 U)
        (declare-const u2 U)
        (declare-const u3 U)
        (declare-fun f (U) U)
        (declare-fun g (U) U)
        (declare-const p Bool)
        (declare-const q Bool)
        (assert (= (g u1) (f (ite p (ite q u2 u3) (ite q u3 u2)))))
        (assert (not p))
        (assert q)
        (assert (not (= (g u1) (f u3))))
        (check-sat)
    "#;
    // Same selection (u3), but now directly contradicted -- unsat.
    assert_eq!(run(script_unsat), vec!["unsat"]);
}

/// Opt-in domain-first branching (`SolverConfig::enable_domain_first_branching`)
/// must never change the verdict -- it is a decision-order hint, not a
/// rewrite -- on a formula with a genuine flattened lookup table.
#[test]
fn test_pr32_domain_first_branching_opt_in_matches_default_verdict() {
    use nixie_core::ast::TermManager;

    fn build_and_check(config: SolverConfig) -> (SolverResult, Option<i64>) {
        let mut manager = TermManager::new();
        let mut solver = Solver::with_config(config);
        let int = manager.sorts.int_sort;
        let idx = manager.mk_var("idx", int);
        let r = manager.mk_var("r", int);

        let default = manager.mk_int(0);
        let mut chain = default;
        for (key, value) in [(5i64, 50i64), (4, 40), (3, 30), (2, 20), (1, 10)] {
            let k = manager.mk_int(key);
            let v = manager.mk_int(value);
            let eq = manager.mk_eq(idx, k);
            chain = manager.mk_ite(eq, v, chain);
        }
        let top = manager.mk_eq(r, chain);
        solver.assert(top, &mut manager);
        let three = manager.mk_int(3);
        let pin = manager.mk_eq(idx, three);
        solver.assert(pin, &mut manager);

        let result = solver.check(&mut manager);
        let value = solver
            .model()
            .and_then(|m| m.get(r))
            .and_then(|v| manager.get(v).cloned())
            .and_then(|t| match t.kind {
                nixie_core::ast::TermKind::IntConst(n) => {
                    use num_traits::ToPrimitive;
                    n.to_i64()
                }
                _ => None,
            });
        (result, value)
    }

    let default_result = build_and_check(SolverConfig::default());
    let opt_in = SolverConfig {
        enable_domain_first_branching: true,
        ..SolverConfig::default()
    };
    let opt_in_result = build_and_check(opt_in);

    assert_eq!(default_result.0, SolverResult::Sat);
    assert_eq!(
        default_result, opt_in_result,
        "domain-first branching must not change the verdict or the entailed value of r"
    );
    assert_eq!(default_result.1, Some(30), "idx = 3 must select the 30 arm");
}

// ======== PR #33 -- equality-logic transitivity preprocessor ========

/// The textbook case straight from the requirements: `a = b`, `b = c`, and
/// `a != c` asserted propositionally. Transitively inconsistent, so `unsat`
/// -- and, being pure equality logic, decided entirely by the fast path.
#[test]
fn test_pr33_transitivity_chain_is_unsat() {
    let script = r#"
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (assert (= a b))
        (assert (= b c))
        (assert (not (= a c)))
        (check-sat)
    "#;
    assert_eq!(run(script), vec!["unsat"]);
}

/// The satisfiable control: the same shape, but `a = c` is asserted instead
/// of its negation, which is exactly what transitivity entails, so it must
/// stay `sat`.
#[test]
fn test_pr33_transitivity_chain_stays_sat_when_consistent() {
    let script = r#"
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (assert (= a b))
        (assert (= b c))
        (assert (= a c))
        (check-sat)
    "#;
    assert_eq!(run(script), vec!["sat"]);
}

/// A disjunctive-equality "pigeonhole": 5 constants, each asserted to equal
/// one of only 4 "slot" constants, plus all 5 asserted pairwise distinct.
/// By pigeonhole two of the five must share a slot (hence be equal),
/// contradicting the distinctness -- `unsat`. This is the shape ("many
/// locally-consistent disjunctive choices, globally inconsistent only
/// through transitivity") that makes naive CDCL(T) round-trip with EUF
/// repeatedly; the static transitivity clauses let plain SAT alone decide
/// it. No wall-clock assertion -- see the next test for the size/parity
/// argument this one exists to set up.
#[test]
fn test_pr33_disjunctive_pigeonhole_chain_is_unsat() {
    let mut script = String::from("(declare-sort U 0)\n");
    for i in 0..5 {
        script.push_str(&format!("(declare-const x{i} U)\n"));
    }
    for i in 0..4 {
        script.push_str(&format!("(declare-const s{i} U)\n"));
    }
    for i in 0..5 {
        script.push_str(&format!(
            "(assert (or (= x{i} s0) (= x{i} s1) (= x{i} s2) (= x{i} s3)))\n"
        ));
    }
    for i in 0..5 {
        for j in (i + 1)..5 {
            script.push_str(&format!("(assert (not (= x{i} x{j})))\n"));
        }
    }
    script.push_str("(check-sat)\n");
    assert_eq!(run(&script), vec!["unsat"]);
}

/// The same pigeonhole shape, but with one assertion (`n > 0`, an
/// arithmetic atom unrelated to the equality structure) added purely to
/// disqualify the formula from the fast path (`collect_equality_skeleton`
/// declines the moment it sees anything outside its grammar). Falls back to
/// the ordinary CDCL(T) + EUF search, which is a sound and complete decision
/// procedure for equality logic in its own right (congruence closure is
/// inherently transitive) -- proving the fast path and the fallback agree at
/// a size both can solve, without timing either one.
#[test]
fn test_pr33_disjunctive_pigeonhole_chain_normal_path_agrees() {
    let mut script = String::from("(declare-sort U 0)\n(declare-const n Int)\n(assert (> n 0))\n");
    for i in 0..5 {
        script.push_str(&format!("(declare-const x{i} U)\n"));
    }
    for i in 0..4 {
        script.push_str(&format!("(declare-const s{i} U)\n"));
    }
    for i in 0..5 {
        script.push_str(&format!(
            "(assert (or (= x{i} s0) (= x{i} s1) (= x{i} s2) (= x{i} s3)))\n"
        ));
    }
    for i in 0..5 {
        for j in (i + 1)..5 {
            script.push_str(&format!("(assert (not (= x{i} x{j})))\n"));
        }
    }
    script.push_str("(check-sat)\n");
    assert_eq!(
        run(&script),
        vec!["unsat"],
        "the arithmetic atom must disqualify the fast path, but the fallback \
         CDCL(T)+EUF search must reach the same (correct) verdict"
    );
}

/// The satisfiable pigeonhole control: 4 constants into 4 slots has an exact
/// bijection, so it must stay `sat` (the transitivity clauses must never
/// over-constrain a genuinely satisfiable disjunctive-equality formula).
#[test]
fn test_pr33_pigeonhole_with_enough_slots_is_sat() {
    let mut script = String::from("(declare-sort U 0)\n");
    for i in 0..4 {
        script.push_str(&format!("(declare-const x{i} U)\n"));
    }
    for i in 0..4 {
        script.push_str(&format!("(declare-const s{i} U)\n"));
    }
    for i in 0..4 {
        script.push_str(&format!(
            "(assert (or (= x{i} s0) (= x{i} s1) (= x{i} s2) (= x{i} s3)))\n"
        ));
    }
    for i in 0..4 {
        for j in (i + 1)..4 {
            script.push_str(&format!("(assert (not (= x{i} x{j})))\n"));
        }
    }
    script.push_str("(check-sat)\n");
    assert_eq!(run(&script), vec!["sat"]);
}

/// Pure-equality detection, negative case: a single function application
/// mixed into an otherwise-pure equality formula must disqualify the whole
/// thing from the fast path -- and the formula must still be decided
/// correctly (by the ordinary EUF-backed search) once it falls through.
/// `f(a) = f(a)` is a tautology and changes nothing about satisfiability, so
/// this formula's verdict is identical to `test_pr33_transitivity_chain_is_unsat`;
/// only the *path* taken to it differs.
#[test]
fn test_pr33_function_application_disqualifies_but_answer_stays_correct() {
    let script = r#"
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (declare-fun f (U) U)
        (assert (= a b))
        (assert (= b c))
        (assert (not (= a c)))
        (assert (= (f a) (f a)))
        (check-sat)
    "#;
    assert_eq!(run(script), vec!["unsat"]);
}

/// Pure-equality detection, positive case restated at `Context` level (the
/// unit tests in `eq_skeleton/tests.rs` check `collect_equality_skeleton`
/// directly): a formula built *only* from `and`/`or`/`not`/`=` over
/// uninterpreted constants, with a satisfiable and an unsatisfiable
/// variant, both by way of a `check-sat` round-trip through a full
/// SMT-LIB2 script (declarations, multiple assertions, boolean structure).
#[test]
fn test_pr33_pure_equality_positive_case_both_verdicts() {
    let sat = r#"
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (declare-const d U)
        (assert (or (= a b) (= a c)))
        (assert (not (= a d)))
        (assert (not (= b d)))
        (assert (not (= c d)))
        (check-sat)
    "#;
    assert_eq!(run(sat), vec!["sat"]);

    let unsat = r#"
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (assert (or (= a b) (= a c)))
        (assert (not (= a b)))
        (assert (not (= a c)))
        (check-sat)
    "#;
    assert_eq!(run(unsat), vec!["unsat"]);
}

/// `(get-model)` and `(get-value ...)` after a pure-equality `sat` must report
/// values *of the declared sort*.
///
/// An uninterpreted sort has no literals, so the only honest value is an
/// abstract witness – the same `@uc_S_n` form the model layer already uses for
/// any unconstrained constant of such a sort. Reporting a concrete `Int` tag
/// instead (which is what a class index printed straight into the model looks
/// like) is a sort error in the output. The witnesses also have to *respect the
/// partition*: constants the formula equates share one, constants it separates
/// do not.
#[test]
fn test_pr33_pure_equality_model_uses_sort_correct_witnesses() {
    let script = r#"
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (assert (= a b))
        (assert (not (= a c)))
        (check-sat)
        (get-model)
        (get-value (a b c))
    "#;
    let output = run(script);
    assert_eq!(output.first().map(String::as_str), Some("sat"));

    let model = output.get(1).cloned().unwrap_or_default();
    let values = output.get(2).cloned().unwrap_or_default();
    for rendered in [&model, &values] {
        assert!(
            rendered.contains("@uc_U_"),
            "an uninterpreted-sort constant must print as an abstract witness, got: {rendered}"
        );
    }

    // Pull `a`, `b` and `c`'s witnesses out of the `(get-value ...)` answer,
    // which prints one `(term value)` pair per line.
    let witness_of = |name: &str| -> String {
        values
            .lines()
            .find(|line| line.contains(&format!("({name} ")))
            .and_then(|line| {
                line.split_whitespace()
                    .last()
                    .map(|token| token.trim_end_matches(')').to_string())
            })
            .unwrap_or_else(|| panic!("no value reported for {name} in: {values}"))
    };
    let (wa, wb, wc) = (witness_of("a"), witness_of("b"), witness_of("c"));
    assert!(wa.starts_with("@uc_U_"), "unexpected witness for a: {wa}");
    assert_eq!(wa, wb, "a = b is asserted, so they share a witness");
    assert_ne!(wa, wc, "a != c is asserted, so their witnesses must differ");
}
