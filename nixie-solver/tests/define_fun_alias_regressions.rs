//! Nullary `define-fun` handling regressions.
//!
//! The Context historically asserted `(= name body)` for every nullary
//! `define-fun` — definitionally satisfiable, added for `get-model`
//! visibility.  On macro-heavy inputs (the `goto_symex`/Sydr files declare
//! tens of thousands of nullary definitions, each body referencing earlier
//! bodies) that ran the full per-assert preprocessing+blasting pipeline over
//! every chained body (quadratic ingestion) and left the unified core
//! carrying tens of thousands of definitional clauses: `bmc-bv-svcomp14/
//! s3_clnt_1_true` never *reached* `check()` inside 400 s.  Definitions are
//! now pure aliases (z3 macro semantics): declared for introspection,
//! solver-side unit-eq reps kept via `Solver::note_define_fun_alias`, and
//! `get-model` values resolved by evaluating the body under the `sat`
//! verdict's model (`Context::resolve_define_fun_aliases`).
//!
//! These tests pin the contract the change must preserve:
//!
//! 1. **No constraint** — a definition cannot change satisfiability
//!    (`define_does_not_constrain`).
//! 2. **Model visibility** — the name lists at its *defined* value, for
//!    constant bodies, compound bit-vector bodies over pinned variables,
//!    and chained definitions (`define_lists_defined_value_*`).
//! 3. **`get-value`** — unchanged (the parser inlines the body at use
//!    sites; the value comes from the body itself).
//! 4. **Ingestion scale** — thousands of chained definitions parse and
//!    check in bounded time (`chained_defines_ingest_linearly`): the
//!    historical quadratic made this class of input unsolvable *before*
//!    the search began.

use nixie_solver::Context;

fn run(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    let out = ctx.execute_script(script).expect("script executes");
    out.iter()
        .filter(|t| !t.trim().is_empty())
        .cloned()
        .collect()
}

/// A definition is a macro: `(define-fun b () Bool false)` must not make
/// the goal unsat.
#[test]
fn define_does_not_constrain() {
    let out = run(r#"
        (set-logic QF_BV)
        (define-fun b () Bool false)
        (define-fun v () (_ BitVec 8) (_ bv255 8))
        (check-sat)
    "#);
    assert_eq!(out.last().map(String::as_str), Some("sat"));
}

/// Constant body: the name lists at the constant's value.
#[test]
fn define_lists_defined_value_constant() {
    let out = run(r#"
        (set-logic QF_BV)
        (define-fun answer () (_ BitVec 8) (_ bv42 8))
        (assert true)
        (check-sat)
        (get-model)
    "#);
    assert_eq!(out[0], "sat");
    assert!(
        out[1].contains("(define-fun answer () (_ BitVec 8) #b00101010)"),
        "model: {}",
        out[1]
    );
}

/// Compound BV body over a pinned variable: the name lists at the body's
/// value under the model (`hi = x + 1 = 8` when `x = 7`).  `Model::eval`
/// alone cannot fold BV operators — the resolution substitutes model
/// assignments first, exactly like `get-value`'s completion.
#[test]
fn define_lists_defined_value_compound_bv() {
    let out = run(r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (define-fun hi () (_ BitVec 8) (bvadd x (_ bv1 8)))
        (assert (= x (_ bv7 8)))
        (check-sat)
        (get-model)
    "#);
    assert_eq!(out[0], "sat");
    assert!(
        out[1].contains("(define-fun hi () (_ BitVec 8) #b00001000)"),
        "model: {}",
        out[1]
    );
}

/// Chained definitions resolve transitively (`c = b + 1`, `b = x + 1`).
#[test]
fn define_lists_defined_value_chained() {
    let out = run(r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (define-fun b () (_ BitVec 8) (bvadd x (_ bv1 8)))
        (define-fun c () (_ BitVec 8) (bvadd b (_ bv1 8)))
        (assert (= x (_ bv9 8)))
        (check-sat)
        (get-model)
    "#);
    assert_eq!(out[0], "sat");
    assert!(
        out[1].contains("(define-fun c () (_ BitVec 8) #b00001011)"),
        "model: {}",
        out[1]
    );
}

/// `get-value` on the name: the parser inlines the body, so the value is
/// the body's — this contract predates the alias change and must survive.
#[test]
fn define_get_value_reports_body() {
    let out = run(r#"
        (set-logic QF_BV)
        (define-fun answer () (_ BitVec 8) (_ bv42 8))
        (check-sat)
        (get-value (answer))
    "#);
    assert_eq!(out[0], "sat");
    assert!(
        out[1].contains("#x2a") || out[1].contains("#b00101010"),
        "{}",
        out[1]
    );
}

/// The ingestion canary: N chained nullary definitions over one variable,
/// then a contradiction on the chain's end.  Under the historical
/// assert-per-define this scaled quadratically (each asserted `(= name
/// body)` re-ran the per-assert pipeline over the referenced bodies);
/// the assert-free path is linear.  The bound is generous to stay
/// load-robust while still tripping on a reintroduced quadratic.
#[test]
fn chained_defines_ingest_linearly() {
    const N: usize = 6000;
    let mut script = String::from("(set-logic QF_BV)\n(declare-const x (_ BitVec 32))\n");
    script.push_str("(define-fun d0 () (_ BitVec 32) (bvadd x (_ bv1 32)))\n");
    for i in 1..N {
        script.push_str(&format!(
            "(define-fun d{i} () (_ BitVec 32) (bvadd d{} (_ bv1 32)))\n",
            i - 1
        ));
    }
    // d_{N-1} = x + N: force x = 0 and contradict x + N = 0 for 0 < N < 2^31.
    script.push_str(&format!(
        "(assert (= x (_ bv0 32)))\n(assert (= d{} (_ bv0 32)))\n(check-sat)\n",
        N - 1
    ));
    let start = std::time::Instant::now();
    let out = run(&script);
    assert_eq!(out.last().map(String::as_str), Some("unsat"));
    let elapsed = start.elapsed();
    assert!(
        elapsed.as_secs() < 25,
        "chained define ingestion too slow: {elapsed:?} (quadratic regression?)"
    );
}
