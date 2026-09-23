//! Reading a value out of a model whose array variables are pinned by
//! ALIAS-and-chain assignments: `select_in`'s walk (and the model builder
//! that feeds it) must resolve through aliases and must never install a
//! value that mentions its own name.
//!
//! Both regressions came out of the TLA+ two-array BMC arc
//! (`docs/handovers/2026-09-22-dom-pair-budget-handoff.md`): a trace decoder
//! completing never-read array points from the model found (1) walks that
//! broke on alias assignments, so every don't-care defaulted, and (2) an
//! EUF-overwrite pass that re-valued `x@0` with `store(x@0, 1, 1)` — a value
//! containing the name itself.

use nixie_solver::Context;

/// Runs `script` and returns the printed `(get-value …)` lines verbatim
/// (everything that is not a verdict).
fn values(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    let out = ctx.execute_script(script).expect("executes");
    out.into_iter()
        .filter(|l| !matches!(l.as_str(), "sat" | "unsat" | "unknown"))
        .collect()
}

/// `f = g` (an alias: neither side is a store) and `g = store(base, 1, 5)`.
/// Reading `f[1]` must follow `f -> g -> store(base, 1, 5)` and answer `5`;
/// before alias-following, the walk broke at `g`, the minted
/// `select(f, 1)` matched nothing, and the point read back unconstrained —
/// which is exactly the never-read-point shape the TLA+ trace decoder has to
/// complete.
#[test]
fn select_walks_through_an_alias_assignment() {
    let script = r#"
(set-logic ALL)
(declare-fun f () (Array Int Int))
(declare-fun g () (Array Int Int))
(declare-fun base () (Array Int Int))
(assert (= f g))
(assert (= g (store base 1 5)))
(check-sat)
(get-value ((select f 1)))
"#;
    assert_eq!(values(script), vec!["(((select f 1) 5))"]);
}

/// The alias may sit at the END of the chain too: the store's base is read
/// through a further alias (`h = base`), so the miss-case read at index 2
/// walks `f -> g -> store(base=h, 1, 5) -> h` and finds the query-built
/// select at 2 there.
#[test]
fn select_walks_alias_bases_to_the_underlying_reads() {
    let script = r#"
(set-logic ALL)
(declare-fun f () (Array Int Int))
(declare-fun g () (Array Int Int))
(declare-fun h () (Array Int Int))
(declare-fun base () (Array Int Int))
(assert (= h base))
(assert (= base (store (store ((as const (Array Int Int)) 0) 2 9) 3 0)))
(assert (= f g))
(assert (= g (store h 1 5)))
(check-sat)
(get-value ((select f 2)))
"#;
    assert_eq!(values(script), vec!["(((select f 2) 9))"]);
}

/// The self-reference shape: `x = y` and `y = store(x, 1, 7)` are
/// satisfiable (the write is a no-op on a free `x`), and `x`'s EUF class
/// then contains both names while `y`'s recorded value mentions `x`.
/// Re-valuing `x` with that value installs `x -> store(x, 1, 7)` — a value
/// containing its own name, on which `Model::eval` ping-pongs to its chain
/// bound and reads back garbage.  Whatever the model prints for `x`, the
/// *point readings* must stay exact: `x[1]` is 7 and `y[1]` is 7.
#[test]
fn model_never_installs_a_self_referential_array_value() {
    let script = r#"
(set-logic ALL)
(declare-fun x () (Array Int Int))
(declare-fun y () (Array Int Int))
(assert (= x y))
(assert (= y (store x 1 7)))
(check-sat)
(get-value ((select x 1) (select y 1)))
"#;
    assert_eq!(
        values(script),
        vec!["(((select x 1) 7)\n ((select y 1) 7))"],
        "a self-referential assignment would break every point reading of x"
    );
}
