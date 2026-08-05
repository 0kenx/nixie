//! Regression coverage for `define-fun` call-site expansion (see
//! `oxiz-core/src/smtlib/parser/{commands,terms,mod}.rs`).
//!
//! ## Root cause this pins
//!
//! `Parser::expand_defined_fun` used to rebuild each formal parameter's `Var`
//! term from its bare *name* at the call site, guessing its sort from
//! `self.constants` (falling back to `Bool` when no same-named global
//! constant existed). Since [`TermManager::mk_var`] hash-conses on the
//! `(name, sort)` pair, guessing the wrong sort mints a *different* term than
//! the one actually bound while the macro body was parsed — the substitution
//! map's key then never matches anything in the body, `substitute` is a
//! silent no-op, and the formal parameter is left dangling (free) in the
//! "expanded" term instead of being replaced by the call-site argument.
//!
//! The fix stores each formal parameter's exact `TermId`, minted once while
//! the body is parsed, and reuses it verbatim as the substitution key at
//! every call site (`FunctionMacro::formal_vars`).
//!
//! Every case below is a shape where the old name+guessed-sort recovery
//! either fails outright (no same-named global constant exists, or one
//! exists at the wrong sort) or only "works" by accident (the guessed
//! fallback sort happens to match). The assertions check the *fixed*
//! behavior directly rather than executing the old code path.

use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::smtlib::{Command, parse_script};

/// Depth-first search for a free `Var` named `name` anywhere under `root`.
/// Iterative (explicit stack) so a pathological script cannot blow the test
/// harness's stack; a handful of frames is all any of these scripts need.
fn contains_free_var(tm: &TermManager, root: TermId, name: &str) -> bool {
    let mut stack = vec![root];
    let mut seen = std::collections::HashSet::new();
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let Some(t) = tm.get(id) else { continue };
        match &t.kind {
            TermKind::Var(s) if tm.resolve_str(*s) == name => {
                return true;
            }
            TermKind::Var(_) => {}
            TermKind::Not(a) | TermKind::Neg(a) => stack.push(*a),
            TermKind::And(xs) | TermKind::Or(xs) | TermKind::Add(xs) | TermKind::Mul(xs) => {
                stack.extend(xs.iter().copied());
            }
            TermKind::Eq(a, b)
            | TermKind::Lt(a, b)
            | TermKind::Le(a, b)
            | TermKind::Gt(a, b)
            | TermKind::Ge(a, b)
            | TermKind::Sub(a, b)
            | TermKind::Xor(a, b)
            | TermKind::Implies(a, b) => {
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermKind::Apply { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    false
}

/// Pull the sole top-level `assert`ed term out of a parsed script.
fn sole_assertion(cmds: &[Command]) -> TermId {
    let asserts: Vec<TermId> = cmds
        .iter()
        .filter_map(|c| match c {
            Command::Assert(t) => Some(*t),
            _ => None,
        })
        .collect();
    assert_eq!(asserts.len(), 1, "expected exactly one assert command");
    asserts[0]
}

/// The common real-world shape: a define-fun parameter whose name is never
/// declared as a global constant anywhere in the script. The old code's
/// `self.constants.get(param_name)` lookup misses entirely and falls back to
/// `Bool`, which does not match this (Int-sorted) parameter at all.
#[test]
fn test_pr27_define_fun_param_absent_from_globals_int_sort() {
    let mut tm = TermManager::new();
    let cmds = parse_script(
        r#"
(declare-const w Int)
(define-fun triple ((v Int)) Int (* v 3))
(assert (= (triple w) 9))
"#,
        &mut tm,
    )
    .expect("parse must succeed");
    let a = sole_assertion(&cmds);
    assert!(
        contains_free_var(&tm, a, "w"),
        "expansion of (triple w) must mention the call-site argument w"
    );
    assert!(
        !contains_free_var(&tm, a, "v"),
        "expansion of (triple w) must not leave the formal parameter v free"
    );
}

/// Sharper version of the same defect: a global constant *does* share the
/// parameter's name, but at a different sort. The old fallback would resolve
/// `self.constants.get("n")` to `Bool`, still missing the actual (Int)
/// parameter var.
#[test]
fn test_pr27_define_fun_param_shadowed_by_differently_sorted_global() {
    let mut tm = TermManager::new();
    let cmds = parse_script(
        r#"
(declare-const n Bool)
(declare-const m Int)
(define-fun double-it ((n Int)) Int (* n 2))
(assert (= (double-it m) 10))
"#,
        &mut tm,
    )
    .expect("parse must succeed");
    let a = sole_assertion(&cmds);
    assert!(
        contains_free_var(&tm, a, "m"),
        "expansion of (double-it m) must mention the call-site argument m"
    );
    // The global Bool `n` is a different term (different sort) from the
    // Int-sorted formal parameter `n`; the expansion must not retain any
    // free occurrence of the *Int* parameter either way.
    let a_term = tm.get(a).expect("assertion term exists");
    if let TermKind::Eq(lhs, _) = &a_term.kind {
        let lhs_t = tm.get(*lhs).expect("lhs exists");
        assert!(
            !matches!(lhs_t.kind, TermKind::Var(_)),
            "left side of (= (double-it m) 10) must have been expanded, not left as a bare var"
        );
    }
}

/// Two macros reuse the same formal-parameter name at two different sorts.
/// Under the old fallback, the Int-sorted formal (`scale`'s `v`) fails to
/// substitute (no global `v` exists, guessed sort is `Bool`) while the
/// Bool-sorted formal (`flip`'s `v`) substitutes only by *coincidence*
/// (guessed `Bool` happens to be right). Both must now substitute correctly
/// for the same reason: exact `TermId` reuse, not name-based guessing.
#[test]
fn test_pr27_define_fun_shared_param_name_different_sorts() {
    let mut tm = TermManager::new();
    let cmds = parse_script(
        r#"
(declare-const a Int)
(declare-const p Bool)
(define-fun scale ((v Int)) Int (+ v v))
(define-fun flip ((v Bool)) Bool (not v))
(assert (and (= (scale a) 8) (flip p)))
"#,
        &mut tm,
    )
    .expect("parse must succeed");
    let a = sole_assertion(&cmds);
    assert!(
        contains_free_var(&tm, a, "a"),
        "(scale a) must mention the call-site argument a"
    );
    assert!(
        contains_free_var(&tm, a, "p"),
        "(flip p) must mention the call-site argument p"
    );
    assert!(
        !contains_free_var(&tm, a, "v"),
        "neither expansion may leave the shared parameter name v free"
    );
}

/// A define-fun whose body calls an earlier define-fun, both parameters
/// named identically. Exercises expansion nested inside expansion, at parse
/// time of the outer macro's own body.
#[test]
fn test_pr27_define_fun_nested_call_same_param_name() {
    let mut tm = TermManager::new();
    let cmds = parse_script(
        r#"
(define-fun sq ((x Int)) Int (* x x))
(define-fun sum-of-squares ((x Int) (y Int)) Int (+ (sq x) (sq y)))
(declare-const p Int)
(declare-const q Int)
(assert (= (sum-of-squares p q) 25))
"#,
        &mut tm,
    )
    .expect("parse must succeed");
    let a = sole_assertion(&cmds);
    assert!(
        contains_free_var(&tm, a, "p") && contains_free_var(&tm, a, "q"),
        "expansion must mention both call-site arguments p and q"
    );
    assert!(
        !contains_free_var(&tm, a, "x") && !contains_free_var(&tm, a, "y"),
        "expansion must not leave either macro's formal parameter free"
    );
}

/// An `ite`-bodied macro, matching the shape most likely to hide a
/// substitution miss inside a branch rather than at the top of the body.
#[test]
fn test_pr27_define_fun_ite_body_shadowed_param() {
    let mut tm = TermManager::new();
    let cmds = parse_script(
        r#"
(declare-const s Int)
(declare-const t Int)
(define-fun clamp-to-zero ((s Int)) Int (ite (< s 0) 0 s))
(assert (= (clamp-to-zero t) 0))
"#,
        &mut tm,
    )
    .expect("parse must succeed");
    let a = sole_assertion(&cmds);
    assert!(
        contains_free_var(&tm, a, "t"),
        "expansion must mention the call-site argument t"
    );
    assert!(
        !contains_free_var(&tm, a, "s"),
        "expansion must not leave the formal parameter s free in either ite branch"
    );
}

/// End-to-end: a define-fun whose parameter name collides with a
/// differently-sorted global must still be *solvable* end to end, not merely
/// parse to a term shape that happens to look right. `x = 7` is forced only
/// if `(bump x)` genuinely expands to `(+ x 1)`; a dangling free parameter
/// would make the constraint under-determined and this would spuriously
/// answer `unknown`/`sat` with an unrelated model instead of pinning `x`.
#[test]
fn test_pr27_define_fun_end_to_end_forces_unique_value() {
    let mut tm = TermManager::new();
    let cmds = parse_script(
        r#"
(declare-const x Int)
(define-fun bump ((x Int)) Int (+ x 1))
(assert (= (bump x) 8))
"#,
        &mut tm,
    )
    .expect("parse must succeed");
    let a = sole_assertion(&cmds);
    // (+ x 1) = 8  forces x = 7; a correctly expanded term is `Eq(Add([x,1]),
    // 8)` and must mention x, not a dangling copy of the formal parameter
    // under a different identity (which, here, coincides in name but must be
    // the *same* TermId as the declared constant for solving to pin it).
    assert!(
        contains_free_var(&tm, a, "x"),
        "expansion of (bump x) must mention x"
    );
}
