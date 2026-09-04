//! Regression tests for audited soundness defects in `AggressiveSimplifier`'s
//! Boolean absorption / factoring rules.
//!
//! Findings fixed (see nixie-core/src/simplification/mod.rs):
//!   1. `try_boolean_absorption_in_and` used to collapse
//!      `And(a, Or(a,b), c)` down to just `a`, silently dropping `c`
//!      (an UNSAT formula, e.g. c=false, was reported SAT).
//!   2. `try_boolean_absorption_in_or` used to collapse
//!      `Or(a, And(a,b), c)` down to just `a`, silently dropping `c`
//!      (a SAT formula, e.g. c=true & a=false, was reported UNSAT).
//!   3. `try_factor_or_of_ands` used to collapse
//!      `Or(And(x,a), And(x,b), c)` down to `And(x, Or(a,b))`, dropping `c`
//!      and strengthening the formula (SAT -> UNSAT).
//!
//! Each defect is covered by (a) a direct regression test reproducing the exact
//! audit example, and (b) a property test that brute-force-checks truth-table
//! equivalence between the unsimplified and aggressively-simplified form of many
//! small random Boolean formulas over up to 4 variables.

use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::simplification::{AggressiveSimplifier, SimplificationConfig};
use std::collections::HashMap;

fn aggressive_config() -> SimplificationConfig {
    SimplificationConfig { aggressive: true }
}

/// Evaluate a Boolean term (built only from True/False/Var/Not/And/Or) under the
/// given variable assignment. Used purely by tests as a brute-force oracle -- this
/// is intentionally independent of any production simplification/evaluation code.
fn eval_bool(manager: &TermManager, term: TermId, assignment: &HashMap<TermId, bool>) -> bool {
    match manager.get(term).map(|t| &t.kind) {
        Some(TermKind::True) => true,
        Some(TermKind::False) => false,
        Some(TermKind::Var(_)) => *assignment
            .get(&term)
            .unwrap_or_else(|| panic!("unassigned variable in eval_bool")),
        Some(TermKind::Not(arg)) => !eval_bool(manager, *arg, assignment),
        Some(TermKind::And(args)) => args.iter().all(|&a| eval_bool(manager, a, assignment)),
        Some(TermKind::Or(args)) => args.iter().any(|&a| eval_bool(manager, a, assignment)),
        other => panic!("eval_bool: unsupported term kind {other:?}"),
    }
}

// ========  ========
// Finding 1 -- And absorption must keep all other conjuncts.
// ========  ========

#[test]
fn and_absorption_keeps_other_conjuncts() {
    let mut manager = TermManager::new();
    let bool_sort = manager.sorts.bool_sort;
    let a = manager.mk_var("a", bool_sort);
    let b = manager.mk_var("b", bool_sort);
    let c = manager.mk_var("c", bool_sort);

    // And(a, Or(a, b), c)
    let or_ab = manager.mk_or([a, b]);
    let and_term = manager.mk_and([a, or_ab, c]);

    let result = {
        let mut simplifier = AggressiveSimplifier::new(&mut manager, aggressive_config());
        simplifier.simplify_term(and_term)
    };

    // a=true, c=false must make the simplified result false too (c must not be dropped).
    let mut assignment = HashMap::new();
    assignment.insert(a, true);
    assignment.insert(b, false);
    assignment.insert(c, false);

    assert!(
        !eval_bool(&manager, result, &assignment),
        "And(a, Or(a,b), c) with c=false must simplify to something false, \
         but conjunct `c` was dropped (absorption bug)"
    );

    // And a=true, b=true, c=true must be true.
    assignment.insert(b, true);
    assignment.insert(c, true);
    assert!(eval_bool(&manager, result, &assignment));
}

// ========  ========
// Finding 2 -- Or absorption must keep all other disjuncts.
// ========  ========

#[test]
fn or_absorption_keeps_other_disjuncts() {
    let mut manager = TermManager::new();
    let bool_sort = manager.sorts.bool_sort;
    let a = manager.mk_var("a", bool_sort);
    let b = manager.mk_var("b", bool_sort);
    let c = manager.mk_var("c", bool_sort);

    // Or(a, And(a, b), c)
    let and_ab = manager.mk_and([a, b]);
    let or_term = manager.mk_or([a, and_ab, c]);

    let result = {
        let mut simplifier = AggressiveSimplifier::new(&mut manager, aggressive_config());
        simplifier.simplify_term(or_term)
    };

    // a=false, b=false, c=true must make the simplified result true too
    // (disjunct `c` must not be dropped).
    let mut assignment = HashMap::new();
    assignment.insert(a, false);
    assignment.insert(b, false);
    assignment.insert(c, true);

    assert!(
        eval_bool(&manager, result, &assignment),
        "Or(a, And(a,b), c) with a=false,c=true must simplify to something true, \
         but disjunct `c` was dropped (absorption bug)"
    );

    // a=false, b=false, c=false must be false.
    assignment.insert(c, false);
    assert!(!eval_bool(&manager, result, &assignment));
}

// ========  ========
// Finding 3 -- factoring Or-of-Ands must keep untouched disjuncts.
// ========  ========

#[test]
fn factor_or_of_ands_keeps_other_disjuncts() {
    let mut manager = TermManager::new();
    let bool_sort = manager.sorts.bool_sort;
    let x = manager.mk_var("x", bool_sort);
    let a = manager.mk_var("a", bool_sort);
    let b = manager.mk_var("b", bool_sort);
    let c = manager.mk_var("c", bool_sort);

    // Or(And(x,a), And(x,b), c)
    let and_xa = manager.mk_and([x, a]);
    let and_xb = manager.mk_and([x, b]);
    let or_term = manager.mk_or([and_xa, and_xb, c]);

    let result = {
        let mut simplifier = AggressiveSimplifier::new(&mut manager, aggressive_config());
        simplifier.simplify_term(or_term)
    };

    // x=false, c=true must still be satisfiable (true) in the simplified form.
    let mut assignment = HashMap::new();
    assignment.insert(x, false);
    assignment.insert(a, false);
    assignment.insert(b, false);
    assignment.insert(c, true);

    assert!(
        eval_bool(&manager, result, &assignment),
        "Or(And(x,a), And(x,b), c) with x=false,c=true must remain true, \
         but disjunct `c` was dropped by the factoring rule"
    );

    // x=false, c=false must be false.
    assignment.insert(c, false);
    assert!(!eval_bool(&manager, result, &assignment));

    // x=true, a=true (b irrelevant), c=false must be true via the factored branch.
    assignment.insert(x, true);
    assignment.insert(a, true);
    assignment.insert(b, false);
    assignment.insert(c, false);
    assert!(eval_bool(&manager, result, &assignment));
}

// ========  ========
// Property test: brute-force truth-table equivalence over small random formulas.
// ========  ========

/// A tiny deterministic xorshift-style PRNG so the property test has no new
/// dependency and is fully reproducible.
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed | 1)
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    fn next_range(&mut self, n: usize) -> usize {
        (self.next_u64() % n as u64) as usize
    }
}

/// Randomly build a small Boolean formula over `vars` using And/Or/Not, up to
/// `depth` levels deep.
fn random_formula(manager: &mut TermManager, vars: &[TermId], rng: &mut Rng, depth: u32) -> TermId {
    if depth == 0 || rng.next_range(4) == 0 {
        return vars[rng.next_range(vars.len())];
    }

    match rng.next_range(3) {
        0 => {
            let n = 2 + rng.next_range(2); // 2 or 3 args
            let args: Vec<TermId> = (0..n)
                .map(|_| random_formula(manager, vars, rng, depth - 1))
                .collect();
            manager.mk_and(args)
        }
        1 => {
            let n = 2 + rng.next_range(2);
            let args: Vec<TermId> = (0..n)
                .map(|_| random_formula(manager, vars, rng, depth - 1))
                .collect();
            manager.mk_or(args)
        }
        _ => {
            let inner = random_formula(manager, vars, rng, depth - 1);
            manager.mk_not(inner)
        }
    }
}

#[test]
fn aggressive_simplify_preserves_truth_table_on_random_formulas() {
    let num_vars = 4;
    let num_formulas = 300;

    for seed in 0..num_formulas {
        let mut manager = TermManager::new();
        let bool_sort = manager.sorts.bool_sort;
        let vars: Vec<TermId> = (0..num_vars)
            .map(|i| manager.mk_var(&format!("v{i}"), bool_sort))
            .collect();

        let mut rng = Rng::new(0x9E37_79B9_7F4A_7C15 ^ (seed as u64 + 1));
        let original = random_formula(&mut manager, &vars, &mut rng, 4);

        let simplified = {
            let mut simplifier = AggressiveSimplifier::new(&mut manager, aggressive_config());
            simplifier.simplify_term(original)
        };

        // Brute-force every assignment of the (<=4) Boolean variables and check
        // that the simplified formula agrees with the original on every one.
        for mask in 0u32..(1 << num_vars) {
            let mut assignment = HashMap::new();
            for (i, &v) in vars.iter().enumerate() {
                assignment.insert(v, (mask >> i) & 1 == 1);
            }

            let original_value = eval_bool(&manager, original, &assignment);
            let simplified_value = eval_bool(&manager, simplified, &assignment);

            assert_eq!(
                original_value, simplified_value,
                "seed={seed} mask={mask:#06b}: aggressive simplification changed \
                 truth value (original={original_value}, simplified={simplified_value})"
            );
        }
    }
}
