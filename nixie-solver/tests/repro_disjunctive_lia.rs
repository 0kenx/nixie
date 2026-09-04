//! Reproduction of soundness bug: disjunctive LIA formula wrongly UNSAT.

use nixie_solver::Context;
use nixie_solver::SolverResult;

fn check_str(res: SolverResult) -> &'static str {
    match res {
        SolverResult::Sat => "Sat",
        SolverResult::Unsat => "Unsat",
        SolverResult::Unknown => "Unknown",
    }
}

// Regression: wrong UNSAT on a satisfiable disjunctive LIA chain.
//
// x0 = 0 ∧ (x1 = x0+1 ∨ x1 = x0-1) ∧ (x2 = x1+1 ∨ x2 = x1-1) ∧ x2 = 2 is SAT
// (x1 = 1, x2 = 2), but the solver used to answer Unsat.  The SAT core's
// conflict analysis can compute a wrong backtrack level and overwrite a decision
// literal's polarity in place, leaving the incremental EUF/arith state reflecting
// the stale polarity and manufacturing a spurious theory conflict that collapses
// the whole search to a wrong top-level UNSAT.  The theory manager now shadows
// every theory assignment, detects the in-place flip, and rebuilds theory state
// from the corrected trail (see `TheoryManager::resync_theory_state`).
#[test]
fn test_repro_disjunctive_lia_sat() {
    let mut ctx = Context::new();
    let _ = ctx.set_logic("QF_LIA");

    let int_sort = ctx.terms.sorts.int_sort;
    let x0 = ctx.declare_const("x0", int_sort);
    let x1 = ctx.declare_const("x1", int_sort);
    let x2 = ctx.declare_const("x2", int_sort);

    let zero = ctx.terms.mk_int(0);
    let one = ctx.terms.mk_int(1);
    let two = ctx.terms.mk_int(2);

    let c0 = ctx.terms.mk_eq(x0, zero);
    ctx.assert(c0);

    let x0p1 = ctx.terms.mk_add(vec![x0, one]);
    let x0m1 = ctx.terms.mk_sub(x0, one);
    let x1_eq_p = ctx.terms.mk_eq(x1, x0p1);
    let x1_eq_m = ctx.terms.mk_eq(x1, x0m1);
    let d1 = ctx.terms.mk_or(vec![x1_eq_p, x1_eq_m]);
    ctx.assert(d1);

    let x1p1 = ctx.terms.mk_add(vec![x1, one]);
    let x1m1 = ctx.terms.mk_sub(x1, one);
    let x2_eq_p = ctx.terms.mk_eq(x2, x1p1);
    let x2_eq_m = ctx.terms.mk_eq(x2, x1m1);
    let d2 = ctx.terms.mk_or(vec![x2_eq_p, x2_eq_m]);
    ctx.assert(d2);

    let c2 = ctx.terms.mk_eq(x2, two);
    ctx.assert(c2);

    let result = ctx.check_sat();
    assert!(
        matches!(result, SolverResult::Sat),
        "Expected SAT (x1=1, x2=2), got {}",
        check_str(result)
    );
}

// Simpler: one disjunction
#[test]
fn test_one_disjunction() {
    let mut ctx = Context::new();
    let _ = ctx.set_logic("QF_LIA");
    let int_sort = ctx.terms.sorts.int_sort;
    let x0 = ctx.declare_const("x0", int_sort);
    let x1 = ctx.declare_const("x1", int_sort);
    let zero = ctx.terms.mk_int(0);
    let one = ctx.terms.mk_int(1);

    let c0 = ctx.terms.mk_eq(x0, zero);
    ctx.assert(c0);
    let x0p1 = ctx.terms.mk_add(vec![x0, one]);
    let x0m1 = ctx.terms.mk_sub(x0, one);
    let a = ctx.terms.mk_eq(x1, x0p1);
    let b = ctx.terms.mk_eq(x1, x0m1);
    let d1 = ctx.terms.mk_or(vec![a, b]);
    ctx.assert(d1);
    // x1 = 1 forces the first arm
    let x1eq1 = ctx.terms.mk_eq(x1, one);
    ctx.assert(x1eq1);

    let result = ctx.check_sat();
    assert!(
        matches!(result, SolverResult::Sat),
        "one_disjunction expected SAT, got {}",
        check_str(result)
    );
}

// Disjunction where the second arm is forced
#[test]
fn test_one_disjunction_second_arm() {
    let mut ctx = Context::new();
    let _ = ctx.set_logic("QF_LIA");
    let int_sort = ctx.terms.sorts.int_sort;
    let x0 = ctx.declare_const("x0", int_sort);
    let x1 = ctx.declare_const("x1", int_sort);
    let zero = ctx.terms.mk_int(0);
    let one = ctx.terms.mk_int(1);
    let neg1 = ctx.terms.mk_int(-1);

    let c0 = ctx.terms.mk_eq(x0, zero);
    ctx.assert(c0);
    let x0p1 = ctx.terms.mk_add(vec![x0, one]);
    let x0m1 = ctx.terms.mk_sub(x0, one);
    let a = ctx.terms.mk_eq(x1, x0p1);
    let b = ctx.terms.mk_eq(x1, x0m1);
    let d1 = ctx.terms.mk_or(vec![a, b]);
    ctx.assert(d1);
    // x1 = -1 forces the second arm
    let x1eqm1 = ctx.terms.mk_eq(x1, neg1);
    ctx.assert(x1eqm1);

    let result = ctx.check_sat();
    assert!(
        matches!(result, SolverResult::Sat),
        "one_disjunction_second_arm expected SAT, got {}",
        check_str(result)
    );
}

// Two disjunctions but no final equality constraint (trivially SAT)
#[test]
fn test_two_disjunctions_free() {
    let mut ctx = Context::new();
    let _ = ctx.set_logic("QF_LIA");
    let int_sort = ctx.terms.sorts.int_sort;
    let x0 = ctx.declare_const("x0", int_sort);
    let x1 = ctx.declare_const("x1", int_sort);
    let x2 = ctx.declare_const("x2", int_sort);
    let zero = ctx.terms.mk_int(0);
    let one = ctx.terms.mk_int(1);

    let c0 = ctx.terms.mk_eq(x0, zero);
    ctx.assert(c0);
    let x0p1 = ctx.terms.mk_add(vec![x0, one]);
    let x0m1 = ctx.terms.mk_sub(x0, one);
    let a = ctx.terms.mk_eq(x1, x0p1);
    let b = ctx.terms.mk_eq(x1, x0m1);
    let d1 = ctx.terms.mk_or(vec![a, b]);
    ctx.assert(d1);
    let x1p1 = ctx.terms.mk_add(vec![x1, one]);
    let x1m1 = ctx.terms.mk_sub(x1, one);
    let c = ctx.terms.mk_eq(x2, x1p1);
    let e = ctx.terms.mk_eq(x2, x1m1);
    let d2 = ctx.terms.mk_or(vec![c, e]);
    ctx.assert(d2);

    let result = ctx.check_sat();
    assert!(
        matches!(result, SolverResult::Sat),
        "two_disjunctions_free expected SAT, got {}",
        check_str(result)
    );
}

// Pure conjunction, no disjunction: exposes arith combination order issue.
#[test]
fn test_conjunction_chain() {
    let mut ctx = Context::new();
    let _ = ctx.set_logic("QF_LIA");
    let int_sort = ctx.terms.sorts.int_sort;
    let x0 = ctx.declare_const("x0", int_sort);
    let x1 = ctx.declare_const("x1", int_sort);
    let x2 = ctx.declare_const("x2", int_sort);
    let zero = ctx.terms.mk_int(0);
    let one = ctx.terms.mk_int(1);
    let two = ctx.terms.mk_int(2);

    let c0 = ctx.terms.mk_eq(x0, zero);
    ctx.assert(c0);
    let c2 = ctx.terms.mk_eq(x2, two);
    ctx.assert(c2);
    // x2 = x1 + 1
    let x1p1 = ctx.terms.mk_add(vec![x1, one]);
    let e1 = ctx.terms.mk_eq(x2, x1p1);
    ctx.assert(e1);
    // x1 = x0 + 1
    let x0p1 = ctx.terms.mk_add(vec![x0, one]);
    let e2 = ctx.terms.mk_eq(x1, x0p1);
    ctx.assert(e2);

    let result = ctx.check_sat();
    assert!(
        matches!(result, SolverResult::Sat),
        "conjunction_chain expected SAT (x1=1,x2=2), got {}",
        check_str(result)
    );
}

// ========  ========
// Regression tests for the O(n^2) -> O(n) rewrite of `model_based_combination`
// (theory_manager.rs).  These exercise the EUF <-> arithmetic interface: EUF
// congruence closure equates two arithmetic-valued terms and the arithmetic
// solver must agree on / disagree with their values.
// ========  ========

// a = b forces f(a) = f(b) by congruence; the arithmetic bounds on f(a) and
// f(b) are then jointly contradictory ( >=5 and <=3 for the same value ).
#[test]
fn test_euf_arith_interface_unsat() {
    let mut ctx = Context::new();
    let _ = ctx.set_logic("QF_UFLIA");
    let int_sort = ctx.terms.sorts.int_sort;

    ctx.declare_fun("f", vec![int_sort], int_sort);
    let a = ctx.declare_const("a", int_sort);
    let b = ctx.declare_const("b", int_sort);

    let a_eq_b = ctx.terms.mk_eq(a, b);
    ctx.assert(a_eq_b);

    let fa = ctx.terms.mk_apply("f", [a], int_sort);
    let fb = ctx.terms.mk_apply("f", [b], int_sort);
    let five = ctx.terms.mk_int(5);
    let three = ctx.terms.mk_int(3);
    let fa_ge_5 = ctx.terms.mk_ge(fa, five);
    let fb_le_3 = ctx.terms.mk_le(fb, three);
    ctx.assert(fa_ge_5);
    ctx.assert(fb_le_3);

    let result = ctx.check_sat();
    assert!(
        matches!(result, SolverResult::Unsat),
        "euf_arith_interface expected UNSAT (a=b => f(a)=f(b), 5<=f(a)=f(b)<=3), got {}",
        check_str(result)
    );
}

// Same shape but with satisfiable bounds: f(a) = f(b) in [5, 10] is fine.
#[test]
fn test_euf_arith_interface_sat() {
    let mut ctx = Context::new();
    let _ = ctx.set_logic("QF_UFLIA");
    let int_sort = ctx.terms.sorts.int_sort;

    ctx.declare_fun("f", vec![int_sort], int_sort);
    let a = ctx.declare_const("a", int_sort);
    let b = ctx.declare_const("b", int_sort);

    let a_eq_b = ctx.terms.mk_eq(a, b);
    ctx.assert(a_eq_b);

    let fa = ctx.terms.mk_apply("f", [a], int_sort);
    let fb = ctx.terms.mk_apply("f", [b], int_sort);
    let five = ctx.terms.mk_int(5);
    let ten = ctx.terms.mk_int(10);
    let fa_ge_5 = ctx.terms.mk_ge(fa, five);
    let fb_le_10 = ctx.terms.mk_le(fb, ten);
    ctx.assert(fa_ge_5);
    ctx.assert(fb_le_10);

    let result = ctx.check_sat();
    assert!(
        matches!(result, SolverResult::Sat),
        "euf_arith_interface_sat expected SAT, got {}",
        check_str(result)
    );
}

// ========  ========
// Randomized cross-check: small disjunctive LIA formulas vs. brute force.
//
// Each formula is a chain `x0 = c0`, then for every i `(x_i = x_{i-1} + p_i) ∨
// (x_i = x_{i-1} + q_i)`, plus a handful of filter constraints (`= c`, `<= c`,
// `>= c`) on individual variables.  Because every variable's value is fully
// determined by `x0` and the sequence of arm choices, the entire model space is
// exactly the `2^(k-1)` arm combinations – so brute-force enumeration of those
// combinations is an EXACT decision procedure (no finite-domain truncation), and
// we can assert the solver's Sat/Unsat verdict matches it on every instance.
// This is precisely the disjunction/backtrack ↔ LIA interaction that produced
// the wrong-UNSAT soundness bug.
// ========  ========

/// Minimal deterministic PRNG (SplitMix64) – no external `rand` dependency.
struct Rng(u64);
impl Rng {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    /// Uniform integer in `lo..=hi`.
    fn in_range(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i64
    }
}

/// One filter atom on a single variable, evaluated over a concrete assignment.
#[derive(Clone, Copy, Debug)]
enum Filter {
    Eq(usize, i64),
    Le(usize, i64),
    Ge(usize, i64),
}

/// A generated disjunctive-LIA instance with an exact Rust semantics.
struct Instance {
    k: usize,
    c0: i64,
    /// `arms[i]` holds `(p, q)` for the disjunction defining `x_{i+1}`.
    arms: Vec<(i64, i64)>,
    filters: Vec<Filter>,
}

impl Instance {
    fn generate(rng: &mut Rng) -> Self {
        let k = rng.in_range(2, 4) as usize;
        let c0 = rng.in_range(-3, 3);
        let arms: Vec<(i64, i64)> = (1..k)
            .map(|_| (rng.in_range(-2, 2), rng.in_range(-2, 2)))
            .collect();
        // Endpoint constraint on the last variable – the exact shape of the
        // original soundness bug (…∧ x_{k-1} = target). Half the time we drop
        // it (a trivially-satisfiable chain); otherwise pin the endpoint with
        // an equality, upper bound, or lower bound, chosen at random so every
        // `Filter` variant documented above (`= c`, `<= c`, `>= c`) is
        // actually generated and checked, not just `Eq`.
        let filters = if rng.in_range(0, 1) == 0 {
            Vec::new()
        } else {
            let c = rng.in_range(-6, 8);
            let filter = match rng.in_range(0, 2) {
                0 => Filter::Eq(k - 1, c),
                1 => Filter::Le(k - 1, c),
                _ => Filter::Ge(k - 1, c),
            };
            vec![filter]
        };
        Self {
            k,
            c0,
            arms,
            filters,
        }
    }

    /// Brute-force: is there an arm combination whose induced assignment
    /// satisfies every filter?  Exact because each combination fixes all values.
    fn brute_force_sat(&self) -> bool {
        let combos = 1usize << (self.k - 1);
        'combo: for mask in 0..combos {
            let mut vals = vec![self.c0];
            for (i, &(p, q)) in self.arms.iter().enumerate() {
                let delta = if (mask >> i) & 1 == 0 { p } else { q };
                vals.push(vals[i] + delta);
            }
            for f in &self.filters {
                let ok = match *f {
                    Filter::Eq(v, c) => vals[v] == c,
                    Filter::Le(v, c) => vals[v] <= c,
                    Filter::Ge(v, c) => vals[v] >= c,
                };
                if !ok {
                    continue 'combo;
                }
            }
            return true;
        }
        false
    }

    /// Build and solve the same instance through the full solver.
    fn solve(&self) -> SolverResult {
        let mut ctx = Context::new();
        let _ = ctx.set_logic("QF_LIA");
        let int_sort = ctx.terms.sorts.int_sort;
        let xs: Vec<_> = (0..self.k)
            .map(|i| ctx.declare_const(&format!("x{i}"), int_sort))
            .collect();

        let c0 = ctx.terms.mk_int(self.c0);
        let a0 = ctx.terms.mk_eq(xs[0], c0);
        ctx.assert(a0);

        for (i, &(p, q)) in self.arms.iter().enumerate() {
            let pc = ctx.terms.mk_int(p);
            let qc = ctx.terms.mk_int(q);
            let src_p = ctx.terms.mk_add(vec![xs[i], pc]);
            let src_q = ctx.terms.mk_add(vec![xs[i], qc]);
            let arm_p = ctx.terms.mk_eq(xs[i + 1], src_p);
            let arm_q = ctx.terms.mk_eq(xs[i + 1], src_q);
            let disj = ctx.terms.mk_or(vec![arm_p, arm_q]);
            ctx.assert(disj);
        }

        for f in &self.filters {
            let atom = match *f {
                Filter::Eq(v, c) => {
                    let cc = ctx.terms.mk_int(c);
                    ctx.terms.mk_eq(xs[v], cc)
                }
                Filter::Le(v, c) => {
                    let cc = ctx.terms.mk_int(c);
                    ctx.terms.mk_le(xs[v], cc)
                }
                Filter::Ge(v, c) => {
                    let cc = ctx.terms.mk_int(c);
                    ctx.terms.mk_ge(xs[v], cc)
                }
            };
            ctx.assert(atom);
        }

        ctx.check_sat()
    }
}

#[test]
fn test_random_disjunctive_lia_vs_brute_force() {
    let mut rng = Rng(0xC0FF_EE12_3456_789A);
    let mut checked = 0usize;
    let mut unknown = 0usize;
    let mut wrong = 0usize;

    for _ in 0..400 {
        let inst = Instance::generate(&mut rng);
        let expected_sat = inst.brute_force_sat();
        match inst.solve() {
            // SOUNDNESS: every DECIDED verdict must agree with the exact
            // brute-force enumeration.  This is the property the wrong-UNSAT bug
            // violated and must never regress.
            SolverResult::Sat => {
                if !expected_sat {
                    wrong += 1;
                }
            }
            SolverResult::Unsat => {
                if expected_sat {
                    wrong += 1;
                }
            }
            // `Unknown` is honest – the model-verification gate refusing to trust
            // a model the SAT core built over an inconsistent trail – but on this
            // fragment it must never be needed.  Every instance here is decidable
            // by construction, so a single `Unknown` means the CDCL(T) loop again
            // produced a model that `model_refutes_assertions` had to reject.
            // That is exactly what the propagation-fixpoint bug did (57 of these
            // 400 instances); see `nixie-sat`'s
            // `cdclt_propagation_fixpoint_soundness` regression suite.
            SolverResult::Unknown => {
                unknown += 1;
                continue;
            }
        }
        checked += 1;
    }
    assert_eq!(
        wrong, 0,
        "UNSOUND: {wrong} verdict(s) disagreed with brute force (checked={checked}, unknown={unknown})"
    );
    assert_eq!(
        unknown, 0,
        "every instance in this fragment is decidable: {unknown} Unknown verdict(s) mean the \
         CDCL(T) search handed up a model the soundness gate had to refuse (checked={checked})"
    );
}

// ========  ========
// Regression: the CDCL(T) propagation-fixpoint bug, reduced.
//
// This is the smallest instance of the generated family above that made
// `nixie_sat::Solver::solve_with_theory` answer `Sat` over a *total* model
// falsifying an original ternary clause whose three literals were all pinned
// false at level 0.  `Context::check_sat` only escaped a wrong `Sat` because
// `model_refutes_assertions` rejected the model and downgraded it to `Unknown`.
//
//   x0 = -1 ∧ (x1 = x0 + -1 ∨ x1 = x0 + 0) ∧ (x2 = x1 + -1 ∨ x2 = x1 + 0) ∧ x2 = 0
//
// x1 ∈ {-2,-1} and x2 ∈ {x1-1, x1}, so x2 ≤ -1 and `x2 = 0` is unreachable: the
// only sound verdict is UNSAT.
// ========  ========
#[test]
fn test_cdclt_propagation_fixpoint_regression_unsat() {
    let mut ctx = Context::new();
    let _ = ctx.set_logic("QF_LIA");
    let int_sort = ctx.terms.sorts.int_sort;
    let xs: Vec<_> = (0..3)
        .map(|i| ctx.declare_const(&format!("x{i}"), int_sort))
        .collect();

    let minus_one = ctx.terms.mk_int(-1);
    let zero = ctx.terms.mk_int(0);

    let a0 = ctx.terms.mk_eq(xs[0], minus_one);
    ctx.assert(a0);

    for i in 0..2 {
        let dec = ctx.terms.mk_add(vec![xs[i], minus_one]);
        let same = ctx.terms.mk_add(vec![xs[i], zero]);
        let arm_dec = ctx.terms.mk_eq(xs[i + 1], dec);
        let arm_same = ctx.terms.mk_eq(xs[i + 1], same);
        let disj = ctx.terms.mk_or(vec![arm_dec, arm_same]);
        ctx.assert(disj);
    }

    let endpoint = ctx.terms.mk_eq(xs[2], zero);
    ctx.assert(endpoint);

    let result = ctx.check_sat();
    assert!(
        matches!(result, SolverResult::Unsat),
        "x2 ≤ -1 on every arm choice, so x2 = 0 is unsatisfiable; got {}",
        check_str(result)
    );
}

// Companion of the above: the satisfiable endpoint on the same chain must be
// decided `Sat`, and the model must genuinely satisfy every assertion.  This is
// the model-validity half of the contract – a `Sat` from the CDCL(T) path is
// worthless if the assignment behind it does not satisfy the input.
#[test]
fn test_cdclt_propagation_fixpoint_regression_sat_model_is_valid() {
    let mut ctx = Context::new();
    let _ = ctx.set_logic("QF_LIA");
    let int_sort = ctx.terms.sorts.int_sort;
    let xs: Vec<_> = (0..3)
        .map(|i| ctx.declare_const(&format!("x{i}"), int_sort))
        .collect();

    let minus_one = ctx.terms.mk_int(-1);
    let zero = ctx.terms.mk_int(0);
    let minus_two = ctx.terms.mk_int(-2);

    let a0 = ctx.terms.mk_eq(xs[0], minus_one);
    ctx.assert(a0);
    for i in 0..2 {
        let dec = ctx.terms.mk_add(vec![xs[i], minus_one]);
        let same = ctx.terms.mk_add(vec![xs[i], zero]);
        let arm_dec = ctx.terms.mk_eq(xs[i + 1], dec);
        let arm_same = ctx.terms.mk_eq(xs[i + 1], same);
        let disj = ctx.terms.mk_or(vec![arm_dec, arm_same]);
        ctx.assert(disj);
    }
    // x2 = -2 is reachable (one "same" arm and one "-1" arm, in either order).
    let endpoint = ctx.terms.mk_eq(xs[2], minus_two);
    ctx.assert(endpoint);

    let result = ctx.check_sat();
    assert!(
        matches!(result, SolverResult::Sat),
        "x2 = -2 is reachable on this chain; got {}",
        check_str(result)
    );

    // Every assertion must evaluate to true under the reported model.
    let model = ctx.get_model().expect("Sat must come with a model");
    let values: Vec<i64> = (0..3)
        .map(|i| {
            let name = format!("x{i}");
            let raw = &model
                .iter()
                .find(|(n, _, _)| *n == name)
                .unwrap_or_else(|| panic!("{name} must appear in the model"))
                .2;
            // SMT-LIB renders negative integers as `(- n)`.
            let text = raw.trim();
            let parsed = if let Some(rest) = text.strip_prefix("(-") {
                let digits = rest.trim_end_matches(')').trim();
                digits.parse::<i64>().map(|v| -v)
            } else {
                text.parse::<i64>()
            };
            parsed.unwrap_or_else(|_| panic!("{name} = {text:?} is not an integer literal"))
        })
        .collect();
    assert_eq!(values[0], -1, "x0 = -1 is asserted");
    assert_eq!(values[2], -2, "x2 = -2 is asserted");
    for i in 0..2 {
        let delta = values[i + 1] - values[i];
        assert!(
            delta == -1 || delta == 0,
            "x{} - x{i} must be -1 or 0 (the two disjuncts), got {delta}",
            i + 1
        );
    }
}
