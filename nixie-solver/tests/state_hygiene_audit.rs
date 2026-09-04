//! Audit harness for the task-#26 `rebase_theory_state` seam.
//!
//! Every property here is a consequence of the rebase claim "the state the next
//! search is entitled to is exactly the facts implied by the root-level SAT
//! trail": if that holds, an interposed `(check-sat)`, a repeated
//! `(check-sat)`, and a `(push)`/`(pop)` bracket can none of them change a
//! verdict, and a model reported after any of them must still satisfy the
//! assertions.

use nixie_solver::Context;

/// Run a script on a fresh context and return the responses.
fn run(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script)
        .unwrap_or_else(|e| panic!("script failed: {e}\n{script}"))
}

/// The verdict lines of a script, in order.
fn verdicts(script: &str) -> Vec<String> {
    run(script)
        .into_iter()
        .filter(|l| l == "sat" || l == "unsat" || l == "unknown")
        .collect()
}

/// A deterministic small-state PRNG (no external dependency).
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// Build a random conjunction of small LIA / UF assertions over `x`, `y`, `z`.
fn random_assertions(rng: &mut Rng, count: usize) -> Vec<String> {
    let vars = ["x", "y", "z"];
    let mut out = Vec::with_capacity(count);
    for _ in 0..count {
        let a = vars[rng.below(3) as usize];
        let b = vars[rng.below(3) as usize];
        let k = rng.below(9) as i64 - 4;
        let shape = rng.below(7);
        out.push(match shape {
            0 => format!("(assert (= {a} {k}))"),
            1 => format!("(assert (<= (+ {a} {b}) {k}))"),
            2 => format!("(assert (>= (- {a} {b}) {k}))"),
            3 => format!("(assert (or (= {a} {k}) (= {b} {k})))"),
            4 => format!("(assert (= (f {a}) {k}))"),
            5 => format!("(assert (not (= (f {a}) (f {b}))))"),
            _ => format!("(assert (> {a} {k}))"),
        });
    }
    out
}

const PREAMBLE: &str = "(set-logic UFLIA)\n(declare-fun f (Int) Int)\n\
                        (declare-const x Int)\n(declare-const y Int)\n\
                        (declare-const z Int)\n";

/// A second `(check-sat)` on an unchanged assertion set must repeat the first
/// verdict.  This is the direct observable of the `check_core`-entry rebase: the
/// previous check ends `Sat` without backtracking, so whatever it leaves in the
/// theory solvers is what the next check would otherwise start from.
#[test]
fn repeated_check_sat_is_stable_over_random_lia_uf_goals() {
    let mut rng = Rng(0x5eed_1234_9abc_def1);
    for case in 0..400 {
        let asserts = random_assertions(&mut rng, 4).join("\n");
        let script = format!("{PREAMBLE}{asserts}\n(check-sat)\n(check-sat)\n(check-sat)\n");
        let got = verdicts(&script);
        assert_eq!(
            got.len(),
            3,
            "case {case}: expected three verdicts\n{script}"
        );
        assert!(
            got[0] == got[1] && got[1] == got[2],
            "case {case}: repeated check-sat changed the verdict: {got:?}\n{script}"
        );
    }
}

/// Splitting the assertions around an interposed `(check-sat)` must not change
/// the final verdict, and must agree with the same assertions checked once.
///
/// The interposed check is what leaves the theory solvers several decision
/// scopes deep; the assertions that follow are then asserted on top of it.
#[test]
fn an_interposed_check_does_not_change_the_final_verdict() {
    let mut rng = Rng(0xfeed_0bad_1337_c0de);
    for case in 0..400 {
        let asserts = random_assertions(&mut rng, 5);
        let (head, tail) = asserts.split_at(2);
        let one_shot = format!("{PREAMBLE}{}\n(check-sat)\n", asserts.join("\n"));
        let split = format!(
            "{PREAMBLE}{}\n(check-sat)\n{}\n(check-sat)\n",
            head.join("\n"),
            tail.join("\n")
        );
        let direct = verdicts(&one_shot);
        let staged = verdicts(&split);
        assert_eq!(direct.len(), 1, "case {case}\n{one_shot}");
        assert_eq!(staged.len(), 2, "case {case}\n{split}");
        assert_eq!(
            direct[0], staged[1],
            "case {case}: an interposed check-sat changed the answer \
             (direct {direct:?} vs staged {staged:?})\n{split}"
        );
    }
}

/// A `(push)` / `(pop)` bracket containing extra assertions and a check must
/// leave the outer context answering exactly as it did before the bracket.
#[test]
fn a_push_pop_bracket_with_an_inner_check_is_transparent() {
    let mut rng = Rng(0x0123_4567_89ab_cdef);
    for case in 0..300 {
        let outer = random_assertions(&mut rng, 3).join("\n");
        let inner = random_assertions(&mut rng, 2).join("\n");
        let plain = format!("{PREAMBLE}{outer}\n(check-sat)\n");
        let bracketed = format!(
            "{PREAMBLE}{outer}\n(check-sat)\n(push 1)\n{inner}\n(check-sat)\n(pop 1)\n(check-sat)\n"
        );
        let base = verdicts(&plain);
        let around = verdicts(&bracketed);
        assert_eq!(base.len(), 1, "case {case}\n{plain}");
        assert_eq!(around.len(), 3, "case {case}\n{bracketed}");
        assert_eq!(
            base[0], around[0],
            "case {case}: first verdict diverged\n{bracketed}"
        );
        assert_eq!(
            base[0], around[2],
            "case {case}: the push/pop bracket leaked state into the outer \
             context ({base:?} vs {around:?})\n{bracketed}"
        );
    }
}

/// Same, but with quantifiers: every check drives the MBQI round loop, which is
/// the seam the round-boundary rebase sits on.
#[test]
fn repeated_quantified_checks_are_stable() {
    const GOALS: [&str; 6] = [
        "(assert (= (f 1) 100))\n(assert (or (= x 1) (= x 5)))\n\
         (assert (forall ((i Int)) (=> (= (f i) 100) (not (= x i)))))",
        "(assert (forall ((i Int)) (>= (f i) 0)))\n(assert (= (f x) 3))",
        "(assert (forall ((i Int)) (= (f i) (f (+ i 0)))))\n(assert (= x 4))",
        "(assert (forall ((i Int)) (=> (>= i 0) (> (f i) i))))\n(assert (= (f 2) 3))",
        "(assert (forall ((i Int)) (=> (>= i 0) (> (f i) i))))\n(assert (= (f 2) 1))",
        "(assert (exists ((i Int)) (= (f i) 7)))\n(assert (>= x 0))",
    ];
    for (case, goal) in GOALS.iter().enumerate() {
        let script = format!("{PREAMBLE}{goal}\n(check-sat)\n(check-sat)\n(check-sat)\n");
        let got = verdicts(&script);
        assert_eq!(got.len(), 3, "goal {case}\n{script}");
        assert!(
            got[0] == got[1] && got[1] == got[2],
            "goal {case}: repeated check-sat changed the verdict: {got:?}\n{script}"
        );
    }
}

/// Bit-vector and array goals exercise the two other state families the rebase
/// touches: the BV solver's base-level unit facts, and the array-lemma
/// refinement round (the third seam), which resets mid-check and then keeps
/// encoding lemmas against caches the reset did not clear.
#[test]
fn repeated_bv_and_array_checks_are_stable() {
    const BV_PREAMBLE: &str = "(set-logic QF_AUFBV)\n(declare-const a (_ BitVec 8))\n\
                               (declare-const b (_ BitVec 8))\n\
                               (declare-const m (Array Int Int))\n\
                               (declare-const n (Array Int Int))\n\
                               (declare-const i Int)\n(declare-const j Int)\n";
    const GOALS: [&str; 8] = [
        "(assert (= a #x05))",
        "(assert (bvult a b))\n(assert (= b #x03))",
        "(assert (bvult a b))\n(assert (= b #x00))",
        "(assert (= (bvadd a b) #x10))\n(assert (bvugt a #x08))",
        "(assert (= (select (store m i 5) i) 6))",
        "(assert (= (select (store m i 5) j) 6))\n(assert (not (= i j)))",
        "(assert (= m (store n i 3)))\n(assert (= (select m i) 4))",
        "(assert (= (select m i) 1))\n(assert (= (select m j) 2))\n(assert (= i j))",
    ];
    for (case, goal) in GOALS.iter().enumerate() {
        let script = format!("{BV_PREAMBLE}{goal}\n(check-sat)\n(check-sat)\n(check-sat)\n");
        let got = verdicts(&script);
        assert_eq!(got.len(), 3, "goal {case}\n{script}");
        assert!(
            got[0] == got[1] && got[1] == got[2],
            "goal {case}: repeated check-sat changed the verdict: {got:?}\n{script}"
        );
        // And the same goal reached through an interposed check must agree.
        let staged = format!(
            "{BV_PREAMBLE}(check-sat)\n{goal}\n(check-sat)\n(push 1)\n(pop 1)\n(check-sat)\n"
        );
        let staged_got = verdicts(&staged);
        assert_eq!(
            got[0], staged_got[1],
            "goal {case}: an interposed check changed the answer: \
             {got:?} vs {staged_got:?}\n{staged}"
        );
        assert_eq!(
            got[0], staged_got[2],
            "goal {case}: a push/pop bracket changed the answer: \
             {got:?} vs {staged_got:?}\n{staged}"
        );
    }
}

/// A model reported after an interposed check must still assign every declared
/// constant that the one-shot run assigns.
///
/// `Solver::rebase_theory_state` resets the arithmetic and EUF solvers, and the
/// encoder's theory-variable registrations (`arith.intern`, `bv.new_bv`) are
/// memoised in `arith_terms` / `bv_terms` / `tracked_compound_terms`, which the
/// rebase does not clear.  If a registration is not re-created by the trail
/// replay, the variable silently loses its model value.
#[test]
fn model_values_survive_the_rebase() {
    let cases = [
        "(assert (= (+ x y) 10))\n(assert (>= x 3))",
        "(assert (> (f x) 0))\n(assert (= y 2))",
        "(assert (or (= x 1) (= x 5)))\n(assert (= (f x) 9))",
        "(assert (= (f (+ x 1)) 4))",
        // `div` is an *opaque* arithmetic atom: `Solver::register_arith_atom`
        // gives it its own `ArithSolver` variable at encode time, and only the
        // trail replay re-creates that registration after a rebase.  This is the
        // registration-lifecycle case the rebase invariant is stated about.
        "(assert (= (div x 3) 2))\n(assert (= y 1))",
    ];
    for (case, goal) in cases.iter().enumerate() {
        let one_shot = format!("{PREAMBLE}{goal}\n(check-sat)\n(get-model)\n");
        let repeated = format!("{PREAMBLE}{goal}\n(check-sat)\n(check-sat)\n(get-model)\n");
        let first = run(&one_shot);
        let again = run(&repeated);
        for symbol in ["x", "y"] {
            let in_first = first.iter().any(|l| l.contains(symbol));
            let in_again = again.iter().any(|l| l.contains(symbol));
            assert_eq!(
                in_first, in_again,
                "case {case}: `{symbol}` is present in the one-shot model \
                 ({in_first}) but not after a repeated check ({in_again})\n\
                 first: {first:?}\nagain: {again:?}"
            );
        }
    }
}

// ========  ========
// Result lifetime: a verdict belongs to the assertion stack it was computed on
// ========  ========
//
// `Solver::pop` used to leave `model` / `unsat_core` in place.  The core's
// `indices` name positions in `Solver::assertions`, which the pop truncates, so
// the survivor did not merely describe a superseded stack – it *dangled*, and
// `minimize_unsat_core` indexed the truncated vector with it.  These pins are at
// the `Solver` API level on purpose: `Context` gates every query on its own
// `last_result`, so a solver-level leak is invisible from a script and only an
// embedder driving `Solver` directly would meet it.

/// A model belongs to the stack it was found on: `pop` must take it away.
#[test]
fn pop_discards_the_model_of_the_popped_scope() {
    use nixie_core::ast::TermManager;
    use nixie_solver::{Solver, SolverResult};

    let mut solver = Solver::new();
    let mut terms = TermManager::new();
    let p = terms.mk_var("p", terms.sorts.bool_sort);

    solver.push();
    solver.assert(p, &mut terms);
    assert_eq!(solver.check(&mut terms), SolverResult::Sat);
    assert!(
        solver.model().is_some(),
        "control: a `Sat` check produces a model"
    );

    solver.pop();
    assert!(
        solver.model().is_none(),
        "the model describes a scope that no longer exists"
    );
}

/// An unsat core belongs to the stack it was computed on, and its indices point
/// into that stack's assertion vector.  `pop` truncates that vector.
#[test]
fn pop_discards_the_unsat_core_of_the_popped_scope() {
    use nixie_core::ast::TermManager;
    use nixie_solver::{Solver, SolverResult};

    let mut solver = Solver::new();
    solver.set_produce_unsat_cores(true);
    let mut terms = TermManager::new();
    let p = terms.mk_var("p", terms.sorts.bool_sort);
    let not_p = terms.mk_not(p);

    solver.push();
    solver.assert_named(p, "a1", &mut terms);
    solver.assert_named(not_p, "a2", &mut terms);
    assert_eq!(solver.check(&mut terms), SolverResult::Unsat);
    assert!(
        solver.get_unsat_core().is_some(),
        "control: an `Unsat` check with core production on produces a core"
    );

    solver.pop();
    assert_eq!(solver.num_assertions(), 0);
    assert!(
        solver.get_unsat_core().is_none(),
        "the core indexes assertions the pop has just truncated away"
    );
}

/// Strengthening the stack invalidates the model too: it need not satisfy the
/// assertion that was just added, and reporting it would report a "model" of a
/// formula it falsifies.
#[test]
fn asserting_after_a_check_discards_the_model() {
    use nixie_core::ast::TermManager;
    use nixie_solver::{Solver, SolverResult};

    let mut solver = Solver::new();
    let mut terms = TermManager::new();
    let p = terms.mk_var("p", terms.sorts.bool_sort);
    let not_p = terms.mk_not(p);

    solver.assert(p, &mut terms);
    assert_eq!(solver.check(&mut terms), SolverResult::Sat);
    assert!(solver.model().is_some());

    solver.assert(not_p, &mut terms);
    assert!(
        solver.model().is_none(),
        "the model on the table satisfies `p`, and `(not p)` has just been asserted"
    );
}

/// The counterpart the invalidation rule must **not** break: SMT-LIB leaves
/// `check-sat-assuming` in `sat` mode, so a following `(get-value ...)` must
/// still read this check's model even though the assumption scope is realised
/// as `push` / `assert` / `check` / `pop`.
#[test]
fn check_with_assumptions_keeps_its_model_across_the_internal_pop() {
    use nixie_core::ast::TermManager;
    use nixie_solver::{Solver, SolverResult};

    let mut solver = Solver::new();
    let mut terms = TermManager::new();
    let p = terms.mk_var("p", terms.sorts.bool_sort);
    let q = terms.mk_var("q", terms.sorts.bool_sort);
    let p_or_q = terms.mk_or(vec![p, q]);
    solver.assert(p_or_q, &mut terms);

    assert_eq!(
        solver.check_with_assumptions(&[p], &mut terms),
        SolverResult::Sat
    );
    assert!(
        solver.model().is_some(),
        "a model of `assertions AND assumptions` satisfies `assertions`, which is \
         exactly the stack that survives the internal pop"
    );
}

/// End-to-end shape of the same rule, through the script layer: the SMT-LIB
/// `(get-value ...)` after `check-sat-assuming` must still answer.
#[test]
fn get_value_after_check_sat_assuming_still_answers() {
    let out = run(r#"
        (set-logic QF_UF)
        (declare-const p Bool)
        (declare-const q Bool)
        (assert (or p q))
        (check-sat-assuming (p))
        (get-value (p))
    "#);
    assert_eq!(out[0], "sat");
    assert!(
        out[1].contains('p'),
        "get-value after check-sat-assuming must report a value: {}",
        out[1]
    );
}
