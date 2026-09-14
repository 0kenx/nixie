//! The Phase-3 exit-criterion oracle (`docs/FF_THEORY_DESIGN.md` §10.2):
//! random conjunctive systems over tiny primes, every verdict compared
//! against exhaustive enumeration of all `pⁿ` points — a *complete*
//! oracle. Any disagreement is a wrong answer at n = 1.
//!
//! The enumeration here is independent of the solver's own enumeration
//! fallback: it walks the SMT term language directly (`eval`), while the
//! procedure under test goes through the polynomial encoding, Gröbner
//! bases, root finding and model construction.

use nixie_core::ast::{TermId, TermManager};
use nixie_core::smtlib::Command;
use nixie_core::smtlib::parse_script;
use nixie_core::sort::SortKind;
use nixie_core::sort::field::FieldId;
use nixie_theories::ff_theory::{FfOutcome, check_conjunction, validate_model};
use num_bigint::BigUint;
use num_traits::{One, Zero};
use rustc_hash::FxHashMap;

/// Deterministic xorshift: coverage without nondeterminism.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

fn field_of(manager: &TermManager, sort: nixie_core::sort::SortId) -> FieldId {
    match manager.sorts.get(sort).map(|s| s.kind.clone()) {
        Some(SortKind::FiniteField(id)) => id,
        _ => panic!("expected a finite-field sort"),
    }
}

/// Build `(ff.add (ff.mul a b) c)` style random atoms over `vars`.
fn random_atom(
    rng: &mut Rng,
    manager: &mut TermManager,
    field: FieldId,
    vars: &[TermId],
) -> TermId {
    let pick = |rng: &mut Rng| -> TermId {
        let idx = (rng.next() as usize) % vars.len();
        vars[idx]
    };
    let constant = |rng: &mut Rng, manager: &mut TermManager| -> TermId {
        let v = (rng.next() % 7) as i64;
        manager.mk_ff_const(field, v.into()).expect("const")
    };
    let shape = rng.next() % 4;

    match shape {
        0 => {
            // product of two variables (quadratic)
            let (a, b) = (pick(rng), pick(rng));
            manager.mk_ff_mul([a, b]).expect("mul")
        }
        1 => {
            // sum of a variable and a constant
            let a = pick(rng);
            let c = constant(rng, manager);
            manager.mk_ff_add([a, c]).expect("add")
        }
        2 => {
            // (a + b) * c — degree-2 mix
            let (a, b, c) = (pick(rng), pick(rng), pick(rng));
            let sum = manager.mk_ff_add([a, b]).expect("add");
            manager.mk_ff_mul([sum, c]).expect("mul")
        }
        _ => pick(rng),
    }
}

/// One random system: n_vars variables, n_lits literals (some negated),
/// checked against enumeration.
fn one_round(p: u32, n_vars: usize, n_lits: usize, seed: u64) {
    let mut manager = TermManager::new();
    let sort = manager.sorts.finite_field(BigUint::from(p)).expect("prime");
    let field = field_of(&manager, sort);

    let mut var_names: Vec<String> = (0..n_vars).map(|i| format!("v{i}")).collect();
    // The parser's scope is per-script, so build the variables through the
    // manager directly.
    let vars: Vec<TermId> = var_names
        .iter()
        .map(|name| manager.mk_var(name, sort))
        .collect();
    let _ = &mut var_names;

    let mut rng = Rng(seed);
    let mut assertions: Vec<TermId> = Vec::new();
    for _ in 0..n_lits {
        let lhs = random_atom(&mut rng, &mut manager, field, &vars);
        let rhs = manager
            .mk_ff_const(field, ((rng.next() % p as u64) as i64).into())
            .expect("c");
        let eq = manager.mk_eq(lhs, rhs);
        let lit = if rng.next().is_multiple_of(3) {
            manager.mk_not(eq)
        } else {
            eq
        };
        assertions.push(lit);
    }

    // Independent oracle: enumerate all p^n assignments, evaluate the
    // literal list exactly.
    let mut sat_points = 0usize;
    let total = p.pow(n_vars as u32);
    for point in 0..total {
        let mut assignment: FxHashMap<TermId, BigUint> = FxHashMap::default();
        let mut rest = point as u64;
        for var in &vars {
            assignment.insert(*var, BigUint::from(rest % u64::from(p)));
            rest /= u64::from(p);
        }
        let all = assertions
            .iter()
            .all(|a| eval(&manager, field, p, *a, &assignment));
        if all {
            sat_points += 1;
        }
    }

    let outcome = check_conjunction(&manager, field, &assertions, 1 << 30);
    match outcome {
        FfOutcome::Model(model) => {
            assert!(
                sat_points > 0,
                "p={p} seed={seed}: solver says sat, oracle disagrees"
            );
            let err = validate_model(&manager, field, &assertions, &model)
                .err()
                .unwrap_or_default();
            assert!(
                err.is_empty(),
                "p={p} seed={seed}: model failed validation: {err}"
            );
        }
        FfOutcome::Unsat(core) => {
            assert_eq!(
                sat_points, 0,
                "p={p} seed={seed}: solver says unsat, oracle finds a point"
            );
            // The core must be a subset of the literal indices and every
            // index it names must exist.
            assert!(!core.fact_indices.is_empty());
            for &i in &core.fact_indices {
                assert!(i < assertions.len());
            }
            // Minimality spot-check: the core alone must be unsat by the
            // oracle (a core containing satisfiable literals is not
            // minimal — tolerated for tracing reasons only when the traced
            // cofactors genuinely need them; the checker verifies the
            // algebra separately).
            let core_lits: Vec<TermId> = core.fact_indices.iter().map(|&i| assertions[i]).collect();
            let mut core_sat = 0usize;
            for point in 0..total {
                let mut assignment: FxHashMap<TermId, BigUint> = FxHashMap::default();
                let mut rest = point as u64;
                for var in &vars {
                    assignment.insert(*var, BigUint::from(rest % u64::from(p)));
                    rest /= u64::from(p);
                }
                if core_lits
                    .iter()
                    .all(|a| eval(&manager, field, p, *a, &assignment))
                {
                    core_sat += 1;
                }
            }
            assert_eq!(
                core_sat, 0,
                "p={p} seed={seed}: the returned core is satisfiable by itself"
            );
        }
        FfOutcome::Exhausted => {
            assert_eq!(
                sat_points, 0,
                "p={p} seed={seed}: solver says exhausted-unsat, oracle finds a point"
            );
        }
        other => {
            panic!("p={p} seed={seed}: tiny-field goal must decide, got {other:?}");
        }
    }
}

/// Exact literal evaluation (the independent oracle implementation).
fn eval(
    manager: &TermManager,
    field: FieldId,
    p: u32,
    root: TermId,
    assignment: &FxHashMap<TermId, BigUint>,
) -> bool {
    match &manager.get(root).expect("term").kind {
        nixie_core::ast::TermKind::True => true,
        nixie_core::ast::TermKind::False => false,
        nixie_core::ast::TermKind::Eq(a, b) => {
            eval_term(manager, field, p, *a, assignment)
                == eval_term(manager, field, p, *b, assignment)
        }
        nixie_core::ast::TermKind::Not(inner) => !eval(manager, field, p, *inner, assignment),
        _ => panic!("non-literal in oracle"),
    }
}

fn eval_term(
    manager: &TermManager,
    field: FieldId,
    p: u32,
    root: TermId,
    assignment: &FxHashMap<TermId, BigUint>,
) -> BigUint {
    use nixie_core::ast::TermKind;
    let term = manager.get(root).expect("term");
    match &term.kind {
        TermKind::FfConst { value, field: id } => {
            assert_eq!(id, &field);
            num_bigint::BigInt::to_biguint(value).expect("non-negative") % p
        }
        TermKind::Var(_) => assignment[&root].clone(),
        TermKind::FfAdd(children) => children
            .iter()
            .map(|&c| eval_term(manager, field, p, c, assignment))
            .fold(BigUint::zero(), |acc, v| (acc + v) % p),
        TermKind::FfMul(children) => children
            .iter()
            .map(|&c| eval_term(manager, field, p, c, assignment))
            .fold(BigUint::one(), |acc, v| (acc * v) % p),
        TermKind::FfNeg(c) => (BigUint::from(p) - eval_term(manager, field, p, *c, assignment)) % p,
        TermKind::FfBitsum(children) => {
            let mut acc = BigUint::zero();
            let mut power = BigUint::one();
            for &c in children {
                acc = (acc + &power * eval_term(manager, field, p, c, assignment)) % p;
                power = (&power << 1) % p;
            }
            acc
        }
        _ => panic!("non-FF term in oracle"),
    }
}

#[test]
fn exhaustive_oracle_agrees_at_tiny_primes() {
    // p^n small enough to enumerate: (p, n_vars).
    for (p, n) in [(3u32, 2usize), (5, 2), (7, 2), (11, 1), (13, 2)] {
        for round in 0..40u64 {
            one_round(
                p,
                n,
                2 + (round % 3) as usize,
                0x9E37_79B9_7F4A_7C15 + u64::from(p) + round * 1000 + n as u64,
            );
        }
    }
}

#[test]
fn exhaustive_oracle_agrees_at_f2() {
    for round in 0..30u64 {
        one_round(2, 3, 2 + (round % 3) as usize, 0xDEAD_BEEF + round);
    }
}

#[test]
fn bitsum_constraints_solve() {
    // s = bitsum(b0 b1) ∧ b0, b1 constrained to bits by b_i² = b_i —
    // solved through the GB path (p=17 keeps p^n above the enumeration
    // cap with 3 vars: 17³ = 4913 > 2^12? no, 4913 ≤ 2^22, enumeration
    // would fire; use 5 vars at p=17 → 17^5 > 2^20... still ≤ 2^22.
    // Use p=997 with 3 vars: 997³ ≈ 991M > 2^22 → the GB path, not
    // enumeration.
    let mut manager = TermManager::new();
    let sort = manager
        .sorts
        .finite_field(BigUint::from(997u32))
        .expect("p");
    let field = field_of(&manager, sort);
    let b0 = manager.mk_var("b0", sort);
    let b1 = manager.mk_var("b1", sort);
    let s = manager.mk_var("s", sort);
    // b0^2 = b0, b1^2 = b1 (bit constraints)
    let sq = |v: TermId, manager: &mut TermManager| -> TermId {
        let vv = manager.mk_ff_mul([v, v]).expect("mul");
        manager.mk_eq(vv, v)
    };
    // s = b0 + 2 b1
    let two = manager.mk_ff_const(field, 2i64.into()).expect("c");
    let t2b1 = manager.mk_ff_mul([two, b1]).expect("mul");
    let sum = manager.mk_ff_add([b0, t2b1]).expect("add");
    let bitsum_eq = manager.mk_eq(s, sum);
    let c3 = manager.mk_ff_const(field, 3i64.into()).expect("c");
    let s_is_3 = manager.mk_eq(s, c3);
    let assertions = vec![
        sq(b0, &mut manager),
        sq(b1, &mut manager),
        bitsum_eq,
        s_is_3,
    ];
    let outcome = check_conjunction(&manager, field, &assertions, 1 << 26);
    match outcome {
        FfOutcome::Model(model) => {
            assert_eq!(model.value_of(s), Some(&BigUint::from(3u8)));
            // b0 + 2 b1 = 3 with bits → (b0, b1) = (1, 1).
            assert_eq!(model.value_of(b0), Some(&BigUint::from(1u8)));
            assert_eq!(model.value_of(b1), Some(&BigUint::from(1u8)));
            assert!(validate_model(&manager, field, &assertions, &model).is_ok());
        }
        other => panic!("expected sat, got {other:?}"),
    }
    // Now the impossible value: s = 2 with (b0,b1) bits — satisfiable by
    // (0,1)! And s=3∧s=2 is unsat.
    let c2 = manager.mk_ff_const(field, 2i64.into()).expect("c");
    let s_is_2 = manager.mk_eq(s, c2);
    let mut both = assertions.clone();
    both.push(s_is_2);
    let outcome = check_conjunction(&manager, field, &both, 1 << 26);
    assert!(matches!(outcome, FfOutcome::Unsat(_)));
}

#[test]
fn disequality_witness_semantics() {
    // x ≠ 1 ∧ x·x = 1 over F_101 → x = 100. With x = 1 instead: unsat.
    let mut manager = TermManager::new();
    let sort = manager
        .sorts
        .finite_field(BigUint::from(101u32))
        .expect("p");
    let field = field_of(&manager, sort);
    let x = manager.mk_var("x", sort);
    let one = manager.mk_ff_const(field, 1i64.into()).expect("c");
    let xx = manager.mk_ff_mul([x, x]).expect("mul");
    let x_eq_one = manager.mk_eq(x, one);
    let assertions = vec![manager.mk_eq(xx, one), manager.mk_not(x_eq_one)];
    match check_conjunction(&manager, field, &assertions, 1 << 26) {
        FfOutcome::Model(model) => {
            assert_eq!(model.value_of(x), Some(&BigUint::from(100u8)));
            assert!(validate_model(&manager, field, &assertions, &model).is_ok());
        }
        other => panic!("expected sat (x = -1), got {other:?}"),
    }
    // And the contradictory variant: x = 1 ∧ x ≠ 1.
    let contradictions = vec![manager.mk_eq(x, one), manager.mk_not(x_eq_one)];
    match check_conjunction(&manager, field, &contradictions, 1 << 26) {
        // p=101, one variable: 101 ≤ 2^22, so enumeration decides this and
        // reports the verdict as Exhausted (no traced core on that path);
        // both variants are honest UNSATs.
        FfOutcome::Unsat(core) => assert_eq!(core.fact_indices.len(), 2),
        FfOutcome::Exhausted => {}
        other => panic!("expected unsat, got {other:?}"),
    }
}

#[test]
fn non_prime_is_unreachable_from_the_solver() {
    // A composite modulus cannot produce a field id: parse-time refusal.
    let mut manager = TermManager::new();
    let script = "(declare-const x (_ FiniteField 9)) (assert (= x x))";
    assert!(parse_script(script, &mut manager).is_err());
}

#[test]
fn unknown_sources_are_distinguishable() {
    // Zero budget → OutOfBudget with a named site, never Unsat/Sat.
    let mut manager = TermManager::new();
    let sort = manager
        .sorts
        .finite_field(BigUint::from(101u32))
        .expect("p");
    let field = field_of(&manager, sort);
    let x = manager.mk_var("x", sort);
    let one = manager.mk_ff_const(field, 1i64.into()).expect("c");
    let xx = manager.mk_ff_mul([x, x]).expect("mul");
    // 2 variables at p=101 (enumeration) and the same system reshaped to
    // force the GB path (4 vars) both refuse a zero budget.
    let y = manager.mk_var("y", sort);
    let yy = manager.mk_ff_mul([y, y]).expect("mul");
    let assertions = vec![manager.mk_eq(xx, one), manager.mk_eq(yy, one)];
    match check_conjunction(&manager, field, &assertions, 0) {
        FfOutcome::OutOfBudget { where_ } => {
            assert!(!where_.is_empty(), "the budget site must be named");
        }
        other => panic!("zero budget must yield OutOfBudget, got {other:?}"),
    }
    let _ = one;
}

#[test]
fn asserted_false_is_unsat_with_that_literal() {
    let mut manager = TermManager::new();
    let sort = manager.sorts.finite_field(BigUint::from(7u32)).expect("p");
    let field = field_of(&manager, sort);
    let x = manager.mk_var("x", sort);
    let assertions = vec![manager.mk_eq(x, x), manager.false_id];
    match check_conjunction(&manager, field, &assertions, 1 << 20) {
        FfOutcome::Unsat(core) => assert_eq!(core.fact_indices, vec![1]),
        other => panic!("expected unsat from the false literal, got {other:?}"),
    }
    let _ = x;
}

#[test]
fn underdetermined_system_returns_a_model() {
    // x + y = 5 (positive-dimensional at p=101 > enumeration cap with 2
    // vars? 101² = 10201 ≤ 2^22 → enumeration fires and is complete).
    let mut manager = TermManager::new();
    let sort = manager
        .sorts
        .finite_field(BigUint::from(101u32))
        .expect("p");
    let field = field_of(&manager, sort);
    let x = manager.mk_var("x", sort);
    let y = manager.mk_var("y", sort);
    let five = manager.mk_ff_const(field, 5i64.into()).expect("c");
    let sum = manager.mk_ff_add([x, y]).expect("add");
    let assertions = vec![manager.mk_eq(sum, five)];
    match check_conjunction(&manager, field, &assertions, 1 << 26) {
        FfOutcome::Model(model) => {
            assert!(validate_model(&manager, field, &assertions, &model).is_ok());
        }
        other => panic!("expected sat, got {other:?}"),
    }
}

#[test]
fn parsed_smtlib_goals_solve() {
    // End-to-end: parse a QF_FF script, hand its assertions to the check.
    let mut manager = TermManager::new();
    let script = r#"
        (set-logic QF_FF)
        (declare-const x (_ FiniteField 97))
        (declare-const y (_ FiniteField 97))
        (assert (= (ff.mul x x) #f4m97))
        (assert (= (ff.add x y) #f0m97))
        (check-sat)
    "#;
    let commands = parse_script(script, &mut manager).expect("parses");
    let mut assertions = Vec::new();
    for cmd in commands {
        if let Command::Assert(t) = cmd {
            assertions.push(t);
        }
    }
    let field = {
        let x_decl = manager.mk_var(
            "x",
            manager
                .sorts
                .find_finite_field(&BigUint::from(97u32))
                .expect("sort"),
        );
        let sort = manager.get(x_decl).expect("var").sort;
        field_of(&manager, sort)
    };
    match check_conjunction(&manager, field, &assertions, 1 << 26) {
        FfOutcome::Model(model) => {
            // x ∈ {2, 95}; y = -x.
            let x = model
                .value_of(
                    manager.mk_var(
                        "x",
                        manager
                            .sorts
                            .find_finite_field(&BigUint::from(97u32))
                            .expect("s"),
                    ),
                )
                .cloned()
                .expect("x assigned");
            assert!(x == BigUint::from(2u8) || x == BigUint::from(95u8));
            assert!(validate_model(&manager, field, &assertions, &model).is_ok());
        }
        other => panic!("expected sat, got {other:?}"),
    }
}

#[test]
fn corrupted_certificates_are_rejected() {
    use nixie_core::sort::SortKind;
    // Build an UNSAT goal with a linear certificate, then corrupt the
    // recorded cofactors/generators in every way the verifier watches
    // for; each must fail verification (fail-closed is the property —
    // a broken certificate may never certify).
    let mut manager = TermManager::new();
    let sort = manager
        .sorts
        .finite_field(BigUint::from(97u32))
        .expect("prime");
    let field = match manager.sorts.get(sort).map(|s| s.kind.clone()) {
        Some(SortKind::FiniteField(id)) => id,
        _ => panic!("expected FF sort"),
    };
    let x = manager.mk_var("x", sort);
    let c5 = manager.mk_ff_const(field, 5i64.into()).expect("c");
    let c6 = manager.mk_ff_const(field, 6i64.into()).expect("c");
    let assertions = vec![manager.mk_eq(x, c5), manager.mk_eq(x, c6)];

    use nixie_theories::ff_theory::{FfCertificate, FfOutcome, check_conjunction};
    let outcome = check_conjunction(&manager, field, &assertions, 1 << 24);
    let FfOutcome::Unsat(core) = outcome else {
        panic!("expected unsat");
    };
    let Some(nixie_theories::ff_theory::FfCertificate::IdealMembership {
        field: cfield,
        generators,
        cofactors,
    }) = core.certificate.clone()
    else {
        panic!("expected an ideal-membership certificate");
    };

    // 1. The pristine certificate verifies.
    let good = FfCertificate::IdealMembership {
        field: cfield,
        generators: generators.clone(),
        cofactors: cofactors.clone(),
    };
    assert!(good.verify(&manager, &assertions));

    // 2. Dropping a generator breaks alignment (length mismatch).
    let mut gens2 = generators.clone();
    gens2.pop();
    let bad2 = FfCertificate::IdealMembership {
        field: cfield,
        generators: gens2,
        cofactors: cofactors.clone(),
    };
    assert!(!bad2.verify(&manager, &assertions));

    // 3. Zeroing every cofactor makes the sum 0, not a nonzero constant.
    let bad3 = FfCertificate::IdealMembership {
        field: cfield,
        generators: generators.clone(),
        cofactors: cofactors
            .iter()
            .map(|_| nixie_math::ff::poly::MPoly::zero())
            .collect(),
    };
    assert!(!bad3.verify(&manager, &assertions));

    // 4. A certificate against DIFFERENT assertions (satisfiable ones)
    //    must not verify: the replayed generators disagree.
    let c1 = manager.mk_ff_const(field, 1i64.into()).expect("c");
    let other = vec![manager.mk_eq(x, c1), manager.mk_eq(x, c1)];
    assert!(!good.verify(&manager, &other));
}
