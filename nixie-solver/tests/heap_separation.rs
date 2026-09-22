use nixie_solver::heap::{HeapError, HeapSolver, Heaplet};
use nixie_solver::{SolverConfig, SolverResult};
use num_bigint::BigInt;
use std::collections::BTreeMap;

#[test]
fn allocation_aliasing_and_scopes() -> Result<(), HeapError> {
    let mut s = HeapSolver::new();
    let x = s.int_var("x");
    let y = s.int_var("y");
    let seven = s.integer(7);
    let nine = s.integer(9);
    let owned = s.reify(Heaplet::points_to(&x, &seven).star(Heaplet::points_to(&y, &nine)))?;
    s.assert(&owned)?;
    assert_eq!(s.check(), SolverResult::Sat, "{:?}", s.reason_unknown());
    let model = s.model().ok_or(HeapError("missing model"))?.clone();
    assert_eq!(model.cells.len(), 2);
    assert_ne!(model.integers["x"], model.integers["y"]);
    s.validate_model(&model)?;
    assert_eq!(s.statistics().heaplets, 1);
    assert!(s.statistics().backend_terms > 0);
    s.set_random_seed(17);
    assert!(s.model().is_none());
    assert_eq!(s.check(), SolverResult::Sat);
    let mut aliased = model.clone();
    aliased
        .integers
        .insert("y".into(), model.integers["x"].clone());
    assert!(s.validate_model(&aliased).is_err());
    let aliases = s.eq(&x, &y)?;
    assert!(s.model().is_none());
    s.push();
    s.assert(&aliases)?;
    assert_eq!(s.check(), SolverResult::Unsat);
    assert!(s.model().is_none());
    s.pop()?;
    assert_eq!(s.check(), SolverResult::Sat);
    for _ in 0..3 {
        s.push();
        assert!(s.model().is_none());
        s.assert(&aliases)?;
        assert_eq!(s.check(), SolverResult::Unsat);
        s.pop()?;
        assert_eq!(s.check(), SolverResult::Sat);
    }
    assert!(s.pop().is_err());
    assert!(s.reify(Heaplet::emp()).is_err());
    Ok(())
}

#[test]
fn empty_heap_is_not_pure_true_and_nil_cannot_be_owned() -> Result<(), HeapError> {
    let mut s = HeapSolver::new();
    let nil = s.integer(0);
    let one = s.integer(1);
    let emp = s.reify(Heaplet::emp())?;
    let nil_pto = s.reify(Heaplet::points_to(&nil, &one))?;
    let not_emp = s.not(&emp)?;
    let truth = s.and(&[])?;
    s.assert(&truth)?;
    s.push();
    s.assert(&not_emp)?;
    assert_eq!(s.check(), SolverResult::Sat);
    assert!(
        !s.model()
            .ok_or(HeapError("missing model"))?
            .cells
            .is_empty()
    );
    s.pop()?;
    s.push();
    s.assert(&emp)?;
    assert_eq!(s.check(), SolverResult::Sat);
    assert!(
        s.model()
            .ok_or(HeapError("missing model"))?
            .cells
            .is_empty()
    );
    s.pop()?;
    s.assert(&nil_pto)?;
    assert_eq!(s.check(), SolverResult::Unsat);
    Ok(())
}

#[test]
fn symbolic_values_agree_and_integer_arithmetic_is_validated() -> Result<(), HeapError> {
    let mut s = HeapSolver::new();
    let x = s.int_var("x");
    let a = s.int_var("a");
    let b = s.int_var("b");
    let one = s.integer(1);
    let sum = s.add(&a, &one)?;
    let left = s.reify(Heaplet::points_to(&x, &sum))?;
    let right = s.reify(Heaplet::points_to(&x, &b))?;
    let both = s.and(&[left, right])?;
    s.assert(&both)?;
    let bound = s.le(&one, &a)?;
    s.assert(&bound)?;
    assert_eq!(s.check(), SolverResult::Sat, "{:?}", s.reason_unknown());
    let m = s.model().ok_or(HeapError("missing model"))?.clone();
    assert_eq!(m.integers["b"], &m.integers["a"] + 1);
    let unequal = s.eq(&sum, &b)?;
    let unequal = s.not(&unequal)?;
    s.push();
    s.assert(&unequal)?;
    assert_eq!(s.check(), SolverResult::Unsat);
    s.pop()?;
    let mut corrupt = m.clone();
    corrupt.cells.clear();
    assert!(s.validate_model(&corrupt).is_err());
    corrupt = m.clone();
    for value in corrupt.cells.values_mut() {
        *value += 1;
    }
    assert!(s.validate_model(&corrupt).is_err());
    corrupt = m.clone();
    corrupt.integers.remove("a");
    assert!(s.validate_model(&corrupt).is_err());
    corrupt = m;
    corrupt.cells.insert(BigInt::from(0), BigInt::from(0));
    assert!(s.validate_model(&corrupt).is_err());
    Ok(())
}

#[test]
fn fractional_ownership_is_not_implied_by_equal_values() -> Result<(), HeapError> {
    let mut s = HeapSolver::new();
    let x = s.int_var("x");
    let v = s.integer(3);
    let pto = Heaplet::points_to(&x, &v);
    let shared = s.reify(pto.clone())?;
    let overlapping = s.reify(pto.clone().star(pto))?;
    let classical = s.and(&[shared.clone(), shared])?;
    s.assert(&classical)?;
    assert_eq!(s.check(), SolverResult::Sat);
    s.assert(&overlapping)?;
    assert_eq!(s.check(), SolverResult::Unsat);
    Ok(())
}

#[test]
fn proof_requests_and_foreign_handles_fail_closed() -> Result<(), HeapError> {
    for config in [
        SolverConfig::default().with_proof(),
        SolverConfig::default().certified(),
    ] {
        let mut s = HeapSolver::with_config(config);
        assert_eq!(s.check(), SolverResult::Unknown);
        assert!(s.reason_unknown().is_some());
        assert!(s.model().is_none());
    }
    let mut a = HeapSolver::new();
    let mut b = HeapSolver::new();
    let ai = a.integer(1);
    let bi = b.integer(1);
    assert!(a.eq(&ai, &bi).is_err());
    assert!(a.reify(Heaplet::points_to(&ai, &bi)).is_err());
    let bf = b.boolean(true);
    assert!(a.assert(&bf).is_err());
    assert_eq!(b.check(), SolverResult::Sat);
    assert!(
        a.validate_model(b.model().ok_or(HeapError("missing model"))?)
            .is_err()
    );
    assert_eq!(a.check(), SolverResult::Sat);
    Ok(())
}

#[test]
fn exact_wide_constants_and_negative_locations() -> Result<(), HeapError> {
    let mut s = HeapSolver::new();
    let wide: BigInt = BigInt::from(1) << 180;
    let location = s.integer(-wide.clone());
    let value = s.integer(wide.clone());
    let pto = s.reify(Heaplet::points_to(&location, &value))?;
    s.assert(&pto)?;
    assert_eq!(s.check(), SolverResult::Sat, "{:?}", s.reason_unknown());
    assert_eq!(
        s.model()
            .ok_or(HeapError("missing model"))?
            .cells
            .get(&(-wide.clone())),
        Some(&wide)
    );
    Ok(())
}

#[test]
fn wide_symbolic_arithmetic_never_truncates_to_a_false_verdict() -> Result<(), HeapError> {
    let mut s = HeapSolver::new();
    let wide: BigInt = (BigInt::from(1) << 180) + 17;
    let x = s.int_var("x");
    let value = s.integer(wide.clone());
    let owned = s.reify(Heaplet::points_to(&x, &value))?;
    let pin = s.eq(&x, &value)?;
    s.assert(&owned)?;
    s.assert(&pin)?;
    match s.check() {
        SolverResult::Sat => {
            let model = s.model().ok_or(HeapError("missing model"))?;
            assert_eq!(model.integers["x"], wide);
            assert_eq!(model.cells.get(&wide), Some(&wide));
        }
        SolverResult::Unknown => assert!(s.reason_unknown().is_some()),
        SolverResult::Unsat => panic!("a nonzero wide singleton always exists"),
    }
    Ok(())
}

// Full truth assignments to these atoms exercise every Boolean combination:
// arbitrary outer Boolean formulas are unions of these assignments.
const ATOMS: &[&[(i32, i32)]] = &[
    &[],
    &[(1, 0)],
    &[(1, 1)],
    &[(2, 0)],
    &[(2, 1)],
    &[(1, 0), (2, 1)],
    &[(2, 1), (1, 0)],
    &[(1, 0), (1, 0)],
];

fn oracle_patterns() -> Vec<u32> {
    let mut patterns = Vec::new();
    // All partial maps on {1,2,3} to {0,1}; 3 cells also witness the
    // all-false class, so this is complete for these ground atoms.
    for code in 0..27 {
        let mut code = code;
        let mut heap = BTreeMap::new();
        for location in 1..=3 {
            let state = code % 3;
            code /= 3;
            if state != 0 {
                heap.insert(location, state - 1);
            }
        }
        let mut pattern = 0;
        for (i, atom) in ATOMS.iter().enumerate() {
            let map: BTreeMap<_, _> = atom.iter().copied().collect();
            if map.len() == atom.len() && map == heap {
                pattern |= 1 << i;
            }
        }
        patterns.push(pattern);
    }
    patterns
}

#[test]
fn all_boolean_patterns_against_exhaustive_heaps() -> Result<(), HeapError> {
    let mut s = HeapSolver::new();
    let mut atoms = Vec::new();
    for atom in ATOMS {
        let mut heaplet = Heaplet::emp();
        for &(l, v) in *atom {
            let l = s.integer(l);
            let v = s.integer(v);
            heaplet = heaplet.star(Heaplet::points_to(&l, &v));
        }
        atoms.push(s.reify(heaplet)?);
    }
    let negated = atoms
        .iter()
        .map(|a| s.not(a))
        .collect::<Result<Vec<_>, _>>()?;
    let patterns = oracle_patterns();
    for pattern in 0..(1 << atoms.len()) {
        s.push();
        for i in 0..atoms.len() {
            s.assert(if pattern & (1 << i) != 0 {
                &atoms[i]
            } else {
                &negated[i]
            })?;
        }
        let expected = if patterns.contains(&pattern) {
            SolverResult::Sat
        } else {
            SolverResult::Unsat
        };
        assert_eq!(
            s.check(),
            expected,
            "pattern {pattern}: {:?}",
            s.reason_unknown()
        );
        if expected == SolverResult::Sat {
            s.validate_model(s.model().ok_or(HeapError("missing model"))?)?;
        }
        s.pop()?;
    }
    Ok(())
}

#[test]
fn symbolic_aliases_and_values_against_exhaustive_heaps() -> Result<(), HeapError> {
    let mut s = HeapSolver::new();
    let x = s.int_var("x");
    let y = s.int_var("y");
    let a = s.int_var("a");
    let b = s.int_var("b");
    let hx = Heaplet::points_to(&x, &a);
    let hy = Heaplet::points_to(&y, &b);
    let atoms = [
        s.reify(Heaplet::emp())?,
        s.reify(hx.clone())?,
        s.reify(hy.clone())?,
        s.reify(hx.star(hy))?,
    ];
    let negated = atoms
        .iter()
        .map(|a| s.not(a))
        .collect::<Result<Vec<_>, _>>()?;
    for xv in 0..=2 {
        for yv in 0..=2 {
            for av in 0..=1 {
                for bv in 0..=1 {
                    s.push();
                    for (variable, value) in [(&x, xv), (&y, yv), (&a, av), (&b, bv)] {
                        let value = s.integer(value);
                        let pin = s.eq(variable, &value)?;
                        s.assert(&pin)?;
                    }
                    let possible = symbolic_patterns(xv, yv, av, bv);
                    for pattern in 0..16 {
                        s.push();
                        for i in 0..4 {
                            s.assert(if pattern & (1 << i) != 0 {
                                &atoms[i]
                            } else {
                                &negated[i]
                            })?;
                        }
                        let expected = if possible.contains(&pattern) {
                            SolverResult::Sat
                        } else {
                            SolverResult::Unsat
                        };
                        assert_eq!(
                            s.check(),
                            expected,
                            "x={xv} y={yv} a={av} b={bv} pattern={pattern}: {:?}",
                            s.reason_unknown()
                        );
                        s.pop()?;
                    }
                    s.pop()?;
                }
            }
        }
    }
    Ok(())
}

#[test]
fn original_formula_evaluation_and_drop_are_stack_safe() -> Result<(), Box<dyn std::error::Error>> {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| -> Result<(), HeapError> {
            let mut s = HeapSolver::new();
            assert_eq!(s.check(), SolverResult::Sat);
            let model = s.model().ok_or(HeapError("missing model"))?.clone();
            let mut formula = s.boolean(true);
            for _ in 0..50_000 {
                formula = s.not(&formula)?;
            }
            assert!(s.evaluate(&formula, &model)?);
            Ok(())
        })?
        .join()
        .map_err(|_| "deep evaluator thread panicked")??;
    Ok(())
}

#[test]
fn disjunction_and_negation_preserve_heap_semantics() -> Result<(), HeapError> {
    let mut s = HeapSolver::new();
    let l = s.integer(1);
    let v = s.integer(8);
    let p = s.reify(Heaplet::points_to(&l, &v))?;
    let e = s.reify(Heaplet::emp())?;
    let either = s.or(&[p.clone(), e.clone()])?;
    let ne = s.not(&e)?;
    s.assert(&either)?;
    s.assert(&ne)?;
    assert_eq!(s.check(), SolverResult::Sat);
    assert!(s.evaluate(&p, s.model().ok_or(HeapError("missing model"))?)?);
    let np = s.not(&p)?;
    s.assert(&np)?;
    assert_eq!(s.check(), SolverResult::Unsat);
    Ok(())
}

#[test]
#[ignore = "set CVC5 to a reference executable; no solver dependency or FFI"]
fn cvc5_exhaustive_boolean_patterns() -> Result<(), Box<dyn std::error::Error>> {
    let binary = std::env::var("CVC5")?;
    let mut prefix = String::from(
        "(set-logic ALL)\n(declare-heap (Int Int))\n(assert (= (as sep.nil Int) 0))\n",
    );
    for (i, atom) in ATOMS.iter().enumerate() {
        let text = if atom.is_empty() {
            "sep.emp".to_string()
        } else {
            let cells: Vec<_> = atom.iter().map(|(l, v)| format!("(pto {l} {v})")).collect();
            if cells.len() == 1 {
                cells[0].clone()
            } else {
                format!("(sep {})", cells.join(" "))
            }
        };
        prefix.push_str(&format!("(define-fun h{i} () Bool {text})\n"));
    }
    let patterns = oracle_patterns();
    for pattern in 0..(1 << ATOMS.len()) {
        // CVC5 1.3.4 rejects incremental separation logic. Compare each
        // flattened active scope in a fresh process, never change semantics.
        let mut script = prefix.clone();
        for i in 0..ATOMS.len() {
            script.push_str(&if pattern & (1 << i) != 0 {
                format!("(assert h{i})\n")
            } else {
                format!("(assert (not h{i}))\n")
            });
        }
        script.push_str("(check-sat)\n");
        reference_check(&binary, &script, patterns.contains(&pattern))?;
    }
    Ok(())
}

fn reference_check(
    binary: &str,
    script: &str,
    sat: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    use std::io::Write;
    use std::process::{Command, Stdio};
    let mut child = Command::new(binary)
        .args(["--lang=smt2", "--tlimit-per=10000"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    let mut input = child.stdin.take().ok_or("missing reference stdin")?;
    input.write_all(script.as_bytes())?;
    drop(input);
    let output = child.wait_with_output()?;
    assert!(
        output.status.success(),
        "stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8(output.stdout)?;
    assert_eq!(text.trim(), if sat { "sat" } else { "unsat" }, "{script}");
    Ok(())
}

fn symbolic_patterns(xv: i32, yv: i32, av: i32, bv: i32) -> Vec<u32> {
    let mut possible = Vec::new();
    for code in 0..27 {
        let mut code = code;
        let mut heap = BTreeMap::new();
        for l in 1..=3 {
            let state = code % 3;
            code /= 3;
            if state > 0 {
                heap.insert(l, state - 1);
            }
        }
        let p = xv != 0 && heap == BTreeMap::from([(xv, av)]);
        let q = yv != 0 && heap == BTreeMap::from([(yv, bv)]);
        let star = xv != 0 && yv != 0 && xv != yv && heap == BTreeMap::from([(xv, av), (yv, bv)]);
        possible.push(
            u32::from(heap.is_empty())
                | (u32::from(p) << 1)
                | (u32::from(q) << 2)
                | (u32::from(star) << 3),
        );
    }
    possible
}

#[test]
#[ignore = "set CVC5 to a reference executable; no solver dependency or FFI"]
fn cvc5_symbolic_aliases_and_values() -> Result<(), Box<dyn std::error::Error>> {
    let binary = std::env::var("CVC5")?;
    let prefix = "(set-logic ALL)\n(declare-heap (Int Int))\n(assert (= (as sep.nil Int) 0))\n(declare-const x Int)\n(declare-const y Int)\n(declare-const a Int)\n(declare-const b Int)\n(define-fun h0 () Bool sep.emp)\n(define-fun h1 () Bool (pto x a))\n(define-fun h2 () Bool (pto y b))\n(define-fun h3 () Bool (sep (pto x a) (pto y b)))\n";
    for xv in 0..=2 {
        for yv in 0..=2 {
            for av in 0..=1 {
                for bv in 0..=1 {
                    let patterns = symbolic_patterns(xv, yv, av, bv);
                    for pattern in 0..16 {
                        let mut script = format!(
                            "{prefix}(assert (= x {xv}))\n(assert (= y {yv}))\n(assert (= a {av}))\n(assert (= b {bv}))\n"
                        );
                        for i in 0..4 {
                            script.push_str(&if pattern & (1 << i) != 0 {
                                format!("(assert h{i})\n")
                            } else {
                                format!("(assert (not h{i}))\n")
                            });
                        }
                        script.push_str("(check-sat)\n");
                        reference_check(&binary, &script, patterns.contains(&pattern))?;
                    }
                }
            }
        }
    }
    Ok(())
}

#[test]
fn pure_boolean_control_and_all_linear_operations() -> Result<(), HeapError> {
    let mut s = HeapSolver::new();
    let x = s.int_var("x");
    let two = s.integer(2);
    let six = s.integer(6);
    let twice = s.scale(2, &x)?;
    let difference = s.sub(&twice, &two)?;
    let v = s.eq(&difference, &six)?;
    let control = s.bool_var("choose");
    let empty = s.reify(Heaplet::emp())?;
    let left = s.and(&[control.clone(), empty.clone()])?;
    let negative_control = s.not(&control)?;
    let negative_empty = s.not(&empty)?;
    let right = s.and(&[negative_control, negative_empty])?;
    let either = s.or(&[left, right])?;
    s.assert(&v)?;
    s.assert(&either)?;
    s.assert(&control)?;
    assert_eq!(s.check(), SolverResult::Sat, "{:?}", s.reason_unknown());
    let model = s.model().ok_or(HeapError("missing model"))?;
    assert_eq!(model.integers["x"], BigInt::from(4));
    assert!(model.booleans["choose"]);
    assert!(model.cells.is_empty());
    let mut corrupted = model.clone();
    corrupted.booleans.insert("choose".into(), false);
    assert!(s.validate_model(&corrupted).is_err());
    Ok(())
}
