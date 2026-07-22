//! End-to-end equivalence tests for the quantifier-elimination front-ends
//! that were hardened in this wave:
//!
//! * `qe::MbiSolver` — propositional Craig interpolation (validated).
//! * `qe::cad::CadSolver` — real term→polynomial extraction.
//! * `qe::datatype::DatatypeQePlugin` — constructor case-split QE.
//! * `qe::bv::BvQePlugin` — sound bit-vector QE (unused var / definitional /
//!   small-width brute force).
//!
//! Each "eliminated" result is checked for equivalence against the original
//! quantified formula (or, for CAD, the extracted polynomial is checked
//! against `lhs - rhs` by evaluation).

use oxiz_core::model::{Model, ModelEvaluator, Value};
use oxiz_core::qe::MbiSolver;
use oxiz_core::qe::bv::BvQePlugin;
use oxiz_core::qe::cad::{CadError, CadSolver};
use oxiz_core::qe::datatype::{Constructor, Datatype, DatatypeQePlugin};
use oxiz_core::{TermId, TermKind, TermManager};

// ---------------------------------------------------------------------------
// MBI: validated propositional interpolation.
// ---------------------------------------------------------------------------

fn eval_bool(term: TermId, assign: &[(TermId, bool)], tm: &TermManager) -> Option<bool> {
    match &tm.get(term)?.kind {
        TermKind::True => Some(true),
        TermKind::False => Some(false),
        TermKind::Var(_) => assign.iter().find(|(t, _)| *t == term).map(|(_, b)| *b),
        TermKind::Not(a) => Some(!eval_bool(*a, assign, tm)?),
        TermKind::And(args) => {
            let mut acc = true;
            for a in args.iter().copied().collect::<Vec<_>>() {
                acc &= eval_bool(a, assign, tm)?;
            }
            Some(acc)
        }
        TermKind::Or(args) => {
            let mut acc = false;
            for a in args.iter().copied().collect::<Vec<_>>() {
                acc |= eval_bool(a, assign, tm)?;
            }
            Some(acc)
        }
        TermKind::Implies(a, b) => Some(!eval_bool(*a, assign, tm)? || eval_bool(*b, assign, tm)?),
        _ => None,
    }
}

#[test]
fn mbi_interpolant_satisfies_craig_conditions() {
    // A: (x ∧ z), B: (¬x ∧ w). Shared: x. A ∧ B unsat.
    let mut tm = TermManager::new();
    let bool_sort = tm.sorts.bool_sort;
    let x = tm.mk_var("x", bool_sort);
    let z = tm.mk_var("z", bool_sort);
    let w = tm.mk_var("w", bool_sort);
    let a = tm.mk_and([x, z]);
    let nx = tm.mk_not(x);
    let b = tm.mk_and([nx, w]);

    let mut solver = MbiSolver::new();
    let interp = solver
        .interpolate(a, b, &mut tm)
        .expect("interpolant should exist for unsat A ∧ B");

    // Only the shared variable x may appear.
    assert!(interp.variables().iter().all(|&v| v == x));

    // Verify A ⇒ I and I ∧ B unsat over all assignments of {x, z, w}.
    let vars = [x, z, w];
    for mask in 0u64..(1 << vars.len()) {
        let assign: Vec<(TermId, bool)> = vars
            .iter()
            .enumerate()
            .map(|(i, &v)| (v, (mask >> i) & 1 == 1))
            .collect();
        let av = eval_bool(a, &assign, &tm).unwrap();
        let iv = eval_bool(interp.formula(), &assign, &tm).unwrap();
        let bv = eval_bool(b, &assign, &tm).unwrap();
        assert!(!av || iv, "A ⇒ I violated");
        assert!(!iv || !bv, "I ∧ B satisfiable");
    }
}

#[test]
fn mbi_no_interpolant_when_satisfiable() {
    let mut tm = TermManager::new();
    let bool_sort = tm.sorts.bool_sort;
    let x = tm.mk_var("x", bool_sort);
    let y = tm.mk_var("y", bool_sort);
    let mut solver = MbiSolver::new();
    assert!(solver.interpolate(x, y, &mut tm).is_none());
}

// ---------------------------------------------------------------------------
// CAD: real polynomial extraction.
// ---------------------------------------------------------------------------

#[test]
fn cad_extracts_faithful_polynomial() {
    // (x*x + 2*y) vs (3): polynomial is x^2 + 2y - 3.
    let mut tm = TermManager::new();
    let int_sort = tm.sorts.int_sort;
    let x = tm.mk_var("x", int_sort);
    let y = tm.mk_var("y", int_sort);
    let two = tm.mk_int(2);
    let three = tm.mk_int(3);
    let x_sq = tm.mk_mul([x, x]);
    let two_y = tm.mk_mul([two, y]);
    let lhs = tm.mk_add([x_sq, two_y]);

    let solver = CadSolver::new();
    let poly = solver
        .term_to_polynomial(lhs, three, &tm)
        .expect("polynomial extraction should succeed");
    assert_eq!(poly.degree(), 2);

    use num_bigint::BigInt;
    use num_rational::BigRational;
    use std::collections::HashMap;
    let rat = |n: i64| BigRational::from_integer(BigInt::from(n));
    for (xv, yv) in [(0i64, 0i64), (2, 3), (-1, 4)] {
        let mut point = HashMap::new();
        point.insert("x".to_string(), rat(xv));
        point.insert("y".to_string(), rat(yv));
        let expected = rat(xv) * rat(xv) + rat(2) * rat(yv) - rat(3);
        assert_eq!(poly.evaluate(&point), expected);
    }
}

#[test]
fn cad_rejects_non_polynomial() {
    let mut tm = TermManager::new();
    let int_sort = tm.sorts.int_sort;
    let x = tm.mk_var("x", int_sort);
    let y = tm.mk_var("y", int_sort);
    let div = tm.mk_div(x, y);
    let zero = tm.mk_int(0);
    let solver = CadSolver::new();
    assert_eq!(
        solver.term_to_polynomial(div, zero, &tm),
        Err(CadError::DivisionByNonConstant)
    );
}

// ---------------------------------------------------------------------------
// Datatype: constructor case-split QE.
// ---------------------------------------------------------------------------

fn ctor_name(term: TermId, tm: &TermManager) -> Option<String> {
    match &tm.get(term)?.kind {
        TermKind::DtConstructor { constructor, args } if args.is_empty() => {
            Some(tm.resolve_str(*constructor).to_string())
        }
        _ => None,
    }
}

fn eval_dt(term: TermId, tm: &TermManager) -> Option<bool> {
    match &tm.get(term)?.kind {
        TermKind::True => Some(true),
        TermKind::False => Some(false),
        TermKind::And(args) => {
            let mut acc = true;
            for a in args.iter().copied().collect::<Vec<_>>() {
                acc &= eval_dt(a, tm)?;
            }
            Some(acc)
        }
        TermKind::Or(args) => {
            let mut acc = false;
            for a in args.iter().copied().collect::<Vec<_>>() {
                acc |= eval_dt(a, tm)?;
            }
            Some(acc)
        }
        TermKind::Not(a) => Some(!eval_dt(*a, tm)?),
        TermKind::Eq(a, b) => Some(ctor_name(*a, tm)? == ctor_name(*b, tm)?),
        TermKind::DtTester { constructor, arg } => {
            Some(ctor_name(*arg, tm)? == tm.resolve_str(*constructor))
        }
        _ => None,
    }
}

fn traffic_light() -> Datatype {
    Datatype {
        name: "Light".to_string(),
        constructors: vec![
            Constructor {
                id: 0,
                name: "R".to_string(),
                arg_sorts: vec![],
            },
            Constructor {
                id: 1,
                name: "Y".to_string(),
                arg_sorts: vec![],
            },
            Constructor {
                id: 2,
                name: "G".to_string(),
                arg_sorts: vec![],
            },
        ],
    }
}

#[test]
fn datatype_enum_case_split_equivalence() {
    // ∃ x:Light. (is_R(x) ∨ is_G(x)) ≡ true.
    let mut tm = TermManager::new();
    let light = tm.sorts.mk_datatype_sort("Light");
    let x = tm.mk_var("x", light);
    let is_r = tm.mk_dt_tester("R", x);
    let is_g = tm.mk_dt_tester("G", x);
    let phi = tm.mk_or([is_r, is_g]);

    let mut plugin = DatatypeQePlugin::default_config();
    plugin.register_datatype(traffic_light());
    let result = plugin
        .eliminate(x, "Light", phi, &mut tm)
        .expect("elimination should succeed");

    assert!(!tm.free_vars(result).contains(&x));
    assert_eq!(eval_dt(result, &tm), Some(true));
}

#[test]
fn datatype_enum_unsat_case() {
    // ∃ x:Light. (is_R(x) ∧ is_G(x)) ≡ false.
    let mut tm = TermManager::new();
    let light = tm.sorts.mk_datatype_sort("Light");
    let x = tm.mk_var("x", light);
    let is_r = tm.mk_dt_tester("R", x);
    let is_g = tm.mk_dt_tester("G", x);
    let phi = tm.mk_and([is_r, is_g]);

    let mut plugin = DatatypeQePlugin::default_config();
    plugin.register_datatype(traffic_light());
    let result = plugin
        .eliminate(x, "Light", phi, &mut tm)
        .expect("elimination should succeed");

    assert!(!tm.free_vars(result).contains(&x));
    assert_eq!(eval_dt(result, &tm), Some(false));
}

#[test]
fn datatype_recursive_depth_budget_residual() {
    // Recursive list-like datatype: Nil | Cons(tail: L). With a bounded depth
    // budget the elimination must still succeed, produce a residual, and drop
    // the target variable.
    let mut tm = TermManager::new();
    let list = tm.sorts.mk_datatype_sort("L");
    let x = tm.mk_var("x", list);
    let phi = tm.mk_dt_tester("Nil", x);

    // The recursive `Cons` argument has the datatype's own sort. Only the
    // sort id is consulted by the plugin, so clone the interned datatype sort.
    let list_sort_val = tm
        .sorts
        .get(list)
        .cloned()
        .expect("datatype sort must exist");
    let list_dt = Datatype {
        name: "L".to_string(),
        constructors: vec![
            Constructor {
                id: 0,
                name: "Nil".to_string(),
                arg_sorts: vec![],
            },
            Constructor {
                id: 1,
                name: "Cons".to_string(),
                arg_sorts: vec![list_sort_val],
            },
        ],
    };

    let mut plugin = DatatypeQePlugin::default_config();
    plugin.register_datatype(list_dt);
    let result = plugin
        .eliminate(x, "L", phi, &mut tm)
        .expect("elimination should succeed within depth budget");
    assert!(!tm.free_vars(result).contains(&x));
}

// ---------------------------------------------------------------------------
// BV: sound bit-vector QE.
// ---------------------------------------------------------------------------

fn bv_eval(formula: TermId, assign: &[(TermId, u32, u64)], tm: &TermManager) -> Option<bool> {
    let mut model = Model::new();
    for &(v, w, val) in assign {
        model.assign(v, Value::BitVec(w, val));
    }
    let mut evaluator = ModelEvaluator::new(&model);
    evaluator
        .eval(formula, tm)
        .value()
        .and_then(|v| v.as_bool())
}

#[test]
fn bv_brute_force_equivalence() {
    // ∃ x:bv3. (x + a = 5) — solvable for every a (x = 5 - a), so ≡ true.
    let mut tm = TermManager::new();
    let bv3 = tm.sorts.bitvec(3);
    let x = tm.mk_var("x", bv3);
    let a = tm.mk_var("a", bv3);
    let five = tm.mk_bitvec(5i64, 3);
    let sum = tm.mk_bv_add(x, a);
    let phi = tm.mk_eq(sum, five);

    let mut plugin = BvQePlugin::default_config();
    let result = plugin
        .eliminate(x, phi, &mut tm)
        .expect("brute-force elimination should succeed");
    assert!(!tm.free_vars(result).contains(&x));

    for av in 0..8u64 {
        // ∃ x. φ under a := av.
        let mut exists = false;
        for xv in 0..8u64 {
            if bv_eval(phi, &[(x, 3, xv), (a, 3, av)], &tm) == Some(true) {
                exists = true;
                break;
            }
        }
        let elim = bv_eval(result, &[(a, 3, av)], &tm).expect("evaluable without x");
        assert_eq!(exists, elim, "mismatch at a={av}");
    }
}

#[test]
fn bv_unused_variable_is_identity() {
    let mut tm = TermManager::new();
    let bv4 = tm.sorts.bitvec(4);
    let x = tm.mk_var("x", bv4);
    let a = tm.mk_var("a", bv4);
    let b = tm.mk_var("b", bv4);
    let phi = tm.mk_bv_ult(a, b);

    let mut plugin = BvQePlugin::default_config();
    let result = plugin.eliminate(x, phi, &mut tm).expect("should eliminate");
    assert_eq!(result, phi);
}
