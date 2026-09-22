use nixie_core::ast::TermId;
use nixie_theories::Theory;
use nixie_theories::array::ArraySolver;
use nixie_theories::combination::{CombinationMode, TheoryCombiner};
use nixie_theories::fp::{FpFormat, FpSolver, FpValue};
use nixie_theories::set::{CardConstraintKind, SetConstraint, SetExpr, SetSolver, SetSort};
use nixie_theories::utvpi::{Sign, UtConstraint, UtvpiConfig, UtvpiSolver};
use num_rational::Rational64;
fn t(n: u32) -> TermId {
    TermId::new(n)
}
fn r(n: i64) -> Rational64 {
    Rational64::from_integer(n)
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
    for spfa in [true, false] {
        let config = UtvpiConfig {
            use_spfa: spfa,
            ..Default::default()
        };
        let mut s = UtvpiSolver::with_config(true, config.clone());
        let x = s.get_or_create_var(t(1));
        s.add_sum(x, x, r(1), t(10));
        s.add_neg_sum(x, x, r(-1), t(11));
        println!(
            "integer parity spfa={spfa}: {:?}, x={:?}",
            s.check(),
            s.get_value(x)
        );
        let mut s = UtvpiSolver::with_config(false, config.clone());
        let x = s.get_or_create_var(t(1));
        let mut c = UtConstraint::upper(x, r(0), t(10));
        c.strict = true;
        s.add_constraint(c);
        s.add_lower(x, r(0), t(11));
        println!("real strict spfa={spfa}: {:?}", s.check());
        let mut s = UtvpiSolver::with_config(false, config.clone());
        s.add_general(0, Sign::Zero, 0, Sign::Zero, r(-1), t(10));
        println!("zero coefficients spfa={spfa}: {:?}", s.check());
        let mut s = UtvpiSolver::with_config(false, config.clone());
        let x = s.get_or_create_var(t(1));
        s.push();
        s.add_upper(x, r(0), t(10));
        s.pop(1);
        s.add_upper(x, r(0), t(11));
        s.add_lower(x, r(-1), t(12));
        println!("pop source edges spfa={spfa}: {:?}", s.check());
        let mut s = UtvpiSolver::with_config(false, config);
        let x = s.get_or_create_var(t(1));
        println!("unconstrained check: {:?}", s.check());
        println!(
            "unconstrained implied bounds: {:?} {:?}",
            s.get_lower_bound(x),
            s.get_upper_bound(x)
        );
    }
    let mut c = TheoryCombiner::with_mode(CombinationMode::ModelBased);
    for v in [t(0), t(1)] {
        c.add_shared_var(v);
        c.euf_mut().intern(v);
        c.arith_mut().assert_eq(&[(v, r(1))], r(0), t(20 + v.raw()));
    }
    c.euf_mut().assert_diseq(0, 1, t(10));
    println!("model based x=0 y=0 x!=y: {:?}", c.check()?);
    let mut s = UtvpiSolver::new(true);
    let x = s.get_or_create_var(t(1));
    let mut c = UtConstraint::upper(x, Rational64::new(1, 2), t(10));
    c.strict = true;
    s.add_constraint(c);
    s.add_lower(x, r(0), t(11));
    println!("integer 0 <= x < 1/2: {:?}", s.check());
    let mut s = UtvpiSolver::new(false);
    let x = s.get_or_create_var(t(1));
    let y = s.get_or_create_var(t(2));
    s.add_sum(x, y, r(-1), t(10));
    s.add_neg_sum(x, y, r(0), t(11));
    println!("inconsistent sum conflict core: {:?}", s.check());
    let mut fp = FpSolver::new();
    fp.assert_const(t(1), &FpValue::from_f32(1.0));
    fp.assert_fp_to_fp(t(2), t(1), FpFormat::FLOAT64);
    fp.assert_const(t(2), &FpValue::from_f64(2.0));
    println!("fp widen 1 to 2: {:?}", fp.check()?);
    let mut sets = SetSolver::new();
    let a = sets.new_set_var("a", SetSort::IntSet);
    let b = sets.new_set_var("b", SetSort::IntSet);
    sets.add_constraint(SetConstraint::Disjoint {
        lhs: SetExpr::Var(a),
        rhs: SetExpr::Var(b),
    })
    .map_err(|e| format!("{e:?}"))?;
    for v in [a, b] {
        sets.add_constraint(SetConstraint::Member {
            element: 1,
            set: SetExpr::Var(v),
            sign: true,
        })
        .map_err(|e| format!("{e:?}"))?;
        sets.add_constraint(SetConstraint::Cardinality {
            set: SetExpr::Var(v),
            op: CardConstraintKind::Equal,
            bound: 1,
        })
        .map_err(|e| format!("{e:?}"))?;
    }
    println!("disjoint same singleton: {:?}", sets.check());
    let mut scoped_sets = SetSolver::new();
    let v = scoped_sets.new_set_var("s", SetSort::IntSet);
    scoped_sets.push();
    scoped_sets
        .add_constraint(SetConstraint::Cardinality {
            set: SetExpr::Var(v),
            op: CardConstraintKind::Equal,
            bound: 0,
        })
        .map_err(|e| format!("{e:?}"))?;
    scoped_sets.pop();
    scoped_sets
        .add_constraint(SetConstraint::Member {
            element: 1,
            set: SetExpr::Var(v),
            sign: true,
        })
        .map_err(|e| format!("{e:?}"))?;
    println!("set popped cardinality: {:?}", scoped_sets.check());
    let mut sets = SetSolver::new();
    sets.assert_true(t(1))?;
    sets.assert_false(t(1))?;
    println!(
        "set contradictory assertions: {:?}",
        Theory::check(&mut sets)?
    );
    let mut c = TheoryCombiner::new();
    for v in [t(0), t(1)] {
        c.add_shared_var(v);
        c.euf_mut().intern(v);
        c.arith_mut().intern(v);
    }
    c.euf_mut().assert_diseq(0, 1, t(10));
    println!(
        "polite unconstrained reals x != y: {:?}",
        c.check_polite_combination()?
    );
    let old_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let result = std::panic::catch_unwind(|| {
        let mut a = ArraySolver::new();
        let x = a.intern(t(1));
        a.push();
        let y = a.intern(t(2));
        assert!(a.merge(x, y, t(10)).is_ok());
        a.pop();
    });
    std::panic::set_hook(old_hook);
    println!("array scoped merge pop panics: {}", result.is_err());
    let mut a = ArraySolver::new();
    a.assert_false(t(1))?;
    println!("array negative atom: {:?}", a.check()?);
    Ok(())
}
