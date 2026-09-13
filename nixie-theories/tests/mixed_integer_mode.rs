use nixie_core::ast::TermId;
use nixie_theories::Theory;
use nixie_theories::TheoryCheckResult;
use nixie_theories::arithmetic::ArithSolver;
use num_rational::Rational64;

fn r(v: i64) -> Rational64 {
    Rational64::from_integer(v)
}

#[test]
fn mixed_integer_hole() {
    let t = TermId(7);
    let mut s = ArithSolver::mixed();
    s.intern_integer(t);
    s.assert_gt(&[(t, r(1))], r(3), t);
    s.assert_lt(&[(t, r(1))], r(4), t);
    match s.check().expect("check ok") {
        TheoryCheckResult::Unsat(_) => {}
        other => panic!("x:Int in (3,4) must be unsat, got {other:?}"),
    }
}

#[test]
fn mixed_real_between() {
    let t = TermId(8);
    let mut s = ArithSolver::mixed();
    s.intern(t);
    s.assert_gt(&[(t, r(1))], r(3), t);
    s.assert_lt(&[(t, r(1))], r(4), t);
    match s.check().expect("check ok") {
        TheoryCheckResult::Sat => {}
        other => panic!("y:Real in (3,4) must be sat, got {other:?}"),
    }
}
