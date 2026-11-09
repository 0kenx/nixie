//! Quantified datatype coverage regressions from OxiZ v0.3.4 (#P2b-90).
use nixie_solver::Context;

const Q1: &str = "(set-logic ALL)\n\
(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))\n\
(declare-const l1 L)\n\
(declare-const l2 L)\n\
(assert (= l1 l2))\n\
(assert ((_ is cons) l1))\n\
(assert ((_ is cons) (tl l1)))\n\
(assert (forall ((n Int)) (=> (and (<= 0 n) (<= n 2)) ((_ is nil) (ite ((_ is cons) l2) (tl l2) nil)))))\n\
(check-sat)\n";

const Q2: &str = "(set-logic ALL)\n\
(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))\n\
(declare-const l1 L)\n\
(declare-const l2 L)\n\
(assert (= l1 l2))\n\
(assert ((_ is cons) l1))\n\
(assert ((_ is cons) (tl l1)))\n\
(assert (forall ((n Int)) (=> (and (<= 0 n) (<= n 2)) ((_ is nil) (tl l2)))))\n\
(check-sat)\n";

const Q5: &str = "(set-logic ALL)\n\
(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))\n\
(declare-const l1 L)\n\
(declare-const l2 L)\n\
(assert (= l1 l2))\n\
(assert ((_ is cons) l1))\n\
(assert ((_ is cons) (tl l1)))\n\
(assert (forall ((n Int)) (=> (> n 0) ((_ is nil) (tl l2)))))\n\
(check-sat)\n";

const Q6: &str = "(set-logic ALL)\n\
(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))\n\
(declare-const l1 L)\n\
(declare-const l2 L)\n\
(assert (= l1 l2))\n\
(assert ((_ is cons) l1))\n\
(assert ((_ is cons) (tl l1)))\n\
(assert (forall ((n Int)) (=> (> n 0) (= (tl l2) (cons n nil)))))\n\
(check-sat)\n";

const Q7: &str = "(set-logic ALL)\n\
(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))\n\
(declare-const l1 L)\n\
(declare-const l2 L)\n\
(assert (= l1 l2))\n\
(assert ((_ is cons) l1))\n\
(assert ((_ is cons) (tl l1)))\n\
(assert (forall ((n Int)) (or (< n 0) ((_ is nil) (tl (tl l2))))))\n\
(assert ((_ is cons) (tl (tl l1))))\n\
(check-sat)\n";

const T00088: &str = "(set-logic ALL)\n\
(declare-datatypes ((L 0) (C 0) (P 0)) (((nil) (cons (hd Int) (tl L))) ((red) (green) (blue)) ((mk (px Int) (pc C)))))\n\
(declare-sort U 0)\n\
(declare-fun h (Int) L)\n\
(declare-fun g (Int) C)\n\
(declare-fun k (L) Int)\n\
(declare-fun q (C) Int)\n\
(declare-fun w (Int) U)\n\
(declare-fun v (L) L)\n\
(declare-const x Int)\n\
(declare-const y Int)\n\
(declare-const z Int)\n\
(declare-const l1 L)\n\
(declare-const l2 L)\n\
(declare-const l3 L)\n\
(declare-const c1 C)\n\
(declare-const c2 C)\n\
(declare-const p P)\n\
(declare-const u1 U)\n\
(declare-const u2 U)\n\
(declare-const a Bool)\n\
(declare-const b Bool)\n\
(declare-const e Bool)\n\
(assert (and (<= (- 3) x 3) (<= (- 3) y 3) (<= (- 3) z 3)))\n\
(assert (distinct (ite ((_ is cons) l3) (tl l3) nil) l3))\n\
(assert ((_ is cons) (ite (= u1 u1) (ite ((_ is cons) l1) (tl l1) nil) (ite ((_ is cons) l1) (v nil) l2))))\n\
(assert (and (= (ite (<= z (- 1)) (ite ((_ is cons) nil) (tl nil) nil) (ite ((_ is cons) nil) (cons x l1) l2)) (ite ((_ is cons) (cons x l1)) (tl (cons x l1)) nil)) (distinct (k (ite ((_ is cons) (ite ((_ is cons) nil) (tl nil) nil)) (tl (ite ((_ is cons) nil) (tl nil) nil)) nil)) (+ x 1))))\n\
(assert (forall ((n Int)) (=> (and (<= 0 n) (<= n 2)) ((_ is nil) (ite ((_ is cons) l2) (tl l2) nil)))))\n\
(check-sat)\n\
(get-model)\n\
(push 1)\n\
(assert (and ((_ is cons) (ite (= l1 l2) l2 l1)) ((_ is blue) blue)))\n\
(check-sat)\n\
(get-model)\n";

#[test]
fn quantified_datatype_roots_have_axioms() {
    for (name, input) in [
        ("Q1", Q1),
        ("Q2", Q2),
        ("Q5", Q5),
        ("Q6", Q6),
        ("Q7", Q7),
        ("T00088", T00088),
    ] {
        let mut context = Context::new();
        let output = context.execute_script(input).expect("valid upstream input");
        let verdicts: Vec<_> = output
            .iter()
            .filter(|s| matches!(s.as_str(), "sat" | "unsat" | "unknown"))
            .collect();
        assert!(!verdicts.is_empty(), "{name}: {output:?}");
        for verdict in verdicts {
            assert_eq!(verdict, "unsat", "{name}: {output:?}");
        }
    }
}

#[test]
fn quantified_datatype_sat_controls_and_shadowing() {
    // The local l shadows the free l. Its tail must not receive facts about
    // the free term merely because hash-consing shares the variable's name.
    for claim in [
        "(forall ((n Int)) (=> (> n 0) ((_ is cons) (tl l))))",
        "(exists ((l L)) ((_ is nil) (tl l)))",
    ] {
        let mut context = Context::new();
        let script = format!(
            "(declare-datatype L ((nil) (cons (hd Int) (tl L))))
            (declare-const l L)
            (assert ((_ is cons) l))
            (assert ((_ is cons) (tl l)))
            (assert {claim})(check-sat)"
        );
        let output = context.execute_script(&script).expect("script");
        assert_eq!(
            output.last().map(String::as_str),
            Some("sat"),
            "{claim}: {output:?}"
        );
    }
}
