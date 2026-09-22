//! Repro: does an array variable equated to a store chain *inside a taken
//! or-branch* get a model value? (2026-09-14 fixed the top-level unit case.)
use nixie_solver::Context;

fn main() {
    let script = r#"
(declare-fun f () (Array Int Int))
(declare-fun g () (Array Int Int))
(declare-fun base () (Array Int Int))
(assert (or
  (= f (store (store base 1 2) 2 1))
  (= g (store base 2 2))))
; force the FIRST disjunct: the second writes 2 at index 2, forbid that;
; and pin f[1]=2 which only the first chain provides.
(assert (= (select f 1) 2))
(assert (not (= (select g 2) 2)))
(check-sat)
(get-value (f (select f 1) (select f 2)))
"#;
    let mut ctx = Context::new();
    for line in ctx.execute_script(script).expect("executes") {
        println!("{line}");
    }
}
