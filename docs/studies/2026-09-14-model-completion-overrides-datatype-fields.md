# A model's datatype field contradicts the assertion that pinned it

**Status:** open defect in `nixie-solver`, found 2026-09-14.
**Severity:** wrong `(get-value …)`; the `sat`/`unsat` verdict is unaffected.

## What happens

Assert two field equations on a single-constructor datatype and ask the model
what the fields are:

```rust
let fields = vec![("@t1".to_string(), int), ("@t2".to_string(), str_sort)];
let sort = declare_struct(&fields, &mut tm);          // nixie-tla-check::sorts
let t  = tm.mk_var("t", sort);
let f1 = tm.mk_dt_selector("@t1", t, int);
let f2 = tm.mk_dt_selector("@t2", t, str_sort);
let c1 = tm.mk_eq(f1, tm.mk_int(1.into()));
let c2 = tm.mk_eq(f2, tm.mk_string_lit("a"));
solver.assert(c1, &mut tm);
solver.assert(c2, &mut tm);
assert_eq!(solver.check(&mut tm), SolverResult::Sat);
let m = solver.model().unwrap().clone();
m.eval(f1, &mut tm);   // IntConst(1)    — correct
m.eval(f2, &mut tm);   // StringLit("")  — WRONG, the assertion says "a"
m.eval(c2, &mut tm);   // True           — and the model agrees it is true
```

The model evaluates the *assertion* `@t2(t) = "a"` to `TRUE` and the *term*
`@t2(t)` to `""`. Those cannot both be right. An integer field is returned
correctly; a string field is not, which points at the sort-default completion
(`build_model` completes unconstrained constants with sort defaults) running
over a selector application whose value the equality had already fixed.

## How it was found

Not by looking for it. `nixie-tla-check` now decodes the counterexample behind
a reported violation and **replays it** through `nixie-tla`'s evaluator —
`Init` in the first state, `Next` between each pair, the invariant false at the
end. For

```tla
VARIABLE t
Init == t = <<1, "a">>
Next == UNCHANGED t
Inv  == t[1] = 2
```

the trace decodes as `t = <<1, "">>` and the replay reports `Init` is FALSE.
The violation itself is genuine (`t[1]` is 1, not 2); it is the *witness* that
is wrong.

## What is not the cause

- Not the decoder. It reads `@t2(t)` through `Model::eval`, which is the
  supported way to ask, and the same path returns the integer field correctly.
- Not datatype axiom incompleteness in the sense the `dt_axioms_incomplete`
  gate covers: the solver answers `sat`, which is right, and evaluates both
  assertions to `TRUE`.

## Where to look

`nixie-solver`'s model construction and completion — specifically whatever
assigns a value to a selector application, and the sort-default completion that
appears to overwrite it. The reproducer above is four lines and does not need
the TLA+ front end; it is worth lifting into `nixie-solver`'s own tests as the
regression once the fix lands.

## Why it was not fixed here

It is in a different crate than the slice that found it, that crate had
in-flight edits from another agent at the time, and the fix wants a solver
author's judgement about where completion should and should not run. The
consequence is pinned by
`nixie-tla-check/tests/traces.rs::a_tuple_field_the_query_did_not_probe_comes_back_defaulted`,
which will start failing — correctly — when the model is fixed.
