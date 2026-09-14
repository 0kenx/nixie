# A model's datatype field contradicts the assertion that pinned it

**Status:** **fixed** 2026-09-14, same day. Kept because the shape of the
bug and how it was found are worth having on record.
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

## The cause, and the fix

`build_model` extracts values from asserted equalities whose SAT variable is
true, and its selection recognised **arithmetic, bit-vector and
uninterpreted-function** terms only. A string-sorted name was therefore never
picked as the "variable" side of `x = "a"`, the equality was skipped, and a
default of `""` was installed later — a model value contradicting the very
assertion that pinned it.

The fix is a branch ahead of that selection: when exactly one side of a true
equality is a string literal and the other has no assignment yet, record it.
The equality holds in this model, so the two sides denote the same string and
recording one as the other's value states only what the query already forced.

It was found and fixed on the same day, by the same mechanism: the trace replay
in `nixie-tla-check` decoded the state, the evaluator said `Init` was FALSE for
it, and the disagreement was visible instead of being carried silently inside a
counterexample nobody reads.
`nixie-tla-check/tests/traces.rs::a_tuple_valued_variable_decodes` is the
regression.
