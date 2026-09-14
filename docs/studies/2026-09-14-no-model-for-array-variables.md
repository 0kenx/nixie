# An array-sorted variable has no value in the model

**Status:** open gap in `nixie-solver`, found 2026-09-14.
**Severity:** `(get-value)` on an array term cannot answer; the `sat`/`unsat`
verdict is unaffected.

## What happens

```rust
let arr = tm.sorts.array(int, int);
let f    = tm.mk_var("f", arr);
let base = tm.mk_var("base", arr);
let s2   = tm.mk_store(tm.mk_store(base, one, one), two, two);
solver.assert(tm.mk_eq(f, s2), &mut tm);
assert_eq!(solver.check(&mut tm), SolverResult::Sat);

let m = solver.model().unwrap().clone();
m.get(f)                       // None      — nothing assigned
m.eval(f, &mut tm)             // Var("f")  — evaluates to itself
m.eval(tm.mk_select(f, one), &mut tm)
                               // Select(f, 1) — unreduced
```

`f` is pinned by an assertion to a two-store chain over `base`, and the model
says nothing about it. Two separate things are missing:

1. **The array theory produces no model value** for an array-sorted variable.
   There is no store chain, no `FuncInterp`, no default — `Model::get` returns
   `None`.
2. **`Model::eval` has no case for `select` or `store`.** Even given a store
   chain it could not reduce `select(store(b, j, v), i)`, so a `(get-value
   (select f 1))` cannot be answered from the terms either.

## Why it matters here

`nixie-tla-check` now decodes the counterexample behind a reported violation
and replays it through `nixie-tla`'s evaluator (`src/trace.rs`). A TLA+
function is encoded as an SMT array plus a companion domain term, so a
function-valued state variable is exactly this shape. The decoder works around
(2) by reading the `select` terms *the query itself built* — the same tactic it
uses for sets, whose ground reduction likewise leaves no model value — but that
only recovers points something asked about. A function `Init` pins with a store
chain and the invariant never selects from is unrecoverable, and its trace
cannot be replayed.

Measured cost today: **none on the corpus** — all 19 reported violations are
over scalar state, and 18 of them replay (the 19th is a resource limit, not
this). The cost is on the shape rather than the count, and it is pinned by
`nixie-tla-check/tests/traces.rs::a_function_built_by_init_is_not_replayable_yet`.

## What the fix looks like

Both halves, in `nixie-solver`:

* Array model construction: give an array-sorted term a value — the natural one
  is the store chain the theory already has, or a `FuncInterp` of explicit
  points plus a default, which is what Z3 and CVC5 return for
  `(get-value (as-array …))`.
* `Model::eval`: add the `select`/`store` cases, reducing
  `select(store(a, j, v), i)` to `v` when `i` and `j` are equal constants, to
  `select(a, i)` when they are distinct constants, and leaving it alone when
  neither can be decided. The frame machine already has the shape for a
  two-child operator (`EqLhs` / `EqRhs`).

## Related

`docs/studies/2026-09-14-model-completion-overrides-datatype-fields.md` is a
second model-construction defect found by the same replay, in the same area:
there a datatype field *is* assigned, and assigned a value contradicting the
assertion that pinned it. Both are worth fixing together by whoever owns model
construction.
