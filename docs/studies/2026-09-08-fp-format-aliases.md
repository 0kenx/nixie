# FP format sort aliases: `Float32` & co. parsed as uninterpreted sorts

**Date:** 2026-09-08 · **Found by:** directed probe (roadmap item: FP halfway /
subnormal / rounding-mode boundary productions — the probe phase of building
the `fpboundary` obligation family) · **Status:** FIXED, landed.

## Finding

The most basic satisfiable QF_FP shape answered `unknown` where z3 says
`sat`:

```smt2
(set-logic QF_FP)
(declare-const y Float32)
(assert (= y (fp.add RNE (fp #b0 #x7f #b00000000000000000000001)
                           (fp #b0 #x7f #b00000000000000000000001))))
(check-sat)   ; nixie: unknown   z3: sat
```

(and the same for the pinned-operand chain `x = c ∧ y = fp.add(RNE, x, x)`).
Every probe *without* a declared variable (literal operands only) was already
correct — the rewriter folds concrete `fp.*` applications exactly.

## Root cause

`(declare-const y Float32)` resolved `Float32` through the parser's generic
`Uninterpreted` fallback: `y` carried sort `Uninterpreted("Float32")`, while
every term the `fp.*` operators produce carries the real indexed sort
`FloatingPoint { eb: 8, sb: 24 }` (a *different* `SortId`).

The SMT-LIB FloatingPoint theory declares four canonical format aliases as
part of the theory's language — `Float16` = `(_ FloatingPoint 5 11)`,
`Float32` = `(_ FloatingPoint 8 24)`, `Float64` = `(_ FloatingPoint 11 53)`,
`Float128` = `(_ FloatingPoint 15 113)` — and essentially every QF_FP script
declares its variables at one of these names.  With the mistyped sort:

* `FpModelFinder::is_fp_var` rejected the variable (`Uninterpreted` is not a
  float sort), so the concrete model builder could never pin it — instrumented
  run: `values = []` after propagation, every assertion `eval = None`;
* the variable was equally invisible to the pattern conflict checks and to
  the honesty gate's atom walk, so the FP path had nothing to work on and the
  gate correctly answered `unknown` (honest, useless).

This is the same *silently-wrong-sort* family as the earlier `RoundingMode` /
`RegLan` / `declare-datatype` parser gaps (see `parse_sort_name`'s history):
a theory-declared name falls through to the free-sort fallback, nothing
errors, and a whole theory quietly disconnects from its variables.

## Fix

`Parser::parse_sort_name` resolves the four theory aliases to the exact
indexed sorts (nixie-core `smtlib/parser/sorts.rs`), before the alias/datatype/
uninterpreted fallbacks — so the theory names keep priority over a user
`define-sort` of the same name, matching the reference solvers' treatment of
theory-declared sorts.  z3 and cvc5 give these names exactly this semantics
in FP logics.

Verified end to end: the two probe shapes above now decide `sat` via the
concrete model builder (pin → fold → verify), and `(_ FloatingPoint e s)`
spelled out longhand behaves identically (it always did).

## Verification

* New parser unit test: `float_format_aliases_resolve_to_the_indexed_floatingpoint_sorts`
  asserts each alias's resolved sort renders as the indexed
  `(_ FloatingPoint eb sb)` form (a plain `"Float32"` string there means the
  fallback regression is back).
* New end-to-end regression file `nixie-solver/tests/fp_format_aliases.rs`:
  `Float32`/`Float64` definitional arithmetic decides `sat`; the
  `x < y ∧ y < x` chain is pinned **never `sat`** (honest `unknown` today —
  see rung 2 below); `fp.isNaN` witness synthesis through the alias.
* Full gate on the landing tree: build `--all-features`; nextest workspace
  `--all-features` **10666/10666**; clippy `-D warnings`; fmt; doc
  `-D warnings`; z3 parity **170 entries / 0 wrong**, per-environment results
  byte-identical to the committed record; obligation fuzzer medium 58/58 and
  small+stress-heavy 58/58, zero FAIL/CRASH/GENFAIL.

## What this does NOT close (scoped rungs)

1. **The unsat direction through variables** (the fp analogue of the mixed
   parity gap): `x = c ∧ y = fp.add(RNE, x, x) ∧ y = c2` with `c2 ≠
   fold(c, c)` still answers `unknown` (z3: `unsat`).  The rewriter only
   folds literal operands; EUF congruence does not evaluate `fp.add(x, x)`
   when `x`'s class holds a literal.  The principled rung is **fp constant
   folding through EUF class values**: when an `fp.*` op term's operand
   classes all carry fp-literal class values, evaluate via `Ieee754Engine`
   and merge with the folded literal's class (`roots_value_apart` then
   refutes two distinct literals landing in one class).  That is a real
   FP-theory feature (constant propagation with congruence), not a patch;
   the pattern checks in `check_fp.rs` stay as the cheap UNSAT fast path.
2. **`(_ to_fp e s r)` real-conversion folding in the model builder**: a
   probe using `(_ to_fp 11 53 (/ 3.0 2.0))` as the pinning literal did not
   fold (observed while drafting the regression tests; the hex-literal form
   works).  Small, self-contained; fold the conversion in `eval_fp`'s
   `RealToFp`/`ToFp` arms from the exact rational.
3. **The `fpboundary` obligation family** (the roadmap productions that
   motivated the probe) is still worth building — it would have found this
   on day one, and it stresses exactly the boundaries (halfway ties,
   subnormals, rounding-mode asymmetries, special values) where the *next*
   FP gaps will be.

## Reproducers

* The probe battery: `/tmp`-resident during the session; the two shapes are
  pinned verbatim in `nixie-solver/tests/fp_format_aliases.rs`.
* Deterministic single-file repro (pre-fix): the script at the top of this
  document (`nixie` answered `unknown`, `z3 -in` answers `sat`).
