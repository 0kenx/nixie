# LIA on wide integer literals: a panic at `i64::MAX`, `Unknown` beyond

**Status:** found, reported, not fixed. Reproducers below.
**Found by:** the TLA+ front end's encoder cross-check
(`nixie-tla-check/examples/encodecheck.rs`), 2026-09-13.

## Summary

Three defects in integer arithmetic, all reachable from ordinary SMT input and
none needing TLA+ to reproduce:

| Input | Expected | Actual |
|---|---|---|
| `(9223372036854775807 + 1) = 9223372036854775808` | `unsat` on the negation | **panic** in `num-rational` |
| `(18446744073709551615 + 1) = …` | `unsat` on the negation | `Unknown` |
| `(26 div 2) = 13` | `unsat` on the negation | `Unknown` |

The panic is the serious one. `num-rational-0.4.2/src/lib.rs:481` raises
`attempt to add with overflow`, so the arithmetic path is carrying a
**fixed-width** rational somewhere rather than a `BigRational`. The release
profile sets `panic = "abort"`, so in a release build this is a process abort
on a valid query.

`AGENTS.md` names this class directly: *"Wide bit-vectors and bignums are
exact. `>64`-bit BV constants, `BigUint` / `BigRational` paths … never truncate
to `u64`/`f64` for convenience. Truncation has already produced both false
`sat` and false `unsat` in this codebase."*

The two `Unknown` results are sound — `Unknown` is never a wrong answer — but
they are completeness gaps that matter in practice: a specification doing
integer division is undecidable through this path, and `\div` and `%` are
everywhere in real TLA+.

## Reproducers

`cargo run -p nixie-tla-check --example widerepro` builds the terms directly
with `nixie-core`; no TLA+ is involved.

```rust
let mut tm = TermManager::new();
let a   = tm.mk_int("9223372036854775807".parse::<BigInt>()?);
let one = tm.mk_int(1);
let sum = tm.mk_add([a, one]);
let exp = tm.mk_int("9223372036854775808".parse::<BigInt>()?);
let claim   = tm.mk_eq(sum, exp);
let negated = tm.mk_not(claim);      // valid claim, so this must be unsat
let mut s = Solver::new();
s.assert(negated, &mut tm);
s.check(&mut tm);                    // panics
```

The boundary is sharp:

```
2^62 - 1                   Unsat (correct)
i64::MAX - 1               Unsat (correct)
i64::MAX                   panic: attempt to add with overflow
2^64 - 1                   Unknown
2^96 - 1                   Unknown
```

`i64::MAX - 1` is fine and `i64::MAX` is not, which points at an `i64`-width
accumulator that overflows on the `+ 1` rather than at the literal's own width.

For the division gap:

```
26 \div 2  ->  Unknown      (26 * 2 is fine, so it is specific to div/mod)
26 % 4     ->  Unknown
```

## Where to look

The panic is inside `num_rational`'s `Add`, so the caller is holding a
`Ratio<i64>` (or narrower) where a `BigRational` is needed. Start from the
simplex/LRA bound representation and the LIA literal path in
`nixie-theories/src/arithmetic` and `nixie-theories/src/lra`, and check every
`Ratio<` instantiation for a fixed-width parameter.

The `div`/`mod` incompleteness is separate and probably in the LIA
preprocessing that turns `div`/`mod` into their defining constraints: on two
literals it should constant-fold, and evidently does not.

## Why this was not caught before

Nothing in the existing suites builds a literal near `i64::MAX` and adds to
it. The TLA+ front end reached it immediately because real specifications use
`\div` for layout arithmetic and because the front end's own test corpus
includes wide literals — `nixie-tla` deliberately routes numerals through
`BigInt` so that a 96-bit constant survives lowering exactly, and that is what
delivered one to the solver.

A new front end exercising an old core along different paths is worth having
for exactly this reason.

## Status of the front end's tests

`nixie-tla-check/tests/encode.rs` asserts only the **sound** property for these
cases — that a valid claim never comes back `Sat` — so the suite stays green
and keeps passing once the gap is closed. This study is what records the gap;
the tests are not a substitute for it.
