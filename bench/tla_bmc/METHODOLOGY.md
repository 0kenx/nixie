# TLA+ bounded model checking — methodology

## What this measures

`nixie-tla-check::bmc` is the first path in the repository that runs a TLA+
specification all the way to a solver verdict: parse → lower → infer types →
encode → CDCL(T). This harness (`nixie-tla-check/examples/bmccheck.rs`) runs it
over the external corpora and reports **why each specification could not be
checked**, not just how many were.

The breakdown is the point. A single coverage percentage says nothing about
what to build next; a table that names the blocking construct sizes the
remaining work directly.

## What a verdict means, and what it does not

| Outcome | Claim |
|---|---|
| `Violation { step: k }` | a counterexample of exactly `k` steps exists |
| `NoViolationWithin(k)` | **no** counterexample of `k` steps or fewer exists |
| `Unknown(why)` | the solver did not decide |

`NoViolationWithin` is deliberately not called `Safe`. Bounded model checking
is a bug finder: a `k`-step search that finds nothing is silent about step
`k+1`. There is no `Safe` variant in the enum, so it cannot be reached for by
accident. Proving an invariant needs O2's CHC lowering to `nixie-spacer`.

## Three ways a verdict can be about the wrong specification

Every one of these was found by reading the specifications behind reported
violations rather than by trusting the count. A checker that is *correct* about
the formula it was handed can still answer a question nobody asked.

### 1. `ASSUME`

A TLA+ specification is claimed to hold **under its assumptions**, which are
usually the only thing pinning down a `CONSTANT`. Ignoring them turns "this
invariant holds for the intended parameters" into "…for every value of `N`" — a
strictly harder claim that fails on correct specifications. The resulting
`Violation` is a real model of the encoded formula and a false alarm about the
specification.

`Bmc` asserts every `ASSUME`. One it cannot lower, type or encode is **dropped
and counted**, never approximated: dropping weakens the search, so it can
manufacture a counterexample but never hide one. `dropped_assumptions()`
surfaces the count, and the harness marks any violation found under a dropped
assumption as possibly spurious.

### 2. Apalache's `ConstInit`

A specification run with `--cinit=ConstInit` pins its constants in a definition
rather than an `ASSUME`, so a checker reading only `ASSUME` sees completely
arbitrary constants. `Bug1023.tla` in Apalache's own test suite is exactly this
shape, and it produced a violation before the convention was supported.
`Bmc::prepare` takes extra constraint definitions for this; the harness picks
up `ConstInit`, `CInit` and `ConstantInit` when present.

### 3. The `.cfg` file

TLC's configuration can replace a `CONSTANT` **or a definition**:
`ConfigReplacements.tla` replaces `Value`. A verdict reached without reading
the `.cfg` may be about a different specification. Not yet parsed; the harness
reports when a `.cfg` exists next to a specification whose invariant it found
violated, so the number is visible rather than silently folded into the total.

## Level checking is part of correctness here, not tidiness

An invariant must be a **state** predicate. `UnchangedAsInv1663.tla` has
`Inv == UNCHANGED x`, an *action*. Encoded at depth 0 with no transition
asserted, the next-state value is unconstrained, so `~Inv` is trivially
satisfiable and the checker reported a violation — a faithful reading of the
formula and a meaningless statement about the specification.

`Bmc::prepare` now rejects it: `Init` and `Inv` must be at most `State`, `Next`
at most `Action`. The gate is **one-sided**, matching the rest of this front
end: `trusted_level_of` returns `None` when a level depends on an unresolved
name, and an unproven level is never grounds for rejection. Only a level that
was *proved* too high is.

## How to run it

```bash
export NIXIE_TLA_LIB=../temp/communitymodules/modules
cargo run --release -p nixie-tla-check --example bmccheck -- $(find ../temp/tlaplus-examples ../temp/apalache -name '*.tla')
```

`NIXIE_BMC_DEPTH` sets the bound (default 4).

The harness finds `Init`/`Next`/`Inv` by convention, which is a deliberate
approximation: the authoritative source is the `.cfg`, and until that is parsed
the numbers describe the specifications the convention happens to match, not
the corpus as a whole. `with an Init/Next/Inv triple` is reported separately
for exactly that reason.
