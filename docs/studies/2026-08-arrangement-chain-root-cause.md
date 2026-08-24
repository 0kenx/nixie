# Arrangement round root cause: truncated pair enumeration; complete chain fix; backstops removed (2026-08-24)

## Answering the question honestly

Asked "did you dig to the root cause of the false sat?", the honest
answer at the time was **no**: I bisected to the flipping commit,
characterized the *class* (trajectory-dependent coverage), and built an
exit gate that converted the wrong answer into an honest `Unknown` — a
backstop that (as flagged in review) **hid the real bug** and duplicated
the verification certified mode already performs.  This study records
the completed dig, the fix, and the backstop removal.

## The dig (on the false build, 9345d77)

1. **Reproduce**: clean rebuild of the flipping commit answers `sat`.
2. **Scanners** (`OXIZ_SCAN_VIOL`, debug build): the false model carries
   an `[viol]` — an equality atom whose operands the arithmetic model
   maps to equal values, assigned false — and a stack of
   `[cgap] PROPAGATION GAP`s: apps whose args are arith-equal in the
   model but EUF-distinct.  Extending the scanner to dump the args
   reduced the whole stack to ONE root pair: **`t1031 ≡ t945` (both at
   model value 1, never merged)**; every gap is a congruence cascade
   from it.
3. **Round instrumentation** (`OXIZ_ARR_TRACE`): the round ran on every
   candidate — the defect was inside it:
   * 6 value-groups, **~790 candidate pairs**, Phase 1 probes only **64**
     (cap), in `FxHashMap` group iteration order.
   * The fatal pair was probed **only against other partners**
     (`x=1297 y=1031`, `x=1145 y=945`, …) — never `(1031, 945)`
     itself: the `i<j` double loop truncates before generating it.
   * Phase 2 (full-arrangement check) is *also* truncated: 32-merge cap
     plus a **break at the first conflict during accumulation**
     (requesting splits for a partial prefix only).
4. **Consequence**: the split atom `(= 1031 945)` was never
   internalized → CDCL never had that branching dimension → the model
   kept both at 1, EUF never merged, congruence never fired → `sat`.

**Why the perturbation flipped it**: term-id shifts change `FxHashMap`
iteration order → a different 64-of-790 subset.  The good trajectory
enumerated the fatal pair; the bad one didn't.  Any clause-DB change is
such a perturbation — the same class as the wisas wall-clock bug.

## The fix

Phase 2 now merges a **spaning chain per value-group** (consecutive
terms; a chain realizes the same partition as all-pairs merging at
O(group) cost) — **no caps, no early break**.  Verified on the *false*
build first: with trie-vivify still present, cxs-bp answers `unsat`
with the chain fix alone.  Phase 1 (per-pair diseq derivation) keeps its
cap — it is an optimization; completeness comes from Phase 2.

## Backstops removed (per review)

`model_violates_euf_congruence` at the quantifier-free `Sat` exit
(`04329ea`) and the congruence canonicalizer (`c135d6f`) are **removed**:
they papered over this exact bug, and certified mode (sat verification +
LRAT unsat gating, `SolverConfig::certified()`) is the verification
surface.  The pre-existing quantified-path gate (pr30#3) predates this
work and is left for its own root-cause dig.

## Results

| instance | verdict | z3 |
|---|---|---|
| pete family (cxs-bp, 5s, cxs-bp-ex, cxs-bp-safety, 6stage-flush, **25s**) | `unsat` | unsat |
| wisas xs_8_13 | `unsat` | unsat |
| sorted_list_insert_noalloc1 | `sat` (no canonicalizer needed) | sat |

Differential: **0 wrong verdicts**, solved back to 160 (the gate had
cost 158).  Full suite 10 083, clippy/fmt/doc, Z3 parity 168/168.

## Lesson (added to the pile)

The exit gate was the wrong reflex even as a temporary measure: it
removed the failing canary (`sat` → `unknown`) while leaving the bug,
and its "honesty" made the suite greener.  When a differential flags a
wrong answer, the next step is the scanner/instrumentation dig to the
specific pair/atom — the backstop reflex converts evidence into noise.
