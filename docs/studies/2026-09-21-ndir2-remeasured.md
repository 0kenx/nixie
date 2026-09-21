# `NIXIE_S6_NDIR2` re-measured on the transformed tree — the deflection wall dissolved, the gate still buys nothing (2026-09-21)

**Date:** 2026-09-21 (evening).  **Item:** the wide-LP handoff's
standing item 6 — *"the trade map predates the wide-LP build;
re-measure it against the new baseline before deciding"* — unblocked
because the armed/default A/B is self-paired (same binary, env
toggled), needing no BASELINE pin.  Binary `precompile/fa30412c`
(branch channel + Bareiss + integer-tableau Phase 1 + the fused
tokenizer + everything through the graph repair), z3 4.16.0 where
used, counters primary throughout, load disclosed per leg.

## The four surfaces (armed = `NIXIE_S6_NDIR2=1`, default = the landed
wide+pinned scoping)

1. **The named deflection cell (fi1)** — the original map's headline
   cost (the chain/fi1 trajectory deflected into the unpivotable-wide
   convergence wall: `unknown`, then a 180 s timeout after the repair
   step).  **DISSOLVED**: fi1 answers `sat` at **10/10 seeds armed**
   (48 ms-class, same as default).  The value-overflow migration
   (item 49), the wide-LP store, and the integer-tableau rounds
   removed the wall the deflection used to hit — the cost cell the
   gate was kept off FOR is gone.
2. **The MBQI cadence cell** (the original screening failure — the
   per-final-check derivation cost on wide-free instances;
   `a_check_leaves_the_mbqi_search_state_where_it_found_it`).
   **PERSISTS**: default completes (188 s at load 57); armed **caps at
   420 s at load 29** — strictly ≥ 2.2× worse on a calmer machine.
3. **The wide win surface** (`wide_fuzz`, 2 fresh seeds × 300, both
   arms, z3-diffed): **zero wins** — seed 20261012's verdict
   distribution is bit-identical between arms; 20261011 is mildly
   WORSE armed (56→55 sat, 2→3 timeout).  The original win class
   (the constructed mixed-magnitude/chain twins) is not a shape
   today's generators emit, and arming closes nothing they do.
4. **The LIA mass** (the powered standard — 10 seeds × 12 standing
   cells): **11/12 cells bit-identical** across all seeds (the landed
   scoping already covers the paying states); the one differing cell
   (`convert/convert-jpg2gif-query-1546`) is a pure cost — default
   declines honestly at 1 293 conflicts, armed burns past a 60 s cap
   (verified a timeout, not a crash), on 6/10 seeds.

## The verdict

**Keep-off stands, now on measured ground instead of a stale map.**
The unconditional direction-2 buys nothing measurable on any current
surface (the wide+pinned scoping captures the whole paying class the
generators can find), and costs on two: the MBQI cadence (every
wide-free instance pays per-final-check) and the convert-class grind.
`NIXIE_S6_NDIR2` remains the probe-only opt-in.  What DID change —
and is worth this record — is the headline cost's mechanism: the
wide-row convergence wall that produced the fi1 deflection no longer
exists on this tree, so any future case FOR the general gate must
rest on new win evidence, not on the old deflection story.

Measurement artifacts: `~/.cache/nixie-scratch/ndir2/` (the per-arm
wide distributions, the 12-cell A/B grid, the jpg2gif armed run) —
numbers recorded above; the scratch is transient.
