# Issue #28: --view, view-distinct --max-error, and real symbolic simulate

**Date:** 2026-11-23
**Issue:** #28
**Landed from:** worktree `tla-28-view-simulate`

## What landed

### `--view=V` and view-distinct `--max-error`

- A reported counterexample is now blocked **under the view** when one is
  set: at each step, the view's *value* — computed by the evaluator over
  the decoded state, the semantic truth the trace carries — is ruled out
  against the view's own encoded term (`Encoder::encode_at` at that step),
  so the next query must differ where the author looks. A step whose view
  value has no term form falls back to the full-state block, which is
  stronger and therefore sound.
- `--max-error > 1` **without** a view is refused with exit 255, exactly as
  Apalache refuses it (`ApalacheConfigResolver`): without a view, further
  counterexamples are near-duplicates, and the combination promises a
  diversity nothing can deliver. The old note ("--view is not used") is
  gone; a view that names nothing, or sits above state level, is refused
  by name.
- The `max_error_yields_distinct_counterexamples` CLI test is extended to
  the issue's distinct-by-view acceptance, with a no-view refusal test and
  a test that three traces of a two-counter walk are pairwise distinct in
  their viewed (`x`) histories however their `y`s scatter.

### `simulate` — sampled behaviours, not a search

- `Next`'s top-level disjuncts are decomposed (`disjuncts_of`); at each
  step of a run they are tried in a **seeded** Fisher-Yates order
  (SplitMix64, `--seed=N`, default 0 — no clock, no OS entropy) and the
  first *enabled* one (prefix ∧ disjunct satisfiable) is asserted for the
  run. A run with no enabled disjunct dead-ends; a state invariant broken
  in a reached state is decoded and **replayed** before it is reported —
  a sampled trace that does not replay is `Unknown`, never exit 12.
- `--output-traces` writes `example<k>.itf.json` per run: the violating
  run's trace, and every completed run's trace read back from the solver
  (`--max-error`'s `write_itf_as` machinery, sharing `render_itf`).
- "No error" says what it means: `NoError in N sampled run(s) (D
  dead-ended early); this is a sample, not an exhaustive search`, exit 0.
- Determinism pinned: the same seed gives byte-identical example files
  across runs (a CLI test asserts it).

### The fix the y2k cell exposed

`y2k_instance.tla` takes `Init`, `Next` and `Safety` from an **unnamed**
`INSTANCE y2k WITH …`, so the roles name members that are not units of
the root module. `lower_named` now falls back to open-instance members —
lowered through the instance machinery, substitution and all, via a
pre-seeded frame stack (`run_frames`) — and both the CLI's and
`lower_one`'s existence checks accept them. The y2k simulate acceptance
cell (`--out-dir --length=10 --max-run=5 --output-traces --inv=Safety`)
now produces `example1..5.itf.json`, `NoError`, exit 0, byte-identical
across runs.

## Verification

- tla crates: 612/612 tests; workspace suite: green except the two
  pre-existing `nixie-solver` failures inherited from the base (unrelated;
  no dependency edge).
- clippy/fmt/doc clean.
- Apalache parity (123 cells): `NestedCallByName` Declined→**Agree-Ok**
  (the y2k-family fix reached it), no cell worsened; the remaining
  mismatches are the same pre-existing temporal/variant cells as main.

## What is deliberately not claimed

Simulation is a sampler: `NoErrorInSampledRuns` is a statement about the
runs taken, and the outcome line says so. Nothing here bounds what a
longer or luckier search would find.
