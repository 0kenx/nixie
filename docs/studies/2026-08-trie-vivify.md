# Trie-shared vivification (POS'25 mechanism): LANDED, then REVERTED after the SMT differential caught a trajectory-crossed false-SAT (2026-08-24)

## History of this study

1. **First filing**: component gate passes (39% fewer in-pass propagations),
   end-to-end neutral (0.9897) — filed REJECT, then reclassified NEUTRAL
   under the ±5% band, then **LANDED** under the band rule's landing
   corollary (above-band component win + neutral end-to-end + "no new risk
   surface").
2. **This revision**: the landing's "no new risk surface" claim was
   **factually wrong**, and the error surfaced as a live false-SAT.
   **Reverted.** The mechanism data below stands; the landing decision did
   not survive contact with the SMT path.

## What the landing got wrong

The landing claimed: *"Default search paths are untouched — vivify runs
only under the opt-in inprocessing bundle."* That is true for the DIMACS
`CaDiCaL` preset and **false for the SMT path**: `oxiz-solver`'s
`SolverConfig::default()` is `balanced()`, which sets
`enable_inprocessing: true`, threaded verbatim into the embedded SAT core
(`solver/mod.rs` `sat_config`).  The CDCL(T) search therefore runs
`inprocess()` mid-search, and `inprocess()` ends with an unconditional
`vivify_clauses()` call.  The trie rewrite (candidate reordering) changed
strengthening inside that bundle → different clause DB → different CDCL(T)
trajectory corpus-wide.

## The failure

`smt-lib/non-incremental/QF_UFIDL/pete/cxs-bp.smt2` (z3: `unsat`):

| build | verdict |
|---|---|
| `8db2f3c` (arrangement round) .. `b07c12c` (SOI), clean builds | `unsat` |
| `9345d77` (trie-vivify) .. HEAD, clean builds | **`sat` (false)** |

Bisected with clean per-commit worktree builds (two independent from-
scratch builds of `9345d77` produce byte-identical binaries — the solver
is per-build deterministic — so the flip is a real trajectory change, not
build noise).  With the trie-vivify diff alone reverted from HEAD,
cxs-bp returns to `unsat` and wisas stays `unsat`.

## Two findings, one revert

1. **The landing decision was invalid** (my error): the corollary's
   "no new risk" clause was evaluated against the DIMACS presets only.
   A SAT-core change is an SMT-path change whenever the embedded core
   executes it — which inprocessing-on-in-CDCL(T) does.  The corollary
   in `BENCHMARKING.md` is amended accordingly (see below).
2. **The deeper, pre-existing fragility**: the arrangement round
   (`8db2f3c`) closes the pete false-SATs *on the trajectories it was
   measured on*; a clause-DB perturbation suffices to steer the search
   onto a trajectory where a candidate model escapes the round (its
   merge caps or pair coverage) and the non-convex hole reopens.  This is
   the wisas wall-clock lesson in a new shape: **a correct verdict that
   depends on trajectory luck is not closed**.  The follow-up is to make
   the arrangement round's coverage unconditional (or its residual gap
   an honest `Unknown`), independent of which candidate the search
   reaches; until then any SMT-path perturbation can re-cross this
   boundary, and differentials must gate every SAT-core landing.

## Verification of the revert

Full suite 10 082, clippy/fmt/doc, Z3 parity 168/168; differential
(`trie-vivify-revert`): **0 wrong verdicts**, cxs-bp `unsat` (serially;
`timeout` at the 10 s parallel cap), wisas `unsat`.

## Disposition

**REVERTED then RELANDED (same session, 2026-08-25).**  The revert stood
because the false-SAT root cause was open.  It has since been closed at
`a5f97b9` (complete spanning-chain arrangement — the round's Phase 2 has
no caps and no early break, so its coverage no longer depends on which
candidate the search reaches; see
`docs/studies/2026-08-arrangement-chain-root-cause.md`).  The disposition
required either (a) SMT-differential cleanliness at the landing commit
or (b) a flag the SMT path leaves off.  (a) is now demonstrated:

| gate | result |
|---|---|
| differential (270 files), run 1 | 0 wrong, solved 160, cxs-bp `unsat` |
| differential, run 2 | 0 wrong, solved 160 (the one-run 159 was parallel-load noise — all 10 "lost" files byte-identical on targeted serial re-runs) |
| Z3 parity | 167/0/1 — identical to pre-change |
| canaries | cxs-bp `unsat`, 25s `unsat`, wisas `unsat`, sorted_list `sat` — all hold WITH the perturbation present |
| SAT A/B (60 satcomp files) | 0 verdict mismatches, 0 TO asymmetry, 22/22 both-solved; multi-second files at 1.01–1.02 (neutral, consistent with the original 0.9897) |
| full bar | 10 100 tests, clippy/fmt/doc |

The re-applied diff is the original `9345d77` `learn.rs` change verbatim
(candidate reordering + shared-prefix reuse with lockstep per-index
depths); the surrounding code had drifted, so the superseded
`vivify_clause` was removed and three clippy findings fixed.  The
component win (39% fewer vivify-internal propagations, identical
strengthening) stands unchanged.  **The landing's lasting lesson**: the
original flip was a real bug in the arrangement round, exposed by — not
caused by — this perturbation; a trajectory change that flips a verdict
is a detector, and the fix belongs in the detector's target.
