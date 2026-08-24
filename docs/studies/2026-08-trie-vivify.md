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

Reverted (learn.rs restored to the per-candidate vivifier).  The
mechanism remains real and measured; any RELANDING must first either
(a) demonstrate SMT-differential cleanliness at the landing commit (not
just the SAT corpus), or (b) land behind a config flag that the SMT
path provably leaves off.
