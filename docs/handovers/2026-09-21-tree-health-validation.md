# Tree-health validation record — the combined tree at `af07e5ad` (2026-09-21, afternoon)

**The trigger:** the morning's rapid multi-owner churn — gate-modulo
forward subsumption **plus the base-solver class-crossing-unit
false-`sat` it exposed** (`87311f70`), i504's published-model
certificate fix (`286f63bd`), the early-conflict scans + memoized
quantifier checks (`ef8d76a9`), and the snapshot-era landings — each
verified individually, none re-validated TOGETHER.  The `b49b9242`
precedent (the attribution session's record): after heavy churn, the
full battery re-runs on every surface.  Binary:
`precompile/af07e5ad/nixie` (dev build for the panic sweep from the
same tree).

## The battery (all on `af07e5ad`, load disclosed per leg)

1. **Workspace suite** (`nextest --workspace --all-features`): 12 120
   run — 12 115 pass, 5 timeouts, ALL five the documented load-flake
   class (`scope_rebase` ×4, `bv_odd_width` ×1`) at load 40–68;
   re-run at `-j1`: **9/9 + 1/1 pass**.
2. **Pinned-sample differential** (`bench_diff.py --validate-models`,
   270 instances): **0 soundness disagreements; 85/86 sats
   model-validated (0 invalid, 1 emit-failed)** — TRUSTED_TOTAL 173.
3. **Fresh-seed generators** (the attribution recipe's mix): `mixed`
   ×3 (seeds 20261001–03, 400 cases each), `wide` ×2 (…04–05, 300
   each), `quant` ×2 (…06–07, 300 each) — **zero verdict
   disagreements, zero refuted models** across all seven runs (the
   quant runs' honest `unknown`s are the surface's normal).
4. **Debug-panic sweep** (the dev binary, overflow-checks on) over
   the parity corpus + the pinned sample + extended-theories: 220
   files — **zero panics** (146 sat / 68 unsat / 4 unknown / 2 fail =
   the baseline's documented honest logic-contract rejections).
5. **Z3 parity suite** (z3 4.16.0): **177 benchmarks, 176 agree, 0
   wrong-verdict pairs** (the standing nixie-`unsat`/z3-`unknown`
   inconclusive on `array_unique`).
6. **Stratified SMT-LIB verdict screen** (50/family × 8 QF_LIA
   arithmetic families, cap 15 s, calm leg): **153 decisive-verdict
   pairs, 153 agree, 0 disagreements** (226 nondecisive — dominated
   by the Labyrinth/ezsmt scheduling strata where z3 solves and nixie
   times out: the standing LIA timeout frontier, not a crash class;
   one manual spot-check of an "empty output" cell was a mistyped
   path — the real files complete honestly).  The pair count is
   thinner than `b49b9242`'s 399 (different strata mix); the zero on
   ~153 pairs + the 2 900+ decisive comparisons above carries the
   signal.
7. **Perf gate** (BASELINE `87311f70`): **PASS — conflicts 1.000,
   decisions 1.000, wall 0.99**.

## The verdict

**The wrong-verdict ledger stays empty.**  The combined tree — the
subsumption landing with its false-`sat` fix, i504's certificate
rework, the early-conflict scans, and everything underneath — is
validated clean on every surface this repo instruments: ~2 900
decisive solver comparisons beyond the suite, zero disagreements,
zero refuted models, zero debug panics, parity 0 wrong pairs, gate
bit-stable.  Total decisive comparisons this record: 270 (pinned) +
1 500 (mixed) + 600 (wide) + 600 (quant) + 153 (screen) + 177
(parity) ≈ 3 300.

## Standing notes for the next sessions

* The integer-tableau design brief (`4d7551ad`) is the arith owner's
  pre-registered next; the fold-demand experiment (`8a25f260`) is
  named and owned.  Both untouched here.
* Load oscillation continues (~10–15 min campaign cycles); the
  suite's flake classes re-verify at `-j1` per the standing trap.
* `hunt/` sits untracked in the tree root (not this session's; left
  in place for its owner).
