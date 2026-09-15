# The untraced fast path: killing the certificate tracer's per-S-pair cost

**Date:** 2026-09-16
**Scope:** the #1 lever named by
`docs/studies/2026-09-16-ff-chain-frontier-budget-honesty.md` — the
measured ~1 s-per-S-pair cofactor-row maintenance on 96-input cascades.
**Verdict:** **ship** — chain 64×96 `sat` (the named frontier goal), every
corpus goal held or improved 4–400×, verdicts unchanged, and the
load-bearing invariant (untraced ≡ traced trajectory) pinned by a
property test.

## The mechanism

The tracer's cost lives entirely in `TracedPoly`'s row-mapping operations
(`sub`/`add`/`neg`/`scale`/`mul_monomial` each rebuild the full
`n_inputs`-wide cofactor row). The fix gates every one of those mappings
on `cofactors.is_empty()`: an element constructed with an **empty row**
stays empty through the whole cascade — no per-op row work anywhere, and
the gating propagates automatically through every shared code path
(S-pairs, reductions, tail reductions, inter-reduction). Two entry
points share one implementation (`grobner_basis_inner`):
`grobner_basis` (rows, as always) and `grobner_basis_untraced` (empty
rows).

The budget charge follows the work really done: the cofactor charge uses
`current.cofactors.len()` — `n_inputs` when traced, **0** when untraced
(the earlier honesty fix would otherwise over-charge the fast path
n×-into-uselessness).

## Where it runs (and where it must not)

* **Wide monolithic components** (`inputs ≥ 40`): the fast path first. If
  the completing basis contains a constant (the traced-UNSAT witness is
  needed), ONE traced re-run recovers it — a completing cascade
  reproduces its trajectory, so the re-run yields the identical basis
  with rows; UNSAT costs ≈ what a traced-only world pays (no regression),
  and SAT gets the n× speed. Case-tree tracking is explicitly disabled
  on untraced roots (empty rows would compose to silently-zero
  memberships — fail-closed by the verifier, but wrong to mint);
  branch-exhaustion certificates for ≥40-input components downgrade
  honestly, as they already did whenever the tracking budget aborted.
* **The split basis** (`split_grobner_basis`): always untraced — its
  merged inputs are not replayable and no certificate is ever minted
  from it; the rows were pure overhead.
* **FindZero's branch children**: untraced whenever tracking is off
  (the existing `tracking` flag routes it).
* **Below the threshold**: everything exactly as before — the certified
  suites (tiny goals, all < 40 inputs) still mint ideal-membership and
  case-tree certificates; the tiny-prime oracle is unaffected.

## The invariant, pinned

`ff_gb_traced_untraced_identity.rs`: for random planted systems at
3×4…17×20, `grobner_basis` and `grobner_basis_untraced` must agree on
completion-vs-budget AND produce element-for-element identical basis
polynomials. Divergence would mean the rows influence the trajectory —
a soundness-relevant coupling of certificate bookkeeping to the search.
This is also what the UNSAT traced re-run relies on.

## Measurements (release; first run quiet load ~8, re-run under load ~14–30)

| goal | honesty landing | fast path (quiet) | fast path (loaded) |
|---|---|---|---|
| bn254 chain 64×96 | 150 s+ timeout | **`sat` 1.24 s** | `sat` 3.25 s |
| bn254 chain 32×48 | `sat` 53 s | **`sat` 0.13 s** | `sat` 0.97 s |
| bn254 chain 16×24 | `sat` 0.07 s | `sat` 0.07 s | `sat` 0.19 s |
| bn254 chain 128×192/256×384 | 150 s+ grind | **`unknown` 2.7/2.9 s** | `unknown` 5/9 s |
| bn254 sparse 128×192 | `sat` 4.6 s | **`sat` 0.21 s** | `sat` 0.24 s |
| all small/sparse/goldilocks goals | held | held | held |

The named frontier goal (chain ≥64×96 capacity) is half-closed: 64×96
solves; 128×192 and 256×384 refuse honestly in seconds (the refusal
*time* is now the honest budget, not a wall-clock grind). The remaining
frontier is chain ≥128×192 — see below.

## What remains (revised frontier)

* **Chain 128×192+**: the monolithic fast path budget-outs (the cascade
  is genuinely large), the split runs untraced and fast, and FindZero's
  lazy round-robin exhausts its node budget. The next lever is the
  pre-registered **branch-variable selection** (product-variable-first
  ordering would propagate earlier) — now measurable because everything
  upstream is fast — and it needs the matched-null discipline of
  `docs/BENCHMARKING.md`. F4 remains orthogonal.
* **Certificates on the fast path**: a traced re-run could equally
  recover case-tree tracking after a find_zero exhaustion (re-run
  monolithic traced + re-search); deferred until a corpus goal needs it.

## Soundness accounting

Rows never influence reductions (now pinned by the identity test); the
fast path only skips bookkeeping. UNSAT verdicts from wide components
re-run traced before `traced_unsat` — the witness carries real rows. SAT
verdicts never needed rows. Case-tree tracking is gated off on untraced
roots. All oracle suites (exhaustive tiny-prime verdicts + certificate
corruption rejections + planted fuzz at real primes) and the certified
solver regressions are green unchanged.
