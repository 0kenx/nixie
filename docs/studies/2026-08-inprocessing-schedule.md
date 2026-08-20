# Item 2: inprocessing-schedule study (pre-registered)

Date: 2026-08-19 (pre-registration written **before** any arm was run)
Follow-up to: `docs/studies/2026-08-walk-glue-ema-and-shrink.md` (stack
soundness restored; old 1.74× verdict obsolete).

## Question

With the stack sound (previous study), does any schedule configuration
deliver the stack's completion wins without its easy-file regression — i.e.
is there a case for a defaults change, or does the stack stay opt-in?

## Pre-registered design

**Corpus** (26 files, stratified by default-arm instructions vs CaDiCaL,
seed-42 draw, frozen below):
- 8 *easy* (5× uf100 + 3 satcomp; default ≤ 0.5× of cadical)
- 8 *medium* (0.7–2.0×)
- 6 *hard-solved* (>2×)
- 4 *hard-to* (default timeout, cadical solved)

**Arms** (single run each; env knobs only):
- **A default** — all passes off (current default).
- **B full** — BVE+EQUIV+PROBE+HBP+INPROCESS, ELIM_INTERVAL=2000 (cadical
  `elimint`), INPROC_INTERVAL=5000 (default; mid-search inprocess every 5k
  conflicts).
- **C full+rare-inproc** — as B, INPROC_INTERVAL=50000 (mid-search
  inprocessing ~10× rarer; isolates the scheduled passes' cost).
- **D no-probe** — BVE+EQUIV+INPROCESS (no failed-literal/hyper-binary
  probing; isolates the probe pair, cadical `probeeffort=8‰`, the smallest
  effort of the family).
- **E presearch-only** — BVE+EQUIV, INPROCESS off (pure pre-search collapse;
  no purelit/subsume/vivify/transred machinery at all).

**Metrics**: completions per arm (timeout 240 s); paired
instructions-to-verdict on commonly-completed files, per stratum and overall
geomean; verdict disagreements vs CaDiCaL (must be 0 — any disagreement is a
soundness bug, not a data point).

**Decision rule (fixed now)**: a defaults change requires an arm to beat A on
**both** completions **and** overall paired-instruction geomean, and that win
must then survive a ≥10-seed CRN-paired study with a matched null before
landing. Absent that, the verdict of this study is "stack stays opt-in" plus
whatever per-stratum structure the single run shows (labeled screening, not
proof).

## Results (filled after the run)

See "Results" below.