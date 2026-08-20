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


## Follow-up: conflict scheduling landed (the mechanism behind the verdict)

Root-causing *why* the stack regressed easy files while cadical never does:
cadical schedules every inprocessing pass on the **conflict clock** (first
elim phase ≈ 1e4 conflicts, `eliminit`); an instance that solves earlier
never runs a single pass.  Measured: on `ITC2021_Early_3` cadical
eliminates **zero** variables (it finishes in 1164 conflicts), while our
pre-search collapse — a port invention, not cadical semantics — eliminated
1903 and needed 5040 conflicts (34× our own default's 149).  The
pre-search fixpoint also paid cost on every instance regardless of need.

**Landed**: `SolverConfig::presearch_collapse` (default `false`,
cadical parity).  With it off, the pre-search BVE fixpoint / ELS one-shot /
inprocess+probing+vivify pre-passes are skipped; the passes run on the
conflict schedule instead — `eliminating()` fires the first elimination
phase unconditionally once `lim_elim` (= `elim_interval`) is crossed, and
the one-shot ELS gets its own trigger on the same clock (independent of
`enable_bve`, so `EQUIV=1` alone keeps its meaning).  The old behavior is
preserved behind `presearch_collapse: true` (the pr26 mechanism tests opt
into it).

**Evidence** (study knob `OXIZ_SCHED_PARITY=1` = the landed behavior):
single-run A/B/C on 8 files — every easy-file regression gone
(ITC 159G→0.6G, worker_20 8.3G→0.1G, Break 3.1G→0.3G, all == default), win
files improved beyond the plain stack (6s167 66→46G, mrpp 287→96G,
circuit 564→348G); two stack-only solves lost (mdp_28, 6s167b — both
T/O for default anyway).  Then **10 seeds × 6 files × 3 arms** (150 s cap):
SP vs plain stack — **48/60 pairs faster, geomean 6.26×, sign p<1e-4**,
equal completions (60/60 both), SP vs default 20/45 faster (geomean 1.22×,
p=0.55 — i.e. the scheduled stack is default-neutral on this mixed set
while plain stack was strictly worse); **0 verdict disagreements** in all
180 runs.  Landed behavior re-verified equal to the study arm (6s167
46.4G, ITC 0.7G, worker_20 0.1G).

This supersedes the screening-study conclusion's caveat: the stack's
easy-file cost was an artifact of *when* the passes ran, not of running
them.  The defaults question (all passes still opt-in) remains closed per
the pre-registered rule — but the entry bar for reopening it is now much
lower, since the scheduled stack no longer regresses the easy stratum at
all.

**Full-corpus single-seed snapshot** (canonical seed, 94 files, default vs
scheduled stack): completions 79 vs 80 with churn both ways — the scheduled
stack adds mrpp, both `circuit_48in64` files, `noL_11_14`, `adf6dacd`
(default T/O on all five) but loses `mdp-28`, `pb_300_09`, `crypto…seed102`,
`frb45-21-2` (default solves all four); 0 verdict disagreements.  On the
commonly-solved set the scheduled stack's ratio-vs-CaDiCaL geomean is
**1.42× vs default's 1.10×** — the mid-search passes (probing every 5 000
conflicts, inprocess rounds) still cost more than they save on the broad
middle of the corpus.  So the pre-registered conclusion stands unchanged
even after scheduling: **stack stays opt-in**; scheduling removed the
pathology (easy-file cliff) but not the case for defaults.  The 10-seed
"SP vs default neutral" reading above was a property of that 6-file
hard-skewed sample, and is hereby qualified.
