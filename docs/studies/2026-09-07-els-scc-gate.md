# Study: ELS gated by binary-SCC mass — closed at rung 0 (inverted again)

**Date:** 2026-09-07
**Parent:** `2026-09-07-throughput-campaign.md` T3; supersedes the closure
claim of `2026-09-06-els-gate-density-study.md`.
**Status:** CLOSED at rung 0 — the pre-registered separation criterion
fails at every threshold; the A/B was not run (2026-09-06 precedent:
measuring a known-wrong policy is wasted cells).

## Why this study exists despite the prior closure

The gate-density study closed "the last plausible static observable" —
congruence-gate density — because its distribution is *inverted* between
ELS winners and losers.  But its own evidence, and the no-gate study's §8,
point at a different carrier: *"the ELS round's binary-SCC content is
independent of gate structure"* — the zero-gate winners (FmlaEquivChain is
an equivalence chain by construction; x9-09054, stable-300) win through
equivalences already present as mutual binary implications at parse time.
That observable — **the mass of non-trivial SCCs in the parse-time
binary-implication graph** — was never measured.  It is:

* **static** (deterministic, seed- and trajectory-invariant),
* **cheap** (one iterative Tarjan over the BIG, O(V+E), read-only, no
  formula mutation, no pass execution),
* **content-matched** to what the ELS actually folds (the SCC of the BIG
  *is* the ELS's equivalence input, modulo gate-congruence augmentation).

## Hypothesis

ELS (mid-search one-shot or pre-search fixpoint) is net-positive on
instances whose parse-time binary graph already carries large equivalence
mass, and net-negative where it does not (pure trajectory reshuffle).
Then `ELS fires iff scc_mass ≥ K` beats a content-scrambled null firing
on the same number of files.

## Rung 0 (this document's rung): telemetry + separation

1. `SCC_MASS=1` in `stats_solve`: after parse (before any pre-search
   pass), print `vars in non-trivial SCCs`, `largest SCC`, and vars in
   SCCs of size ≥ 3.  Iterative Tarjan, read-only.
2. 3-arm sweep on the standing corpus (54 files, 60 s cap, seed 0,
   `off` / `ELS=1` / `ELS_PRE=1`), collecting scc_mass, gate_count,
   conflicts, verdict — rebuilding the per-file ELS join table on the
   current tree (the September-5 raw logs were scratch; the studies name
   only sample files).
3. **Separation criterion (pre-registered):** there exists a threshold
   K (or a composite `scc_mass ≥ K OR gates ≥ K'`) such that
   (a) every seed-known ELS anchor-winner fires (6s167-opt under either
   arm; the pre-arm winners x9-09054 0.26×, stable-300 0.47×), and
   (b) no known ELS-loser fires (the TO class: rbsat, af-synthesis,
   Timetable; the regressions: mp1, summle_X11112, mrpp-under-pre).
   If winners and losers overlap at every K — close at rung 0 as the
   documented end of the static-observable family, and do not run the
   A/B (measuring a known-wrong policy is wasted cells; the 2026-09-06
   precedent).

## Result (rung 0, 2026-09-07): falsified — the distribution is inverted

`SCC_MASS=1` over all 54 files (parse-time, read-only, after the
deterministic BIG materialization `solve()` itself performs):

* **34 of 54 files have mass 0**, including *every* known ELS
  anchor-winner: 6s167-opt (0), FmlaEquivChain (0), mrpp (0), x9-09054
  (0), stable-300 (0) — and several big losers (rbsat, both mp1) as
  well.
* The highest masses belong to **known ELS losers**: the summle family
  (11 944 / 9 530 / 7 380, SCCs up to size 51; summle_X11112 was the
  11× regression under `ELS_PRE`), g2-slp-synthesis (4 240), then the
  simon family (1 088–1 664, all size-2 chains) and pb_300_09 (3 088).

No threshold separates: `K = 0` fires everything (the measured global
no-go, −9 files at cap), any `K > 0` fires **no winner**.  The
pre-registered criterion ("every anchor-winner fires, no known loser
fires") fails at every K — closed without the A/B.

### Why the hypothesis failed (and what it teaches)

§8 of the no-gate study pointed at "the ELS round's binary-SCC content"
— but that content is the SCC of the graph **after the pass's own
preparation**: gate-congruence augmentation plus the BIG refresh over
learned binaries.  The winners' equivalences are *latent* (congruence-
computable from the circuit structure), not *surface* (mutual binary
implications in the parse-time formula).  A static pre-pass observable
cannot see them without doing the very work whose win/loss is being
gated.

### The static-observable family is now closed four ways

| observable | closure |
|---|---|
| online (round cost, yield, DB shape) | 2026-09-05 §1–2: no separation; win/loss lists are reshuffle |
| congruence-gate density | 2026-09-06: inverted (2 of 3 winners 0 gates, largest loser 4 M) |
| placement (mid one-shot vs pre-search fixpoint) | 2026-09-05 §7: same damage either way |
| parse-time binary-SCC mass | this study: inverted (all winners 0, top losers 7–12 k) |

Any future ELS work must accept the per-file trade-off (the `ELS=1` /
`ELS_PRE=1` arms remain) or build the missing kissat simplification-
fixpoint *content* (kitten sweep — reference-priced at ~1 % corpus
geomean for kissat itself, `--sweep=0` 2026-09-05 §8), not a gate.

**Incidental corpus fact worth keeping**: the summle family carries the
corpus's largest parse-time equivalence structure (SCCs to size 51) and
the simon family is literally equivalence-chain-encoded (every SCC
size 2) — structure that neither the gate nor the SCC observable turns
into a win, consistent with the reshuffle finding.

## Rung 1 (only if rung 0 separates; pre-registered now)

Arms: `base` (ELS off) / `treatment = ELS_PRE=1 + gate(scc ≥ K)` /
`null = ELS_PRE=1 + gate(sha256-file ≥ K')` with K′ chosen for equal
fire counts.  Metrics: conflicts-to-verdict paired geomean T/N ≤ 0.95 AND
solved-at-60 s ≥ base, seeds 0–9 on fired files + 54-file × 5-seed
safety screen, 0-verdict-disagreement rule.  `ELS_PRE` is the carrier
arm (the fixpoint measured 2.8× the folds at equal corpus cost).

## What would falsify the whole direction

Rung-0 overlap (above), or rung-1 T/N ≥ 0.95 with the safety screen
failing.  Either way this document is the closure record: after
binary-SCC mass, no static formula observable remains untested for ELS
gating.
