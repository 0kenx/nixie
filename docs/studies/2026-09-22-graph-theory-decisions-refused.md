# Study: theory-directed decisions for graph constraints — the primitive measured and refused (negative)

**Date:** 2026-09-22
**Base:** `fa30412c` (main)
**Verdict:** **NEGATIVE, recorded.** The last untaken lever from the graph
handoff — MonoSAT's `-decide-theories` — is measured on our workloads as a
regression in its natural form and content-free elsewhere. The (default-inert)
wiring lands so the question never has to be re-litigated: `NIXIE_GRAPH_DECIDE`
selects the arms. MonoSAT itself ships `-decide-theories` **off by default**
(`Config.cpp:360`), which this experiment independently reproduces the reason
for.

## The wiring (landed, inert by default)

- `TheoryCallback::suggest_decision() -> Option<Lit>` (default `None`): a
  theory-proposed decision, consulted once per branch before the SAT heuristic
  picks freely; assigned proposals are skipped, and any proposal is a legal
  decision — soundness never depends on the channel.
- `UserCallback` implements it through `UserPropagatorManager::get_decision()`
  (the previously-unwired trait method), mapping the proposed term through the
  watch/literal table.
- `GraphModel::decide()` proposes one undecided reach atom, refreshed by the
  per-run atom scan. Arms via `NIXIE_GRAPH_DECIDE` (OnceLock-memoized):
  `0`/unset = off (default), `1` = first-undecided, **true** (the treatment);
  `2` = last-undecided, true (the matched null — same code path, candidate
  set, frequency, exhaustion timing; the selection content scrambled);
  `3`/`4` = the same pair with **false** polarity (MonoSAT's
  `-decide-theories-reverse` counterpart).

## The experiment

26 instances × 5 arms, one binary, arms by env (perfect common-random-numbers
pairing; every arm deterministic). Corpora: the crafted backtrack-heavy set
(`--clause-size 3 --unit-prob 0.0 --coupling 50`, n ∈ {30,60,90,150},
r=16, seeds 1–3, plus two probes) and the scale corpus (n ∈ {300,500},
r ∈ {8,16}, seeds 1–3). Metric: deterministic solver counters (`STATS=1`),
the house rule.

**The scale corpus never separates the arms**: its reach atoms are fixed by
unit clauses before the first free decision, so the hook returns `None`
forever and all five arms produce identical counters. Only the crafted set
exercises the channel.

Crafted-only decisions geomean vs baseline:

| arm | effect |
|---|---|
| 1 (treatment: first-undecided, true) | **1.600×** |
| 2 (null: last-undecided, true) | 1.462× |
| 3 (first-undecided, false) | 0.981× |
| 4 (last-undecided, false) | 0.979× |

- **The true-polarity treatment is a 60 % decision regression** (conflicts
  0 → 17–83 on the propagation-solved instances): eagerly demanding paths
  before the Boolean search has shaped the edge assignment forces conflicts
  the baseline never takes.
- **Treatment/null = 1.600/1.462 ≈ 1.09** — the residual over the scrambled
  null is inside the neutrality band and rides a regression: there is no
  separable selection-content effect.
- The treatment and null are **bit-identical on 25/26 and 24/26 pairs** —
  with few reach atoms, first-vs-last rarely even differs. The one divergence
  (`craft_n30_s1`: 83/1363 vs 19/385 — 4.4×) is pure CDCL chaos from an
  order perturbation, a live demonstration of §1 of `docs/BENCHMARKING.md`.
- False-polarity arms are a wash (0.98×) with two real single-instance wins
  (`craft_n30_s2`: 13→1 conflicts) balanced by losses — noise-level, and
  treatment==null there too.

Full per-instance matrix (conflicts/decisions):

| instance | base | true-1st | true-last | false-1st | false-last |
|---|---|---|---|---|---|
| craft_n150_s1 | 0/4405 | 51/5961 | 51/5961 | 0/4407 | 0/4407 |
| craft_n150_s2 | 0/1849 | 55/3795 | 55/3795 | 1/2047 | 1/2047 |
| craft_n150_s3 | 0/7804 | 61/9051 | 61/9051 | 0/7803 | 0/7803 |
| craft_n30_s1 | 2/152 | 83/1363 | 19/385 | 2/160 | 2/155 |
| craft_n30_s2 | 13/1007 | 18/1025 | 18/1025 | 1/885 | 1/885 |
| craft_n30_s3 | 3/496 | 18/444 | 18/444 | 2/372 | 2/369 |
| craft_n60_s1 | 0/554 | 36/1656 | 36/1656 | 0/555 | 0/555 |
| craft_n60_s2 | 0/3538 | 20/3689 | 20/3689 | 2/3538 | 2/3538 |
| craft_n60_s3 | 0/979 | 37/1751 | 37/1751 | 0/979 | 0/979 |
| craft_n90_s1 | 2/1105 | 41/1936 | 41/1936 | 0/1104 | 0/1104 |
| craft_n90_s2 | 0/7830 | 17/8569 | 17/8569 | 0/7830 | 0/7830 |
| craft_n90_s3 | 0/1955 | 40/2807 | 40/2807 | 2/1954 | 2/1954 |
| crafted_n500_s1 | 0/35220 | 36/38408 | 36/38408 | 0/35218 | 0/35218 |
| crafted_n90_s1 | 2/1097 | 19/1799 | 19/1799 | 0/1097 | 0/1097 |

## Why this closes the lever

The hypothesis space for "theory-directed decisions help graph solving" in
its atom-proposing form is now measured: the natural polarity is strongly
negative, the reverse polarity is noise, and the selection content carries
no separable signal. What remains unexplored is only *structurally richer*
proposals (e.g. frontier edges chosen from the maintained views, with a
same-pool scrambled null) — a different hypothesis, listed as a follow-up,
not a re-run of this one.

## Verification for the wiring (all arms off by default)

Workspace `--all-features` 12122/12122; perf gate PASS at exactly 1.000
counters (the per-branch consult costs the default path nothing measurable);
MonoSAT differential 300/300; Z3 4.16.0 parity 0 disagreements (re-run after
an aborted first attempt); graph oracles 39/39; clippy/fmt/rustdoc clean on
touched crates. Verdicts identical across all arms on every instance (a
decision-order change cannot flip a complete search's verdict, and none
flipped).
