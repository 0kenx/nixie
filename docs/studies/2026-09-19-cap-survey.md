# Completeness-cap survey: the set/bag reduction caps stay where they are

**Date:** 2026-09-19 · closes the bags-arc chore "cap re-measurement
(`MAX_BAG_ELEMENTS`/`MAX_BAG_PAIRS`), together with the set caps, once the
TLA+ corpus runs green" — the gate condition was verified green the same
day (`bench/tla_parity` 4,970/0 level mismatches, `bench/tla_eval`
646/0 semantic mismatches vs TLC).

## What was measured

The caps bound the eager reductions' identity products; a firing is a
**completeness** event (the construct is skipped, `Sat` degrades to
`Unknown`, every `Unsat` stays sound). Instrumentation landed with this
study: every cap is now observable (`NIXIE_DEBUG_CAPS=1` prints
`[cap] <name> actual=<n> cap=<limit>` per firing) and overridable
(`NIXIE_CAPS=bag_elements=48,…`) for A/B runs without rebuilds —
`nixie-solver/src/solver/caps.rs`, wired into `bag_theory` and
`set_theory` (`bag_elements` 24, `bag_pairs` 128, `set_count_elements`
24, `set_derived_elements` 24, `set_cone_sets` 40). The survey harness is
`bench/cap_survey.py`.

### 1. Real corpora: the caps cost nothing

| corpus | files | cap fires | verdicts lost |
|---|---|---|---|
| TLA+ (tlaplus-examples + Apalache, via `bmccheck` at depth 4) | 907 | **1 spec** (`Prisoners.tla`, `set_count_elements` at actual 27–36) | **0** — the spec still answers `NoViolationWithin(4)`: the firing weakens the encoding, and the unsat direction stays sound through it |
| Z3 parity corpus | 176 | 0 | 0 |
| SMT-LIB extracts | 108k | 0 (no set/bag surface) | 0 |

### 2. Synthetic spanning shapes: the caps sit at the cost cliff

Bag cardinality chains (`(bag i 2)` left-folded, 4→64 elements) and set
cardinality (`set.insert` chains): at the **default** caps everything
over the cap answers `Unknown` in ≲0.1 s; with the caps raised to
64/512/128 the band just above the cap either decides slowly or — more
often — **times out**:

- bag: n ≤ 16 decides in <0.5 s; n = 24+ times out or stays `Unknown`
  at raised caps (20 s+), where the default answers honestly in 0.1 s.
- set: n = 8 decides in ~2 s; n = 24–25 decides at raised cone caps in
  9–11 s, n = 16/32+ times out (the cost is chaotic, not monotone —
  n = 16 times out while 24 and 25 decide).

## Verdict: keep every cap at its current value

The caps are insurance whose firing has never cost a corpus verdict, and
the completeness a raise would buy is a band that mostly converts instant
honest `Unknown`s into slow timeouts. This is the same conclusion the
`MAX_PAIRS` control run reached ("a control run with these pairs switched
off entirely was no faster on the corpus, so the bound is insurance
rather than a measured hot spot" — `set_theory/mod.rs`), now established
for the whole cap family with the instrumentation to re-check any future
corpus in one run:

```sh
NIXIE_DEBUG_CAPS=1 <any harness> 2>&1 | grep '^\[cap\]' | sort | uniq -c
```

Reopen only if a corpus ever shows fires *and* lost verdicts together
(the `Prisoners.tla` shape — fires but still decides — is not a loss).
