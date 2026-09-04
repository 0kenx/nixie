# Inprocessing soundness recheck: the preset-blocking defect is closed; presets stay off on performance grounds (2026-08-25)

## Why this recheck

`nixie-sat/src/config_presets.rs`'s module doc shipped every preset with
`enable_inprocessing: false` on the strength of a **soundness defect
inherited from v0.3.2**: "hanging unit at a propagation fixpoint" from
missing watch rebuilds, with a cited repro — `pigeonhole(7,6)` at
`inprocessing_interval: 1` returning `Sat` on an UNSAT instance (debug:
invariant panic; release: wrong verdict).  That claim gated every
inprocessing-family measurement since (the trie-vivify bundle A/Bs, the
OTF screen), because no preset could enable the pipeline.

## Repro attempts — the cited failure no longer reproduces

| check | result |
|---|---|
| PHP(4..9, 3..8) × interval {1, 97, 5000} (18 configs) | `Unsat` in **release** — all 18 |
| PHP(7,6) interval=1 in **debug** (invariants live) | `Unsat`, no panic |
| 80 satcomp files, `INPROCESS=1`, vs **real `cadical`** | **0 verdict mismatches** |

The intervening clause-management fixes closed it without anyone
targeting it: `retire_clause`'s reason fixups + binary-edge purge
(the Break_unsat_06_07 stale-edge re-establishment), the DRAT-deletion
completion, the subsumption promotion rule (`crn_11_99_u`), and
deletion-aware arena reads in BCP (deleted slots read as "no clause").
These are exactly the classes of fix landed through this session's
predecessors.

## The preset question, re-measured with the amortizers landed

The CaDiCaL preset's *other* recorded reason (measured net-negative:
qwh.50 55.7G→1088G instructions) predates trie-shared vivification,
budgeted transred rounds, and on-the-fly vivify subsumption.  Paired
screen on the same 80-file sample (30 s cap, sequential):

| | inprocessing ON | OFF |
|---|---|---|
| solved | 30 | **32** |
| verdict mismatches | — | **0** |

Still net-negative-or-neutral as a preset default today (2 files lost
at the cap).  **Presets stay off** — but now for the honest reason
only.  A PMU-counter A/B with ≥10 seeds per cell is the bar for any
future flip; the INPROCESS=1 verdict cleanliness stands either way.

## Landed with this study

- The module doc's soundness claim replaced with the re-verification
  evidence and the standing performance reason (four inline comments
  and the Industrial preset assertion updated likewise).
- `pigeonhole_inprocessing_interval_1_stays_unsat` regression test —
  the exact cited repro shape, pinning the defect closed; failure means
  presets must be re-audited before anything else ships.
