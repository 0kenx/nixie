# On-the-fly subsumption in vivification (POS'25 Priority-3 slice) (2026-08-25)

## Mechanism (cadical `vivify_deduce` port)

While vivifying C, two events expose a subsumer:
- a **conflict** whose clause D satisfies `D \ {level-0-fixed} ⊆ C`, or
- a later literal of C forced **true** whose reason clause D does.

Then D ⊨ C outright (level-0-false literals are droppable under the
units) and C is *deleted* instead of shrunk.  Commit mirrors
`subsume_round` exactly: promote a learned subsumer to original when C
is original (else reduction could later drop the justification — the
`crn_11_99_u` false-SAT lesson), re-arm elimination, `retire_clause`.

## The bug the port caught in itself

First measurement: `6s167-opt` reported **5380 subsumptions / 6294
candidates** and answered `sat`.  Cadical answers `unsat`.  Root cause:
assuming ¬ of a prefix can make **C its own reason/conflict clause**
(C = (a∨b∨c) under ¬a,¬b propagates c with reason C); the subset test
"C ⊆ C" then passes *trivially* and C was deleted on its own word —
a mass false-deletion that weakened the formula into a false `sat`.
Cadical's `assert (c != subsuming)` is the guard; the port now carries
it (`d_id != cid`), pinned by a unit test.  After the guard: 60/6294
subsumptions on the same file, verdict `unsat` (= OTF-off = cadical).

## A/B (SAT experimental bundle, INPROCESS=1, 70 satcomp files, 30 s)

| | OTF on | OTF off |
|---|---|---|
| verdict mismatches | — | **0** |
| solved | 27 | 30 |
| geomean, >2 s files (8) | 0.949 | 1 |

Mixed: two large structured wins (13.0→7.3 s, 25.5→14.6 s, ~0.57×),
one 1.46× loss, and 3 borderline TO losses (1.3 s / 12.1 s / 27.4 s
files crossing the 30 s cap).  The headline 1.336 geomean over
all both-solved files is sub-second noise (a 403× ratio between two
0-second runs).  **Inconclusive at this sample size** — a matched-null,
multi-seed run is required before any default-on claim on the bundle;
not run here (the bundle is not a shipped configuration).

## Shipped surfaces (the landing evidence)

All SAT presets ship `enable_inprocessing: false` (the module-doc
watch-rebuild defect), so vivify — and this slice — executes only on
the SMT embedded core (`balanced()`) and the opt-in bundle:

- differential (z3, 270 files): **0 wrong verdicts, solved 160
  byte-identical** to pre-change;
- Z3 parity: 167/0/1 identical;
- canaries: cxs-bp `unsat`, 25s `unsat`, wisas `unsat`,
  sorted_list `sat` — all hold;
- full bar: 10 101 tests (1 new guard unit test), clippy/fmt/doc.

## Disposition

LANDED, default-on in code (reachable only where vivify already runs),
`NIXIE_VIVIFY_OTF=0` disables.  The bundle A/B is recorded as
inconclusive-mixed; revisit with a matched null and ≥10 seeds per cell
before making any bundle-default claim.  The self-subsumption guard is
the load-bearing soundness lesson of this slice.


## Seed study (2026-08-21): default-on CONFIRMED — fires rarely, mildly positive where it fires

The owed ≥10-seed follow-up to the inconclusive bundle screen.  Design: 21
satcomp files (1–15 s default), 10 seeds (`SEED=N` — verified to spread
trajectories, 1.5× conflicts on the mrpp sample), arms ON (default) vs OFF
(`NIXIE_VIVIFY_OTF=0`), 40 s cap, ticks-to-verdict primary; 420 runs, 16 min
at 6-way.  No matched null: the only semantic-scrambling null (delete a
*non*-subsuming clause) is unsound and would corrupt the DB — the seed
band is the comparator instead.  Knob reach verified by construction: 4
files' trajectories changed under OFF.

| | |
|---|---|
| files bit-identical ON vs OFF | **16/20** (all seeds) — the check runs but never fires |
| affected files | 3 wins **0.866 / 0.856 / 0.873** (qwh, stable-300, j3037), 1 loss **1.215** (6s268r) |
| overall geomean-of-geomeans | **0.988** |
| aggregate TOs | ON 34 / OFF 33 (wash) |

Conclusions: (1) OTF subsumption is a **rarely-firing, targeted** pass —
16/20 files see zero firings, consistent with its narrow trigger (conflict
or reason clause D with D ⊆ C mod level-0 units during vivify); (2) where
it fires it is mildly positive on balance (3:1 win/loss, ~13 % median
gain vs one 21 % loss); (3) the original screen's "3 TO losses" does not
reproduce across seeds (TOs wash) — seed luck, as suspected.  **Default-on
stands**, now on a seed study rather than an enablement-rule call.  The
knob itself was proven live (unlike `NIXIE_CHRONO_REUSE`, found dead the
same day).
