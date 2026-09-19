# Standing SMT-side performance table — nixie vs z3

The standing perf reference for the SMT side (QF_LIA / QF_BV slices),
complementing `bench/perf_gate` (nixie-vs-nixie landing gate) and
`bench/z3_parity` (verdict parity): the parity suite's wall columns are
harness-contaminated and mean nothing, and before this table the SMT
side had no standing perf reference at all.

## Protocol

- **Corpus**: deterministic stride samples (60 per family, `LC_ALL=C
  sort` order) of the in-repo `smt-lib/non-incremental` extracts — the
  same files every run; the slices are recorded in the snapshot.
- **Budget**: a per-instance wall *cap* (10 s default, bounding only —
  wall is never a metric).  (nixie's `--conflict-limit` is now enforced
  end to end — it used to bind only theory conflicts, a facade on
  bit-blasted goals — but the harness keeps wall caps so both solvers
  run under an identical, comparable budget shape.)
- **Metric**: each solver's own deterministic conflict counters
  (`--stats` / `-st`).  Counter *levels* are not comparable across
  solvers; **solved-within-cap counts** are the cross-solver datum, and
  the per-solver counters are the nixie-vs-nixie datum (re-run at a new
  sha and compare the `conflicts` columns).
- **Soundness cross-check**: verdict disagreements vs z3 are counted and
  must be zero; any disagreement is a soundness signal, not a perf
  datum.

## Running

```bash
bench/smt_perf/run_perf.sh [nixie-binary]     # default: workspace release build
SMT_PERF_CAP=20 SMT_PERF_SLICE=100 ...        # knobs for wider runs
```

The scratch `results.json` is gitignored; commit the per-environment
`results.<os>-<arch>.json` (the parity suite's convention).

## First snapshot (2026-09-19, z3 4.16.0, nixie `7e5075db`)

| family | nixie | z3 | disagreements |
|---|---|---|---|
| QF_LIA | 32/60 | 54/60 | 0 |
| QF_BV | 50/60 | 53/60 | 0 |

The QF_LIA gap (−22) is simplex-side capacity — the arithmetic arc's
active territory; QF_BV is within 3.  Re-run at landing-relevant shas
and compare against this table.

**Every loss is now mechanism-attributed** with repros and fix routes —
see `docs/studies/2026-09-19-smt-perf-gap-attribution.md`: the LIA gap
splits into the deep-encoding class (9 instant `unknown`s at paren
depth 2537 vs `ENCODE_DEPTH_LIMIT` 512 — the iterative-encoder project)
and the integer-reasoning/simplex-blowup class (z3 decides via its
Diophantine solver, `arith-dio-calls 1`, while nixie's branch-and-bound
grinds BigInt-GCD blowup); the BV gap is the algebraic-identity
(multiplier/wienand) preprocessing class, z3-at-0-conflicts.  On the
both-solved set the conflict-ratio median is 1.0 — the gap is
concentrated, not general slowness.
