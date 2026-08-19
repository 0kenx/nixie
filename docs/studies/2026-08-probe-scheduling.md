# Probe scheduling (cadical root/rank selection): infrastructure landed, ranking signal rejected (2026-08-18)

## Question

Our pre-search failed-literal probing (behind `INPROCESS`) walked every
variable by index and probed both polarities. CaDiCaL probes binary-
implication-graph **roots**, ranked by negated-occurrence count, with
`propfixed` memoization and mid-search interleaving on a conflict budget
(`probe.cpp`). Does adopting the cadical selection discipline improve
instructions-to-verdict?

## What was implemented (kept, off by default — sound infrastructure)

`solver/probe.rs`: `probe_round` schedules roots exactly as cadical's
`generate_probes` (one-polarity-only binary occurrences; probe the
polarity occurring negatively; rank by `noccs(¬probe)` descending), with
`propfixed` memoization (skip re-probing until new level-0 facts), failed
literals forced to units, and hyper-binary derivation on success. Wired as
`inprobing()` into the conflict handler before elimination (cadical loop
order), re-arming on the `25·interval·log10(rounds+9)` schedule. The old
brute-force `failed_literal_probing`/`probe_hyper_binary` remain (pre-search
path, flag-gated as before).

A matched-null switch ships with it: `OXIZ_PROBE_NULL=1` reverses the rank
order (same roots, same schedule, same budgets — only the semantic content
under test, best-first ordering, is destroyed).

## Experiment

54 files (cadical<5s corpus minus Simon-family instant solves) × 8 seeds ×
2 arms, CRN-paired, metric instructions-to-verdict (wall-clock invalid:
foreign load 5-18 during the window). 429 valid cells.

**Result: geomean(treatment/null) = 1.0091** — the treatment *loses* to its
own null by 0.9%, despite winning 325/429 cells (wins small, losses large —
the noise signature). Per-file: one real win (ak128booth 0.767), one real
loss (ITC2021_Early_3 1.529), everything else within ±7%.

Verdict per docs/BENCHMARKING.md §2: **ratio > 1 ⇒ nothing**. The
best-first root ranking carries no detectable signal on this corpus at this
power. Do not tune parameters against this measurement.

## What the controls caught along the way (recorded so they are not repeated)

1. **Phantom false-UNSAT from a stale binary**: an early single-file sweep
   reported `noL-11-14` UNSAT under the treatment (SAT per CaDiCaL). It did
   not reproduce on the freshly-built binary (5× timeout, no verdict) and
   6k differential-fuzz iterations across the probing variants were clean.
   Root cause: a `grep -cE "^error"` whose zero-match exit code short-
   circuited `&&` and masked a failed rebuild — the same trap noted twice
   before in this repo's history. `touch src/main.rs && cargo build 2>&1 |
   tail -1` before any verdict-bearing run.
2. **`env` cannot appear as an argv element under `perf stat`** (perf execs
   it as a path): the paired-harness reported `rc1/<not counted>` until env
   was threaded via `subprocess(env=...)`.
3. Fixed-conflict and wall metrics remain invalid for trajectory-diverging
   changes (re-confirmed: +53% phantom at 100k fixed conflicts).

## What is still open (the actual decisions/conflict term)

The 4.5× decisions-per-conflict gap vs cadical is *not* closed by probe
selection. Remaining hypotheses, in order of expected leverage:

1. **Elimination-as-default re-measure**: the treatment's per-file wins
   concentrate exactly where elimination pays (6s167-family). With probing
   infrastructure in place, re-run the elimination-as-default suite
   experiment (was net-negative pre-probing: 53/94 above 1.5×).
2. **Hyper-binary quality**: our HBR derives ≤64 binaries/probe with a
   fresh-clause cap; cadical's dominator/LCA analysis derives the *backbone*
   implications. This is a different lever than ranking.
3. **Equivalent-literal interleaving** (`decompose`/`sweep`-class passes):
   cadical's ELS runs inside `inprobe`; ours is pre-search-only.

## Follow-up (same day): dominator HBR, ELS interleaving, and the full-stack verdict

### Implemented (kept, off by default; three soundness fixes found on the way)

1. **Dominator hyper-binary resolution** (`derive_hyper_binaries_dominator`):
   the port of cadical's `hyper_binary_resolve` + `probe_dominator`, applied
   post-hoc in trail order — parents reconstructed from reasons (binary
   reasons give the implier directly; long reasons get the dominator of
   their level-1 false literals), the binary derived is `(¬dom ∨ q)` (the
   backbone) instead of `(¬probe ∨ q)`, and the subsumption case retires the
   reason.
2. **ELS interleaving**: `substitute_equivalent_literals_round` (the
   one-shot latch lifted; the substitution map composes) wired into
   `inprocess()` ahead of pure-literal/subsumption, gated on
   `enable_equiv_substitution && !real_theory_attached`.
3. **Deleted-reason hygiene, made structural**: `Solver::retire_clause` /
   `remove_clause` purge binary-graph edges, re-point live trail reasons to
   `Decision`, then retire — routed through every in-solver deletion site
   (subsume, BVE, ELS, eliminator, probe case-(B), learned-subsumption), and
   the pure-literal pass's post-hoc bookkeeping (whose hygiene loop had been
   dead code: the DRAT-gated literal snapshot is empty without proofs — now
   an always-on id-only snapshot).

The soundness fixes, each caught by a real reproducer (`Break_unsat_06_07`,
165 ms, `INPROCESS+PROBE+HBP+BVE`; every proper flag subset clean):

- **HBR promotion hole (the false SAT)**: subsuming an *original* reason
  obliges the resolvent to carry it permanently (cadical `red = !contained
  || reason->redundant`); the first port left the binary learned, a later
  reduction deleted the only remaining (weaker) constraint, and UNSAT
  flipped to SAT. Fix: `clear_learned` promotion.
- **Live-reason deletion (debug invariant)**: retired clauses were still
  recorded reasons — binary reasons escape the `lits[0]` invariant (the
  binary-graph path records either position), so the reduce-style O(1)
  guard misses them. Fix: re-point to `Decision` (exact for level-0 facts;
  cadical `v.reason = level ? … : 0`).
- **Stale binary edges (the re-establishment)**: deleting a binary leaves
  its implication-graph edges propagating (the binary loop never consults
  the deleted flag), re-recording reasons for deleted clauses after any
  clearing. Fix: purge edges before setting the flag.

### The full-stack experiment (hypothesis 1: elimination-as-default re-measure)

Default vs `INPROCESS+PROBE+HBP+EQUIV+BVE`, 67 files, paired
instructions-to-verdict, verdicts cross-checked:

- **0 verdict mismatches** (soundness clean after the fixes)
- **geomean(full/def) = 1.74**, full better on 18/61 paired cells
- solved: default 64/67, full stack 62/67

**Verdict: decisively net-negative as a default, again.** With probing and
ELS in place the elimination-friendly files still improve (6s167 −57.5%),
but the aggregate is far worse than the earlier no-probing measurement
(53/94 → 1.74× geomean). Whatever amortizes this stack in CaDiCaL — the
decompose/transred interplay, the schedule constants, or search quality we
have not ported — is still missing. Per the methodology: recorded, not
tuned against.

### qwh.50.1250 regression (user-reported: sat 2.19s → timeout)

Bisected by instructions-to-verdict across b6398d0 → cc72823 → 5e61d37 →
3ef9086 → HEAD: the flip is **cc72823 (the reuse_trail fix)** — 126.5G →
non-terminating; f32+blocker later restored solving at 263G (2.1× baseline
work; HEAD 269G). No bug: the faithful-but-diverging reuse fix (measured
aggregate-neutral, 11/10 wins/losses over 31 files × 8 seeds) landed on qwh
as a chaotic casualty, and the subsequent diverging changes re-rolled it
partially back. Recorded as a tracked casualty of the accepted trade-off.
