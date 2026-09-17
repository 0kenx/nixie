# The 36-hour env-probe regression: 3× geomean solving cost from uncached `getenv` in instrumentation gates (2026-09-15)

A routine 36 h A/B (user-requested: current HEAD vs a precompile from ~36 h
ago, release binaries, SATCOMP 2025 30-instance prescreened sample) found a
massive solving-power regression — and its root cause turned out to be
debug instrumentation checking its own env var in the BCP hot loop.

## The measurement (interleaved A/B, pinned P-cores, 60 s cap, perf-stat cycles)

| arm | solved / 30 | cycle geomean vs old | verdict mismatches |
|---|---|---|---|
| `82c3c926` (09-14 09:49, +0.1 h from the 36 h mark) | 24 | 1.0× | — |
| `c81d6d26` (HEAD, 09-15 21:29) | 16–17 | **2.98×** | **0** |
| HEAD + env-probe fix (this landing) | **23** | **1.43×** | **0** |

Seven instances regressed from solved to timeout (`b22`, `frb35`,
`14.normalised`, `oddball`, `WS_500`, `SCPC-500-13`, `b21`); per-instance
cycle ratios on commonly solved instances reached 17× (`x9-07092`),
7.6× (`s38584`), 5.7× (`circuit_48in64`).

## Root cause

`perf record` on HEAD solving `s38584`: **`getenv` 50% + `strncmp` 14% of
all cycles.** An LD_PRELOAD `getenv` counter over one 16 s solve:

| env var | calls |
|---|---|
| `NIXIE_CSR_MUT_TRACE` | 65 932 546 |
| `NIXIE_HEAD_TRACE` | 30 546 847 |
| `NIXIE_PICK_TRACE` | 7 442 790 |
| `NIXIE_AWALK_TRACE` / `NIXIE_ENQ_TRACE` / `NIXIE_BUMP_TRACE` / `NIXIE_CWRITE` | 1.8 M / 1.5 M / 1.0 M / 459 K |
| `NIXIE_CONFLICT_TRACE` | 32 263 (but each walks the full ~36 KB environment) |

≈ **108 M `getenv` calls**. The round-13 instrumentation probes
(`mut_trace!`'s `armed()` "all"-mode fallback, the BCP-kernel conflict
trace, head/enq/pick/bump/awalk traces) each did a raw
`std::env::var(...)` per hot-loop invocation — in the *unarmed* default
case. `mut_trace`'s own doc ("the env is read once into a `OnceLock`")
was betrayed by its `"all"` fallback; `conflict.rs` even carries a comment
about a *previous* uncached-env bug of exactly this shape. On this
machine the environment is large (~36 KB), so each `getenv` walks
hundreds of entries; `NIXIE_CONFLICT_TRACE`'s 32 K calls alone cost ~13 s
on `s38584` (proved by `env -i` collapsing the run from 18.6 s to 4.9 s
before the final fix).

## The fix

New `nixie-sat/src/env_flags.rs`: every hot-path probe flag cached in a
per-name `OnceLock` (`pick/head/enq/bump/bt/awalk/conflict/fixpoint`,
`db_digest_step()`, `cwrite_target()`); `mut_trace::armed()` and its
`code_matches` "all" fallback now read once. No test reads these
variables (verified), so caching changes nothing observable except cost.
After the fix: `s38584` **2.3 s** (HEAD: 17–19 s; 36 h-old baseline:
2.6–4.6 s contemporaneous), env-insensitive (`env -i` identical).

## What is NOT fixed here (ownership)

* **Residual 1.43× cycle geomean vs the 36 h baseline** — content-level,
  and **not uniform**: per-instance fix/old ratios over the 23
  commonly-solved instances run min 0.97× / median 1.23× / max 5.19×
  (sum-of-cycles 1.40×; big-instance geomean 1.53×, tiny 1.33×).  The
  geomean is carried by a fat right tail —
  `SCPC-500-13` **5.19×** (35.8→185.7 G, 7.1→46.7 s), `x9-07092` 3.37×,
  `frb35` 2.96× (59.4→175.8 G), `GP_105` 2.20×, `GP_190` 1.92× — while
  `b22`/`hwmcc`/`oddball`/`b21`/`s38584`/`circuit` sit at 0.97–1.11×.
  That shape (median ~1.2×, tail-heavy, two slight improvements) reads as
  **trajectory divergence on a subset**, not a uniform hot-loop tax — the
  classic CDCL-chaos caveat applies: single-run ratios mix real effect
  with path luck, so the tail instances (SCPC first) deserve seed
  replication before a strictly causal reading; the aggregate 1.40× is
  the safer claim.  Whose cost/benefit it is: the round-13 owner's, now
  visible without the env-noise masking it.
* **The `e987b4b6`→`0aa996f2` false-`sat` window**: cached binaries from
  that era answer `sat` in ~0.1 s on the UNSAT `s38584` (watch-list loss,
  since reverted). Never trust a binary from that window.
* **Stale precompile binaries**: `precompile/d832b82e` and others
  disagreed with their own commits (clean rebuild differed). Any cached
  binary used as evidence in a bisection should be re-verified by rebuild
  at the decisive points (this study's decisive points all were:
  `82c3c926` genuine, `c81d6d26` genuine).
* Pre-existing red on clean `main` at landing time: the `wisas_xs_8_13`
  pair (simplex `24cb0567`, see
  `docs/handovers/2026-09-15-wisas-layer2-simplex-24cb0567.md`) and
  `nixie-tla-check::structs::cardinality_of_a_pinned_set_variable_is_exact`
  (sets arc); plus three known slow tests over the 180 s nextest cap.

## Verification

Build/clippy/fmt/rustdoc clean (my files); workspace nextest 11 803 pass,
all failures pre-existing on clean `main` (verified in a worktree);
Z3 parity 177 run / 0 mismatches (z3 4.16.0), identical to the
pre-change record.

Result store: `precompile/<this-sha>/benchmark/reg36h/` (three-arm
results.tsv, per-run logs, harness, env-shim source, sweep tables).

## Addendum (2026-09-16): the "residual 1.43×" was the CSR mirror, not trajectory divergence — and the seed study that proved it

The seed-replication caveat above is now resolved, and the "trajectory
divergence on a subset" reading was **wrong**.  Paired 10-seed A/B
(`82c3c926`+seed-knob vs `0e6f1afe`, three tail instances,
`precompile/0e6f1afe/benchmark/seedstudy.tsv`):

* **Conflict counts are bit-identical between the two binaries on every
  one of the 30 seed-pairs** (SCPC 185 787 = 185 787, frb35 1 204 664 =
  1 204 664, x9 67 067 = 67 067, …).  The landed content is
  trajectory-inert on these instances.
* **Wall at identical work is 2.5–6× worse** on the new arm (SCPC
  5.2→26.3 s @ 185 787 conflicts; frb35: old finishes 10/10 seeds, new
  times out on 4/10) — a pure per-op cost inflation.

`perf` found it: 65 % of the new arm's runtime sat in
`CsrWatchLists::push_overflow` (33.5 %, a `positions` HashMap write per
watcher-add) + `CsrWatchLists::scan_remove` (31.8 %, in-scan mirroring),
while the real BCP scan fell from 65 % to 17 %.  **`WatchLists::new`
attached the CSR mirror unconditionally** (`csr: Some(…)`), contradicting
the documented "Default off; the flag-off path is byte-identical" — the
same defect the wisas-era canary hinted at ("mirror maintenance runs
unconditionally in this build").  This also finally explains the
`add`-loses-its-Vec-write accident's environment: everything about that
window ran with the mirror live.

**The fix** (`<this commit>`): attach the mirror only when one of the CSR
knobs (`NIXIE_CSR_SHADOW` / `NIXIE_CSR_SCAN` / `NIXIE_CSR_READ`) asks for
it.  After: SCPC 5.28 s @ **exactly** 185 787 conflicts (old-arm parity),
x9 2.17 s @ 67 067 (faster than the 36 h-old arm), frb35 21.6 s @
1 204 664 — and, unexpectedly, **the `wisas_xs_8_13` guards pass again**
(the mirror was entangled in that regression's layer 2 as well).

**Gate lesson**: both 36 h regressions (env probes, CSR mirror) were
*semantics-inert constant-factor costs* — a counters-only gate is blind to
that class.  `run_gate.sh` now also gates on interleaved-paired wall
geomean (one-sided: improvements never fail; >1.5× at identical counters
= FAIL, 1.25–1.5× = WARN).  This fix calibrates it: conflicts 1.000,
wall geomean **0.58×**.

## Addendum (2026-09-16, closing the perf campaign): where the remaining gap lives

Post-fix state, measured on the perf-gate corpus (release/perf builds,
pinned, quiet-ish machine):

* **Constant-factor work is done.**  vs 36 h ago: conflicts bit-identical,
  wall geomean ~1.0 (some instances faster — x9 2.17 s vs old-arm 5.3 s).
  vs **kissat 4.0.4** head-to-head: nixie wins 3/9 outright (Carry_Bits
  0.04 s vs 1.15, frb35 13.4 vs 14.8, WS_500 21.3 vs 22.2), close on 3
  (SCPC 8.0 vs 5.2, circuit 8.1 vs 6.2, s38584 2.2 vs 1.3), behind on 3
  (b21 25.2 vs 4.8, 6s299 0.92 vs 0.07, Iter22 3.2 vs 1.2).
* **Machine-level health**: IPC 2.27, branch-miss 3.3 %, cache-miss
  0.3 % — compute-bound, no structural pathology; hot paths are mature
  (cadical-parity subsumption with amortized scratch, tuned BCP driver).
* **The remaining gap is search quality, not cost.**  On the three laggards
  (kissat vs nixie): x9-07092 **13× fewer conflicts** (3 093 vs 40 822 —
  kissat's preprocessing cracks it), 6s299 2.3× (1 801 vs 4 169), b21
  1.7× conflicts (194 567 vs 330 571) **and 3.2× propagations per
  conflict (300 vs 971)** — weaker learned clauses driving far more
  search per conflict.  b21's 5.2× wall is fully accounted for by work
  volume (1.7 × 3.2 ≈ 5.5×); its profile shows no hotspot.
* **Handoff**: improving that is heuristic territory (lemma quality,
  preprocessing strength — the standing-gap study's named families) and
  requires the full docs/BENCHMARKING.md discipline: matched nulls,
  `NIXIE_SAT_SEED` replication (≥10 seeds), the perf gate, and parity.
  No casual knob-twiddling.

## Addendum (2026-09-16): `restart_strategy` was inert config — now wired; the cadical-fold question answered by decomposition

**Discovery** (via the new `NIXIE_SAT_*` decomposition knobs): under
`enable_stabilize: true` — which **every** preset and the default sets —
the restart firing predicate never consulted `config.restart_strategy`;
the whole knob (Luby/Geometric/Glucose/LocalLbd, set differently by five
presets) was facade.  The glucose/minisat/cadical presets' restart
identities were no-ops.

**The wiring**: focused-mode rule is now selected by the strategy —
Glucose/LocalLbd keep the EMA rule bit-for-bit, Luby/Geometric fall back
to the legacy conflict-threshold cadence (whose per-strategy bookkeeping
in `decide.rs` was already maintained).  `SolverConfig::default()` flips
Luby→Glucose so **every existing default/preset trajectory is preserved
bit-identically** (verified: s38584 default 31 515 = 31 515, cadical
preset 16 138 = 16 138; gate conflicts 1.000) while the knob becomes
real (Luby: 35 251 ≠ 31 515).  Regression test pins the liveness.

**The fold question** ("fold cadical preset as default"): decomposition
over 9 instances × 3 seeds says **not justified** —

| arm | conflict geomean vs default | solved |
|---|---|---|
| BVE alone | **1.335× worse** (x9 3.6×, frb35 3.1× worse) | 26/27 |
| glucose restarts | (was inert — n/a) | — |
| full cadical preset | 0.947× (n=5 seeds) vs 1.135× (n=3 seeds) — sign flips with the seed set | 26/27 |

No single component carries the preset's modest aggregate; per-seed
spread on the tail instances (x9: 6.5 k–41 k conflicts) is 5–10×, so
n=3–5 geomeans are noise-dominated (the power table's warning).  A real
fold decision needs the powered experiment: ≥20 seeds × the full
30-instance corpus × both arms (~4–6 h machine time), scored on BOTH
geomean conflicts and solved-at-cap.  Data:
`precompile/f21d0def/benchmark/config-ab/` (cfg_ab.tsv, decomp.tsv,
decomp.py).

## Addendum (2026-09-16, final): the powered experiment settles the fold — cadical preset is now the CLI default

15 seeds × 12 instances × 2 arms (384 runs,
`precompile/c868c54e/benchmark/fold-power/power.tsv`):

* **conflicts geomean 0.842×** (cadical preset 16 % cheaper),
* solved **190/192 vs 189/192** (the n=5 WS_500 timeouts did not
  reproduce at power),
* **bootstrap sign stability**: geomean < 1.0 in 183/200 (k=3), 194/200
  (k=5), **200/200 (k≥10)** — the earlier sign flip was small-sample
  noise, exactly the failure mode the power table predicts.

Per-instance: s38584 0.51, b21 0.64, x9 0.75, 6s299 0.91, Carry 0.95,
circuit 0.87, WS_500 0.68 — vs frb35 **1.71** (the BVE-averse family;
BVE-alone measured 3.1× worse there) and SCPC 1.03.  Net strongly
positive; the losing family is named for the next component-tuning
round.

**Landed**: the CLI fast-path default is now
`ConfigPreset::CaDiCaL.config()` (the standing-table reference
configuration, finally reachable as the default it always should have
been).  `--preset` still overrides; `NIXIE_SAT_BVE/_RESTART/
_STABLE_POLARITY/_DELETION` decompose on top.

**Gate hardening in the same landing**: `GATE_SEEDS=k` — single-seed
conflicts (the old mode, still default) detects semantics-inert
regressions where counters must be bit-identical, but is trajectory
noise for deliberate heuristic landings (measured spreads to 13× per
instance; this fold measured 1.296× at seed 1 and **0.854×** over 10
seeds on the same corpus).  Heuristic landings gate at `GATE_SEEDS>=10`
and cite their powered experiment.

## Addendum (2026-09-17): the props/conflict gap, measured honestly — mostly config, residue 1.37×

Audit of the "971 vs 300 props/conflict" claim on b21 (the generic
clause-quality question):

1. **Metric contamination: ruled out.**  Vivify's internal propagation
   uses its own mini-propagator and never touches `stats.propagations`
   (verified by the new split counter reading 0; the 4.2 M delta under
   `NIXIE_INPROC_VIVSKIP=1` was second-order search change, not
   vivify's own work).  XOR propagation is default-off.  Kissat's
   counter has the same assigned-literal semantics.  To keep it that
   way, `propagations_inprocessing` now exists as a separate stat
   (printed by `--stats` when non-zero) with the vivify round charged
   to it — future contamination becomes visible instead of silent.
2. **The fold closed most of it**: 971 → 410 props/conflict
   (old default → cadical preset).  The "3.2× quality gap" was mostly
   the old configuration.
3. **Not decisions/conflict**: 9.22 (nixie) vs **9.95 (kissat)** on
   b21 — both dive equally deep.
4. **Residue: 410 vs 300 = 1.37× genuine search-props/conflict**,
   which at equal decisions/conflict and equal restart density is
   **1.40× propagation volume per decision** — a search-shape property
   (how many literals each decision drags in before the conflict), i.e.
   branching-order quality: kissat's decisions contradict sooner.
   Heuristic-domain; the honest counter + seed knob now support
   measuring any candidate fix on this exact axis.
5. b21's remaining wall gap (10.8 s vs 4.8 s ≈ 2.25×) decomposes as
   1.11× conflicts × 1.40× props/decision × ~1.45× mixed per-work cost
   — the latter folding in the preset's inprocessing share
   (subsume+probe+kitten ≈ 15-20 % of runtime by profile), which no
   outside counter splits; separating search wall from inprocessing
   wall is a named follow-up if cross-solver cost comparison ever
   needs it.

## Session closure (2026-09-17): final standing vs kissat on the 30-instance corpus

The full arc measured end-to-end (`precompile/098720f6/benchmark/final-standing.tsv`,
60 s cap, pinned, interleaved, kissat 4.0.4 vs nixie `098720f6`):

| | session start¹ | session end |
|---|---|---|
| solved / 30 | 16 | **26** |
| verdict mismatches | 0 | **0** |
| nixie/kissat wall geomean (both-solved) | ~3.1× | **1.93×** |
| nixie faster than kissat | — | 8/26 |

¹ 3-way benchmark (2026-09-15) under the old default with the env-probe
and CSR-mirror taxes and the pre-fold configuration.

Remaining gap anatomy (the honest map): the 1.93× geomean is carried by
search quality on specific families — `bv_ILA` 41.7×, `oddball` 25.1×,
`hwmcc-6s299` 12.1×, `x9` 8.8×, `GP_190` 8.4×, the `normalised` pair
~7×, `5447072093nw` 7.0× — while the trivial-`arles` family and
`Carry_Bits` are 2–5× *faster* than kissat, and `s38584`/`SCPC`/`circuit`
are at 1.2–1.3×.  Four instances still time out (`WS_500`, `1.normalised`,
`Break_12_30`, `nla-digbench`).

Constant-factor work is exhausted (IPC 2.27, healthy profile, every
mechanical regression fixed, both counter splits landed); everything
above 1.5× is search quality — the props-per-decision volume and the
specific families named in the standing-gap study — now measurable with
`NIXIE_SAT_SEED` replication, the `NIXIE_SAT_*` decomposition knobs, and
the inprocessing wall counter built this session.

## Addendum (2026-09-17): the `hwmcc-6s299` 12× is pure parse/setup — anatomy measured, fix named, swap reverted

The final standing's third-worst gap is not search at all: the instance is
decided with **zero conflicts on both sides** (kissat 1.0 s vs nixie 12.2 s
under the same load; 544 MB, 78 % binary clauses).  Profile of the old
(CLI line-parser) path: line-based UTF-8 parsing ≈ 47 % (`Lines::next` +
`from_utf8` + `trim` inline in `process_single_file`), the `Vec<Vec<i32>>`
intermediate's growth+drop ≈ 25 %, shared `add_clause`/attach the rest.

**A direct swap to the byte-level `nixie_sat::DimacsParser` was built and
measured — and reverted**: trajectories bit-identical (conflicts equal on
every gate instance), but wall 1.5× *worse* (24–34 s vs 16–18 s,
interleaved, same conditions).  Its deferred-BIG design trades per-add
edge churn for a full `rebuild_watches_and_binary_graph` +
re-attach pass over all 400 K clauses — an extra whole-database walk that
outweighs the 35 % the byte parser saves on this binary-heavy file.

**The named fix** (SAT-core arc, nixie-sat): a *non-deferred* byte-level
parse mode — `parse_reader_impl` with incremental attach (byte scanning +
`add_clause` per clause, no BIG deferral, no rebuild pass).  Projected
~3–4× on parse-dominated instances from the 47 %→12 % parse saving alone.
Not landed here: it lives in `nixie-sat::dimacs`, is interface-visible to
`cnf_bench`, and deserves its own trajectory-identity verification sweep.
