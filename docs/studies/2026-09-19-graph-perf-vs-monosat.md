# Study: graph-constraint throughput vs MonoSAT — profiling, inert optimizations, and the honest remaining gap

**Date:** 2026-09-19/20
**Base:** `1b974b80` (graph module + differential campaign)
**Verdict:** **LANDED** — 1.94× geomean on the graph corpus (2.65× vs MonoSAT,
down from 5.1×; worst instance 8.45 s → 2.76 s), with **bit-identical
conflicts/decisions/propagations counters** on the whole corpus, 1 600/1 600
MonoSAT differential agreement, full workspace suite green, Z3 4.16.0 parity
176/176 decisive, perf gate PASS (neutral; see attribution note).

## Corpus and harness

40 seeded GNF instances (`bench/graph_differential/gen_instance.py`): one
digraph, n ∈ {25, 50, 100, 150}, reach atoms ∈ {4, 8, 16, 32}, 5 seeds per
cell, unit + two-literal constraint mix (sat/unsat split ≈ 40/60). Both
solvers as release builds (`--release`; MonoSAT rebuilt out-of-tree per the
recipe in the differential study). Wall times are medians of 3 on a
load-sharing machine — recorded as throughput evidence for a
**semantics-inert** change (counters bit-identical), which is the one
setting where wall time is the thing that changed; per `docs/BENCHMARKING.md`
it is never a policy metric.

## Baseline (code at `1b974b80`)

| | MonoSAT | Nixie | ratio |
|---|---|---|---|
| geomean | 0.0153 s | 0.0786 s | 5.1× |
| total | 1.35 s | 30.5 s | 22.6× |
| worst (`v150_r16_s1`, n=150, 16 atoms, ~7.5 k edges) | 0.22 s | 8.45 s | 39× |

## Where the time actually went (perf, release, symbols via `strip=none -g`)

Profiling repeatedly overturned the obvious hypothesis. The graph
propagator's own BFS work was *not* the wall-time bottleneck; five separate
hotspots were, four of them shared solver machinery:

1. **~50 % of samples in `HashMap<TermId, ()>` insert/rehash.**
   `UserPropagatorManager::push` deep-cloned `watched_terms`/`fixed_terms`
   (7.5 k entries) on **every SAT decision level**, and `pop` restored the
   clone — thousands of levels ⇒ millions of hash inserts. Graph models
   were simply the first to register thousands of watches; CP models never
   exposed it.
2. **`UserCallback::truth` scanned the whole watch list** per justification
   literal of every consequence (O(watches) per lookup).
3. **`register_user_propagator` deduplicated watches with a linear scan** —
   O(watches²), ≈28 M comparisons at 7.5 k watches.
4. **`Solver::assert` re-surveyed the entire assertion stack per assertion**
   for the set/bag eager reductions (`set_theory::reduce`,
   `bag_theory::reduce`, `bag_user_eq_atoms` walking
   `self.assertions.clone()` + `certificate_assertions.clone()`) — quadratic
   in assertions, and provably a no-op for goals with no set/bag-sorted
   term. This affects **every** theory mix with many assertions, not just
   graphs. The BV unified constraint sweep had the same shape
   (`collect_unified_constraint_atoms` over all constraints per assert).
5. Only then the propagator: 130 k forced BFS for 7.5 k events (≈17 per
   event — one per reach atom per event, each O(V+E)), `Vec<Vec<…>>`
   adjacency reallocation per event, and full re-reads of all edge values.

## Changes (each semantics-inert by construction)

| # | Change | Inertness argument |
|---|---|---|
| 1 | Manager scopes: snapshot clones → **exact undo journals** (fixed values with their previous value, equality/watch insertions, consequence-queue push/drain replay) | Restores precisely the state a snapshot would — including overwritten fixations; the dedicated manager regression and the CP rollback suites cover the semantics |
| 2 | `truth` via a `Var → (term, lit)` index | One entry per SAT variable decodes both polarities; identical answers to the scan |
| 3 | Watch dedup through a hash set | Produces the identical watch list |
| 4 | Set/bag survey gated on a monotonic `has_set_or_bag_terms` flag (set by the encoder's sort dispatch and by scanning the current assertion) | With no set/bag-sorted subterm in any root, both reductions early-return empty (no axioms, no honesty gates, no minted atoms, `term` unchanged) — the block is a provable no-op; the flag is monotone so a `pop` can only keep the slow exact path |
| 5 | BV unified sweep skipped when `bv_terms.is_empty()` | The sweep matches only BV-operand atoms; no BV-sorted term exists ⇒ provably empty |
| 6 | Graph propagator: **content-addressed `ViewCache`** — packed true-edge / non-false-edge bits per graph; per-source forced BFS, per-target backward BFS and cycle checks memoized under a bit-exact key; flat CSR adjacency rebuilt into reused buffers | Memoization, not incremental state: the key is re-compared against the *full* current assignment every run, so a key hit means "same function, same inputs"; rows preserve declaration order so paths/cuts/reasons are byte-identical |

## Verification

- **Bit-identity:** old vs new binaries, 40/40 corpus instances identical
  `conflicts/decisions/propagations` (via the example's `STATS=1` output) and
  identical verdicts.
- **Differential:** the 1 600-instance MonoSAT campaign re-run — 1 600/1 600
  agree, 0 skips.
- **Suites:** full workspace 12 053/12 053 (the manager and encode changes
  are exercised by the CP rollback, set/bag, and graph suites).
- **Z3 parity (4.16.0):** 176/176 decisive, 0 disagreements, 1 inconclusive
  (Z3 `Unknown`).
- **Perf gate:** PASS. The gate shows 1.013/1.010 vs the pinned `1710e125`
  baseline — **attributed to intermediate main commits, not this diff**:
  building HEAD *without* this diff reproduces the identical 1.013 geomean
  and the identical 2.23× worst instance. This diff is exactly neutral on
  the gate corpus (as expected: no set/bag terms, no user propagators there).
- clippy `-D warnings`, fmt, rustdoc clean.

## Results

| | MonoSAT | Nixie before | Nixie after | before → after |
|---|---|---|---|---|
| geomean | 0.0153 s | 0.0786 s | **0.0406 s** | 1.94× |
| total (40 inst.) | 1.35 s | 30.5 s | **12.5 s** | 2.4× |
| worst instance | 0.22 s | 8.45 s | **2.76 s** | 3.1× |
| gap vs MonoSAT (geomean) | — | 5.1× | **2.65×** | |

Propagator-internal: forced BFS on the worst instance 130 467 → 57 766
(content-addressed memo survives the ~half of events that do not change the
relevant view's bits — false assignments keep the forced view, true
assignments keep the possible view, backjumps often return to a seen key).

## The honest remaining gap and where it lives

At 2.65× geomean (9.3× total, 12.7× on the worst instance) the remaining
difference is structural, in decreasing order:

1. **Incremental graph algorithms.** MonoSAT's per-edge-enable cost is
   amortized over Ramalingam–Reps dynamic reachability, dynamic max-flow
   min-cuts, and PK topological order; our propagator recomputes
   reachability per (event × source) with a memo that only survives
   unchanged views. Closing this means real incremental state with trails —
   the documented upgrade path in `docs/GRAPH.md`, deliberately not taken
   here: it would trade the stateless design's obvious correctness for
   speed, and the current gap is already dominated by (2).
2. **The general SMT per-assertion pipeline.** Even after the gates, each
   `assert` pays interning, preprocessing dispatch and encoding through the
   full CDCL(T) stack; MonoSAT's GNF loader is a lean DIMACS parser. This is
   the cost of being an SMT solver, borne by every theory.
3. **Theory-directed decisions** (MonoSAT's `-decide-theories`) — a search
   heuristic; changing it here would alter trajectories and would need the
   full matched-null machinery of `docs/BENCHMARKING.md`, which is out of
   scope for an inert-optimization landing.

## Follow-ups recorded for the next agent

- The set/bag survey gate (change 4) removes a **quadratic in assertions**
  for every non-set/bag SMT workload with many assertions; the equivalent
  guard may exist elsewhere in the per-assert pipeline (worth an audit with
  a many-assertion microbenchmark).
- The manager journals (change 1) make per-level push/pop O(changes); CP
  models with many domain indicators benefit silently.
- The stale `bench/perf_gate/BASELINE` pin (several SAT-core landings old)
  shows 1.013 drift attributable to intermediate commits — re-pinning is a
  deliberate act for whoever lands the next SAT-core change.

## Addendum (2026-09-20): the per-assertion audit continued — one more shared quadratic

Following this study's own follow-up note, a scaling probe through the real
SMT-LIB path (N declarations + N assertions, `set-logic QF_LIA`) found the
next superlinearity — not in the assertion pipeline but in the theory check:

`TheoryManager::propagate_euf_equalities_to_arith` built its arith-term list
with a `Vec::contains` membership scan — **O(terms²) per call, once per
theory check** — which profiled at 16 % of a 4 000-term run (the rest of
that run is genuine simplex work on the disequalities). Replaced with an
order-preserving `FxHashSet` membership (identical insertion order ⇒
identical class representatives ⇒ bit-identical behavior by construction).
Measured on the `distinct`-heavy probe under a loaded machine: 111 s →
57–77 s for 4 000 terms; the *residual* superlinear cost is the simplex
disequality case-split procedure itself (z3: 0.19 s) — a theory-solver
algorithm change, explicitly out of scope for inert landings.

Verification: verdicts match z3 on the probes (sat/unsat); full workspace
suite green (timeouts re-verified in isolation — load artifacts); Z3 4.16.0
parity 176/176 decisive, 0 disagreements; perf gate **1.000** against the
freshly re-pinned baseline (`a48d8464` re-pinned to `6853ba29`); graph
differential spot-check 300/300 agree.

## Closing attribution (2026-09-20, final build): where the residual 2.67x actually lives

Re-profiled the worst corpus instance (`v150_r16_s1`) on the fully-optimized
build to decide whether the recorded "incremental dynamic-graph algorithms"
upgrade path would pay:

- **The graph propagator no longer registers as a self-time hotspot** (<2 %;
  its only profile presence is ~1.5 % of caller fragments under HashMap
  lookups). The content-addressed memo plus CSR reduced it below measurement
  noise at these scales.
- The residual profile is **term-management infrastructure**: ~40 %
  allocator/libc (`memmove` 14 %, `realloc` 12 %, `malloc`/`reserve_rehash`
  ~12 %) driven by hash-consing ~22 k minted terms
  (`encode_depth_memoized` 7.7 %, `TermManager::intern` 5.4 %) and the
  Tseitin/var maps — the cost of the general SMT API and CDCL(T) stack that
  every theory pays, versus MonoSAT's integer-only GNF loader that parses
  variables straight into solver slots.

**Re-scope of the upgrade path:** incremental reachability
(Ramalingam–Reps et al.) would buy ≈nothing on this corpus — the recomputed
BFS it would amortize is already <2 % of runtime. It becomes the right tool
only for much larger graphs (hundreds of vertices and beyond), where
per-event O(V·E) recompute dominates again; at today's scales the honest
remaining gap is the SMT assertion pipeline itself, shared by all theories.

Fresh corpus re-run on the final build: geomean ratio **2.67×**
(monosat 0.0150 s vs nixie 0.0400 s), matching the recorded result —
measurement reproducible end-to-end after the MonoSAT rebuild.

## Addendum (2026-09-20, evening): the "term-management" gap decomposed — two shared-path fixes, gap 2.67× → 2.33×

Challenged the closing attribution above with allocation-level measurement
(an `LD_PRELOAD` counter plus a phase-sentinel, ~zero overhead) instead of
perf alone. The "~40 % allocator/libc" blob decomposed into two *specific*
shared-path defects — neither of them term management:

1. **SipHash in the propagator-manager maps** (~12 % of a corpus solve).
   `UserPropagatorManager`'s `fixed_terms`/`equalities`/`watched_terms` were
   plain `std::collections` maps — SipHash with a random seed — while every
   other hot map in the codebase is Fx. Every watched atom of every event is
   looked up there (`run_graph` reads all edge values per event: 6 k edges ×
   3.3 k events ≈ 20 M SipHashed lookups on one corpus instance). Switched
   to `FxHashMap`/`FxHashSet`. Nothing iterates these maps for output, so
   results are unchanged.
2. **`std::env::var` per assertion** (~11 %). The BV routing gates
   (`bv_unify_enabled`, `bv_dispatch_unified`, `bv_defer_blast_enabled`,
   `freeze_collapse_enabled`) re-read the environment on every call — and
   `getenv` is a linear scan over `environ` (visible as `__strncmp_avx2`).
   Consulted per assertion/registration/check. Memoized in `OnceLock`s;
   environment variables cannot meaningfully change mid-process.

Also fixed benchmarking parity: the `graph_gnf` example now installs
**mimalloc** exactly like the production CLI (before, it benchmarked glibc
malloc; measured here as ≈neutral on this workload, but parity is owed).

Measured (glibc→glibc, identical binaries otherwise): worst instance
2.66 s → 1.88 s; `v100_r32_s3` 0.94 s → 0.42 s. Corpus: geomean ratio
**2.67× → 2.33×**, totals 10.99 s → 8.05 s, worst per-instance 39× → 18×.
The allocation storm itself (696 k mallocs / 212 MB realloc traffic on one
instance) dropped accordingly; the remainder is genuine interning + Tseitin
work.

Verification: conflicts/decisions/propagations **bit-identical on 40/40
corpus instances** (old vs new binaries); full workspace suite 12 070/12 070;
Z3 4.16.0 parity 176/176 decisive, 0 disagreements; perf gate **1.000**
against the current pin; graph differential 500/500; clippy/fmt clean.
