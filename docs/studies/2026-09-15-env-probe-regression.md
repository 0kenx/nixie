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
