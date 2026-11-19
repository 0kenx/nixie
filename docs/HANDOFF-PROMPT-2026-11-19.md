# Handoff prompt — nixie performance campaign (2026-11-19)

You are continuing a long-running performance campaign on **nixie**, a
pure-Rust SMT solver (~440 kloc, 17 crates, repo root
`/media/data/proj/nixie`).  The mission: close the remaining
benchmark gaps vs **z3** on SMT-LIB QF_BV families, landing measured
wins and recording measured negatives.  **`AGENTS.md` is canonical** —
read it first (soundness rules, verification bar, git discipline,
benchmarking protocol).  This prompt is the campaign-specific state;
the running log with every addendum is
`docs/studies/2026-11-15-bv-andfold-soundness-and-termrules.md`
(27 addenda) and `docs/HANDOFF-2026-11-15.md`.

## Where things stand (HEAD `caf25750`, tree clean)

Scoreboard, all matched-interleaved, zero wrong verdicts at every step:

- **Stratified 170-sample** (seed 20261115, 17/family × 10): nixie at
  or ahead of z3 (matched pairs read 148–150 vs z3's 146).
- **Sydr family census** (535 cells): nixie 388 vs z3 419 under
  load-14 (our arm load-depressed; quiet-machine count higher —
  410 measured at load 7 pre-interval-landing).  **Gap 49, ahead 18**
  (we win pk2bm ×10, faad ×5 that z3 fails).  0 disagreements.
- **asp family: closed** (4 = z3's 4).

Campaign arc (all landed, full bar green at each):
blast strength-reductions → GATE_SH default-on → lean-BV v3 (asp
74→94) → epoch-stamped visited marks → dense-slab `term_to_bv` memo →
per-assert feature-walk gates/memos → solver-owned blastable memo
(soundness: thread-local TermId collision) → sweep-cursor →
on_backtrack watermark + levels array → BIG overflow bitset →
mid-search BIG CSR fold → model-eval pass memo → SCC single-borrow →
**SMT-path inprocessing interval 10000→2000** (`ad7e845b`, the largest
single win: duthen-50 crosses to 7.1 s, asp closes, hdp/minigzip +4).

## Your entry point: target #1 — `subtree_bool_atoms` (hdp class, 10 gap cells)

Fresh profile of `hdp/3365` (bst/hdp, 11–14 s class): **assert side
69.1 %**, of which `assert_fold::fold` 39.1 % → `ctx_simplify` 39.0 %
→ **`subtree_bool_atoms` 37.1 % with 35.1 % of the whole run inside
`HashSet::insert`**.  The pass builds per-node Boolean-atom sets per
assertion by element-wise hashed unions over the meganode DAG
(`nixie-core/src/ast/manager/query/simplify.rs`, fn at ~line 968).

Two fix shapes, both counter-identical by construction:
1. **Sorted `SmallVec<TermId, N>` sets** with merge-unions — no
   hashing anywhere; membership = binary search (the only consumer,
   `ctx_signature`, iterates a small context and tests membership).
   Keep the `MAX_MEMO_ATOM_SET`/None semantics.
2. **Manager-level per-term memo** — the atom sets are immutable term
   properties; assertions share meganode prefixes, so compute once
   (solver-owned memo — see the blastable-memo precedent for why NOT
   thread-local: TermIds are manager-relative).

Sizing: ceiling ≈ −30 % of the class; the 10 hdp gap cells
(`bst/hdp/predicate_3047..3422`, `nested/hdp/predicate_3128`) sit at
11–14 s against a 10 s cap — this is sized to cross several.

**Then** target #2 (minigzip block, 33 gap cells, the largest
cluster): pure SAT-kernel profile — propagate 36.5 % with `scan_list`
15.7 % + `WatchCursor::next` 15.3 %.  The untried counter-safe entry
is the **prefetch over-issue audit** (`prefetch_watch_payload` was
13.6 % of duthen-50; the session kernel issues 3 prefetches per binary
assignment).  Watch-list representation (CSR) is corpus-negative
(+16 %, 2026-09-20) — do not retry without new evidence.  Target #3:
9 misc singles — one profiling pass to test for a shared shape.

## Measurement discipline (hard-won; every rule below has a recorded incident)

- **Matched interleaved A/Bs are the only decision-grade instrument.**
  Single-arm counts drift with load (148–150 observed on the same
  binary; a 410-at-load-7 vs 396-at-load-21 family spread).
- **Deterministic counters, never wall, as the primary metric** — the
  SMT path is seed-invariant (identical counters across
  `NIXIE_SAT_SEED`), so single runs ARE valid trajectory comparisons
  here; the BENCHMARKING.md §4 seed machinery applies only where the
  RNG is actually consulted.
- **Heuristic/schedule changes** (anything trajectory-altering):
  matched null + the full `docs/BENCHMARKING.md` apparatus.  The
  inprocessing-interval landing (`ad7e845b`) is the worked example —
  null-arm via the existing `NIXIE_INPROC_SCHED_NULL`.
- **Traps**: `--stats` writes to **stderr** (a `2>/dev/null` scan once
  read every cell as timeout); identity checks must assert a
  **non-empty verdict** before comparing (an exec-failure once
  compared empty-to-empty); verify the binary exists after concurrent
  cargo activity; `budget_bitblast` has a load-sensitive test now
  hardened to a counter budget.

## Verification bar

Per commit: `cargo fmt --all -- --check`, clippy (doc-warnings =
fail), targeted tests.  At intervals and before any heuristic landing:
```bash
taskset -c 0-7 cargo nextest run --release --workspace --all-features   # 12,810 pass
taskset -c 0-7 ./bench/z3_parity/run_parity.sh                          # 171 Correct / 6 Inconclusive
taskset -c 0-7 bench/perf_gate/run_gate.sh                              # counters ≤1.05, wall ≤1.25
```
Counter-identity on probe cells for pure-perf changes (minigzip
predicate_492, BBB-32, duthen-50, hdp 3128; assert non-empty
verdicts).  Cache every landed binary under `precompile/<sha>/`.

## Machine policy

Shared 20-core box, other agents active (sigid benches, compile
storms; load has hit 60).  `~/.cargo/config.toml` caps builds at 8
jobs; **prefix every test/gate/benchmark with `taskset -c 0-7`**;
record matched pairs when load >10.  Never `git stash`/`restore`;
worktrees for old revisions; clean up your worktrees and scratch.

## Session-start ritual

```bash
git log --oneline -3 && git status --short        # expect clean at caf25750+
uptime                                           # note load before measuring
```
Then read `docs/HANDOFF-2026-11-15.md` (item list + the survey
section) and the study's latest addenda.  The profiling harness
recipe (standalone `Context::execute_script` bin + pprof at 250 Hz,
`RUSTFLAGS="-C force-frame-pointers=yes"`) is re-derivable from any
addendum; scratch it after use.
