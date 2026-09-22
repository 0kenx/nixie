# Handover — the composed stack is default-on (par-2 0.642); the parse arc closed at −47 %; where everything stands (2026-09-22)

Continuation of the 2026-09-21 chain.  **READ THIS ONE'S TREE-STATE
WARNING FIRST.**  AGENTS.md applies as always.

## ⚠ Tree-state warning (cost me two near-miss landings)

The shared primary checkout's HEAD sits on **`parse-arc-wip-snapshot`**
(a snapshot branch an agent created to preserve in-flight edits),
while **`main` is several commits ahead**.  A plain `git commit` from
the primary tree lands on the SNAPSHOT branch, not main.  Either land
from a worktree, or use the **temporary-index pattern** (no checkout —
it cannot disturb the other agents' live files):

```bash
export GIT_INDEX_FILE=$PWD/.tmp-idx && rm -f $GIT_INDEX_FILE
git read-tree main
git add <your files>          # exactly yours, never -a
TREE=$(git write-tree); unset GIT_INDEX_FILE
NEW=$(git commit-tree $TREE -p main -m "...")
git update-ref refs/heads/main $NEW && rm -f .tmp-idx
```

Do **not** `git checkout main` in the primary tree: the snapshot branch
is what keeps the FSM agent's in-flight files on disk.

## What landed (2026-09-21 → 09-22, this arc)

1. **`c0eade40` feat(sat)!: the composed fold stack is DEFAULT ON** —
   the par-2 flip (operator-directed decision rule).  SSR-binaries +
   pre-search ELS + gate-subsumption on by default; each with the
   same-name `=0` opt-out.  par-2 0.642 (12 cells × 3 seeds); the
   10-seed replication: frb **0.30×** (on's worst seed beats off's
   median), WS **0.60×** (the 0.20× was seed-luck — stated honestly),
   b21 neutral, Carry +0.8 s median.  Parity 176/0/1 under the flipped
   default; the three QF_BV known-unsound guards pass (after the corpus
   refill below).  BASELINE re-pinned to the flip; binary cached
   `precompile/c0eade40`.
2. **The parse pipeline**: SIMD tokenizer → fused blockwise tokenizer →
   lazy BIG overflow + parse_lit register path → mmap input.  **−47 %
   whole-run instructions** on the 531 MB hwmcc anatomy; the remaining
   wall gap to kissat is SYS time (page faults on the resident
   formula + the Vec-of-Vec watch headers) — an architecture statement,
   not a backlog; every restructuring priced negative (see the
   do-not-retry records).
3. **Two false-sats fixed**, one pre-existing in the default config
   (class-crossing level-0 units in the fold — `CE2_MIN`, 16 clauses,
   plain CLI answered sat on an UNSAT formula), one in the
   gate-subsumption port's first draft (mutual equal-set retirement).
4. **Search quality: parity with kissat on the frozen residual**
   (7,787 vs 7,645 conflicts on identical bytes; the old study's 16-36×
   gap is gone).  Kissat's own end-to-end on the anatomy reads 8,399 —
   the study's 9,465 was an option-set leak (caught in review).

## Standing traps (new since the last handover)

- **Fault counts are NOT deterministic** (603–635 k band on the
  anatomy; ±3 %).  Band-vs-band separation or nothing.
- **mimalloc recycles doubling-growth frees** — "allocation slack" is
  not fresh pages; exact-capacity materializations priced negative
  under BOTH lenses (instructions and faults).  Three strikes recorded.
- **The fold's collapse is substitutions + BIG edges** — arena
  `num_original` never drops; any retirement-ratio gate reads zero
  (`NIXIE_FOLD_BVE_SKIP`'s numerator is dead as specced).
- **Small formulas are answered by the default fold pre-search** —
  tests asserting on conflict hooks/LBD must pin the legacy trajectory
  (the `legacy_search_only` knob pattern; see conflict.rs).
- The perf gate reads 1.362 vs the pre-flip pin **by design** — the
  flip's citation is the par-2 experiment; EXPECT_TRAJECTORY_SHIFT
  semantics.
- **The QF_BV corpus was wiped and refilled** (2026-09-21 disk crisis;
  Zenodo recipe in `smt-lib/PROVENANCE.md`).  If corpus tests fail
  loudly, check `smt-lib/non-incremental/` occupancy first.
- `rg -rn` replaces matches with the letter n; `/tmp` is policed by the
  operator — scratch lives in repo-local dotfiles, deleted on landing.

## Open items (ranked)

1. **The anatomy's 1.55× wall under the flip** — the fold's
   preprocessing on a formula already decided at load (0 conflicts both
   arms).  A propagate-before-ELS check would skip it; marginal on
   par-2, clean shape, unclaimed.
2. **The watch-world architecture** (380 MB of `Vec` headers, 95 k
   pages) — the CSR world exists opt-in (`NIXIE_CSR_B=1`), corpus-priced
   as default-refused; only revisit with new allocator evidence.
3. The FSM agent's branch (`parse-arc-wip-snapshot`) needs merging or
   retiring by its owner when their arc closes.

## Where everything lives

- `docs/studies/2026-09-21-parse-pipeline-followup.md` — the parse arc
  (5 addenda: every priced ablation and both do-not-retry records).
- `docs/studies/2026-09-21-gate-subsumption-class-units.md` — the
  port, the false-sat, the discriminator map, the par-2 flip + the
  10-seed replication.
- `docs/studies/2026-09-18-ssr-binaries.md` — the residual-parity
  closure + the kissat 8,399 correction.
- `bench/perf_gate/paired_instructions.sh` / `env_ab.sh` — trap 23's
  tool and the env-armed A/B harness.
- `precompile/c0eade40/nixie` — the current pinned baseline binary.
