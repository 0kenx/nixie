# Handover: QF_BV false-sat (nlzbs128 family) + the z3 perf gap measurement

Status date: 2026-09-09. Worktree: `nixie-bv` @ main (landing commit adds
the tooling described below).

## The performance gap (measured, reproducible)

509-file stratified sample of `smt-lib/non-incremental/QF_BV` (12 per
family, 56 families, seed 42; list in
`precompile/<sha>/benchmark/bv_gap/list.txt`), 25 s cap, cores 10–19,
nixie (release) vs system z3 **4.16.0**:

| | nixie | z3 |
|---|---|---|
| solved-at-cap (of 509) | **213** | **281** |
| only-one-sided solves | 8 | 76 |

Worst one-sided families: brummayerbiere4 0/10, uclid 4/12, RWS 3/10,
Sydr 3/9, asp 0/4, UltimateAutomizer* 0/5+. **61 both-solved cells where
nixie is >5× slower** than z3 (z3 solves them in 0.05–0.6 s: nlzbs/bitrev
class = rewriting, uclid/catchconv = preprocessing, BBB-32/tacas).
Raw cells: `precompile/<sha>/benchmark/bv_gap/cells.jsonl` + runner.

A separate cheap finding: mux/increment chain identities
(`ite(bit_i, c+1, c)` nested n-deep, forward vs reverse order) are
*unsat-provable* by z3 at n≤16 in seconds but nixie hits `unknown` at
n≥12–16 depending on width — the equivalence-content class again; the
kitten-sweep/definitions machinery may be exactly the lever here.

## SOUNDNESS BUG (top priority, open): false `sat` on width-128 nlz files

**Nixie answers `sat` on `brummayerbiere/nlzbs128.smt2` and
`nlzbsdown128.smt2`** (both `:status unsat`, z3: unsat). nlzbs256 →
unknown. Widths ≤ 64 answer correctly. The reported model **does not
satisfy the formula** (verified: z3 rejects `x = model ∧ formula`; a
width-masked exact Python evaluator over the 410-let chain agrees with
z3), **and nixie's own `--validate-model` blesses the model** — so the
shared evaluation path is also wrong, or validates the wrong object.

### What is known (all evidence reproducible from the raw artifacts)

1. **Both BV routes** produce it (unified default and
   `NIXIE_BV_DISPATCH_UNIFIED=0`). Not routing-specific.
2. **Not preprocessing**: `simplify false`, `NIXIE_SWEEP=0`,
   `NIXIE_ELS_FORCE=0`, `NIXIE_PROBE_PERMILLE=0` all still `sat`.
3. **Not the SAT search**: the CNF dumped at solve entry
   (`NIXIE_DUMP_CNF`, tooling landed with this commit) is **SAT per
   kissat** — the solver's own entry formula is satisfiable, i.e. the
   *blast emits an under-constrained network* in this context.
4. **Not the isolated circuits**: unit test
   `lshr_const64_forces_zero_high_bits` (landed) pins x=0, amount=k and
   checks every out-of-range result bit of `bv_lshr` is forced false at
   widths 64/96/128, amounts 32/48/64/96 — the barrel shifter alone is
   correct. Standalone symbolic shift identities
   (`lshr/shl/ashr x const` vs concat/extract forms, all widths) are
   correct end-to-end. Single-op and small-compound micro-tests at
   width 128 all agree with z3.
5. **Context-dependence**: pinning `x` to *any* concrete value (an extra
   assert) makes the file `unsat` (correct) — the under-constraint only
   manifests with symbolic x and the full 410-let DAG. Tautology
   add-ons don't flip it; it is the pinning (constant folding at blast
   time) that hides it.
6. Under kissat's satisfying model, the circuit value of
   `bvlshr(x, 64)` has bit 64 free-true while x reads all-zero — the
   network does not force it — but the same term standalone encodes
   tight (point 4). So some *interaction* (two link passes, the
   `get_bv(tid).is_some()` skip in `encode_bv_term_recursive`, eq/ult
   caches, free-vector fallback interplay) drops constraints.
7. **Zero completely-free bits**: every blasted var occurs in ≥1 clause;
   the under-constraint is structural (clauses exist but don't define),
   not "term never encoded".

### Tooling landed (all env-gated no-ops when unset)

- `NIXIE_DUMP_CNF=<path>` — DIMACS snapshot at first solve entry
  (`Solver::solve` and `Solver::solve_with_theory`).
- `NIXIE_DUMP_TERMS=<path>` — sidecar `term → bits / atom var` map with
  op kinds and child ids, plus a free-bit scan report.
- `BvSolver::{debug_bv_terms, debug_bool_nodes}` accessors; test-gated
  pin/solve accessors; the lshr regression unit test.

### Suggested next steps (in order)

1. Rebuild the pipeline as a **unit test**: parse nlzbs128 in-process,
   run the unified link passes, then under a SAT model of the dumped CNF
   evaluate every gate chain (the sidecar gives bits per term) and find
   the first term whose *defining clauses* fail to pin it. The hand
   analysis stopped at "TermId(7) bvlshr loose in context, tight alone"
   — the culprit is whatever distinguishes the in-context encode
   (skip-guard ordering? `bv_sorted` dedup? second link pass re-walk?)
2. Suspect list from reading: `encode_bv_term_recursive`'s early-skip on
   `bv.get_bv(tid)` (a term first given bits by the *free-vector
   fallback* or by `collect_unified_bv_terms`-side allocation is never
   really encoded), and `BvAtomToLink` re-linking in the second pass.
3. The width ≥128 + "works ≤64" boundary also suggests checking every
   `u64`/`usize`-vs-width assumption in `bv/` (though the lshr test
   weakens that hypothesis).

## Parser leniency bug (separate, small, worth its own fix)

Nixie **accepts ill-typed terms** and answers on them (3 sightings):
BV1 term used directly as an `ite` condition; equality between BV1 and
BV128 operands. z3 rejects both with sort errors. Any of these could
alias into soundness paths; the typechecker should reject.

## Corpus-symlink note for worktree testing

`nixie-testcorpus` resolves corpora relative to the worktree root;
worktrees don't carry the gitignored corpora, so 14 corpus-backed tests
fail there. Symlink them in (`ln -s <main>/smt-lib smt-lib` etc.) or the
suite is not green in a worktree.

## RESOLUTION (same day, second session): root cause found and fixed

**`encode_add_const` read `(constant >> i) & 1` with `constant: u64` over
bit positions `i` up to the vector width.** In release, `>>` masks the
shift amount modulo 64, so position `i ≥ 64` re-read bit `i mod 64` —
`bvsub` at width ≥ 65 encoded `−b = ~b + 2^64 + 1` instead of `~b + 1`
(constant 1's bit 0 re-read at position 64). The wrong circuit is still
*consistently satisfiable*, so the solver completed with a false `sat`
whose model satisfies the wrong circuit — exactly the width boundary
(≤ 64 correct, 128 false).

Found via the landed tooling plus one decisive unit-level probe: a debug
build PANICKED (`attempt to shift right with overflow`) in
`encode_add_const` where release silently wrapped.

**Fixed sites** (all the `u64`-shift-at-`i≥64` family):
- `bv/solver.rs encode_add_const` — the soundness bug;
- `bv/solver.rs get_model` — value grouping keyed `1u64 << i` beyond 64
  (wide values collided into one group → wrong model merging); wide terms
  now get singleton groups;
- `bv/aig.rs constant_bitvector` and `bv/aig_builder.rs` — same wrapped
  const-bit reads.

**Evidence chain**: pre-fix precompile binary says `sat` on
nlzbs128/nlzbsdown128; fixed worktree binary says `unsat` (both match
z3); the new unit test `bvsub_wide_matches_exact_semantics` (width-128
subtraction, every result bit forced) FAILS pre-fix and PASSES post-fix;
the corpus-level `audit_nlzbs128_circuits` test (env-gated
`NIXIE_AUDIT_NLZBS`) asserts Unsat.

**Corpus impact**: the wrong `bvsub` circuit didn't just falsify two
files — re-screening the 509-file QF_BV sample, the fix flips **50
verdicts** (mostly `unknown` → decided; `log-slicing/bvsub_*` literally
names the op) and takes nixie from **213 → 263 solved** (z3: 281). The
gap shrinks from 68 to 18 files.

**Incident note (measurement discipline)**: during the hunt, verdicts
appeared to flip between identical binaries. Cause: shell cwd drifted
between the shared main checkout and the worktree (different binaries),
and the worktree was briefly touched by another agent (HEAD moved).
Lesson recorded: always `pwd` + `md5sum` the binary in the same block as
the verdict when chasing nondeterminism. A residual unexplained
observation: one intermediate build (all fixes, pre-fmt) still said
`sat` on nlzbs128; every build since is stably `unsat`. If the false
sat ever resurfaces build-to-build, suspect a second, layout-sensitive
site — the env-gated corpus test is the canary.

**Also fixed this session**: `NIXIE_DUMP_CNF_AT_SAT` (dump the formula
at the sat return — search-added clauses included) landed alongside the
fix for future blast-vs-core splits.

## Post-landing correction (final numbers)

The 509-cell re-screen first ran with a stale worktree binary (another
agent rebuilt the shared `target/` mid-session — the binary at a fixed
path changed md5 three times). Final, verified numbers with the
**committed** `ac13904` binary (`md5 64e6c14…`, built in an isolated
`CARGO_TARGET_DIR`, `unsat` on nlzbs128 ×3):

- **266 of 509 solved** (pre-fix 213, z3 281) — gap 68 → 15;
- **0 verdict disagreements vs z3** (the one recorded nlzbs128 `sat` was
  the stale binary; corrected cell banked in
  `precompile/ac13904/benchmark/bv_gap/fixed_cells.jsonl`).

Remaining gap families (next perf targets): brummayerbiere4 (0 vs 10),
Sydr (5 vs 9), bmc-bv-svcomp14 (5 vs 9), UltimateAutomizer-2023 (2 vs
5), plus one-file losses scattered. The 256-bit nlz variants are honest
timeouts (z3 solves them — wide-width blasting cost).

Measurement lesson (twice in one session): **verify the binary md5 in
the same shell block as any verdict**, and never source a benchmark
binary from a shared, concurrently-rebuilt `target/` — the precompile
cache exists precisely to freeze one artifact per commit.

## Follow-up plan: the remaining 15-net (44 gross) file gap vs z3

Cluster map of the 44 one-sided losses (z3 solves, nixie does not, 25 s
cap), from `precompile/ac13904/benchmark/bv_gap/`:

### Tier A — preprocessing/rewriting gap (~17 files, z3 < 1 s each)

z3's rewriter solves these **before search**; we blast giant circuits.

1. **`elim-unconstrained` (10 files: `brummayerbiere4/unconstrained01-10`,
   z3 0.1 s)** — 6×1024-bit vars each occurring **once**; z3's
   unconstrained-variable propagation replaces the whole goal with a
   free atom. The tactic is an **empty stub** in nixie
   (`nixie-core/src/tactic/core/elim_unconstrained.rs` — every method is
   an `#[allow(dead_code)]` no-op). Port z3's
   `tactic/core/elim_unconstrained*.cpp` + `elim_unconstrained.cpp`
   rules (reference in `../temp/z3/`; Brummayer-Biere, MEMICS'09).
   Soundness notes: satisfiability-preserving only (assert the rewrite
   alongside, as the stage-4 dispatch preprocessor does, or gate model
   production); per-operator reachability conditions are load-bearing.
2. **Bit-hack/structural rewriting (~7 files)** —
   `maxandminor016`/`bitrev1024`/`calypto problem_14/19`/`sage
   bench_4443`/`BuchwaldFried counterexample`: concat/extract
   normalization (extract-of-concat, concat-of-extracts merge),
   AND/OR/NOT constant push. z3's `bv_rewriter` is the reference.
3. **Polynomial normalization (3 files: `cohencu.c_2/3/4`, z3 0.1 s)** —
   32-bit mul/add chains encoding z=3n², y=3n+3n²−1; z3's
   sum-of-monomials canonicalization substitutes the linear relations
   and collapses to a univariate quadratic. The dispatch preprocessor's
   existing SOM/poly-identity pass (stage-4 study) is close — extend or
   fix its routing (`goal_is_pure_bv` declines these: widths < 32).

### Tier B — search gap (~27 files, z3 1–24 s)

`Sydr/cjpeg` predicates (5, z3 8–24 s — bvmul CEGAR territory),
`bmc-bv-svcomp14/s3_clnt*` (4), `spear/samba` (2), `Sydr/symbolic_memory`,
`2019-Wolf zipcpu`, wide-nlz 256-bit variants. These need measured work
on the CEGAR lemma tiers / search, not rewriting.

### Artifacts

- binaries: `precompile/ac13904/nixie` (md5 64e6c14…, isolated build);
- cells: `precompile/ac13904/benchmark/bv_gap/{gap_cells,fixed_cells}.jsonl`;
- reproducer family + audit scripts: `precompile/45e2657/benchmark/bv_gap/`.
