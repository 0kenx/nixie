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
