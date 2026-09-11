# The Sydr cluster: ring-pass rescans were the whole gap (cjpeg/symbolic_memory/spear)

**Date:** 2026-09-11 → 2026-09-12. **Task:** handover menu item 1 — the
`cjpeg`/`s3_clnt`/`symbolic_memory` cluster (~10 cells), "unmoved by
everything this session (all timeout both arms)".

**Verdict: two preprocessing-layer bugs, one landed fix (+10 cells), and a
corrected diagnosis of what z3 actually does.**

1. **The cluster's blocker was never the search.** `bv_preprocess_assertions`
   never *returned* on these files: `solve_ring_equations` rebuilt, on every
   elimination round, the polynomial of every asserted equality and the
   variable-occurrence table of every assertion (a full DAG walk each), and
   these files feed it one eliminable variable per round for thousands of
   rounds. `master/cjpeg/predicate_2636` burned >390 s inside the pass and
   never reached bit-blast — in *both* IR arms, which is why nothing this
   session moved them.
2. **The landed fix** (incremental occurrence/mention index + swap-repairing
   `drop_pair`, elimination sequence bit-identical — 876 elims on
   `predicate_227` before and after, 2.9 s → 4.8 ms) **plus** memoizing the
   `PreprocessOutcome` across the dispatch→stage-4 double run (it was
   computed twice per check on identical input, and the second run is what
   the stage-4 parity pass asserts).
3. **Cluster outcome** (treatment build, 60 s cap, pinned core; `unknown`
   before at 25 s and at 120 s):

   | file | z3 4.16.0 (banked 25 s) | now |
   |---|---|---|
   | `master/cjpeg/predicate_1804` | unsat 14.4 s | **unsat 1.7 s** |
   | `master/cjpeg/predicate_988` | unsat 23.2 s | **unsat 0.9 s** |
   | `master/cjpeg/predicate_2710` | unsat 24.2 s | **unsat 2.8 s** |
   | `master/cjpeg/predicate_1963` | unknown | **sat 1.9 s** (z3@300 s: sat ✓) |
   | `symbolic_memory/bst/hdp/predicate_3365` | unsat 17.5 s | **unsat 18.8 s** |
   | `symbolic_memory/linear/readelf/predicate_2300` | unknown | **unsat 4.6 s** (z3@300 s: unsat ✓) |
   | `spear/bin_libmsrpc_vc1232059` | sat 17.3 s | **sat 1.4 s** |
   | `spear/bin_libsmbsharemodes_vc6344` | sat 16.5 s | **sat 0.8 s** |
   | `spear/bin_libsmbsharemodes_vc7692` | sat 15.4 s | **sat 8.0 s** |
   | `spear/bin_libsmbsharemodes_vc4817` | sat 15.3 s | **sat 4.6 s** |

   Not moved: `cjpeg/predicate_2468` (preprocess now 0.46 s; search-hard —
   z3 itself needs 11.7 s) and the four `bmc-bv-svcomp14/s3_clnt*` cells —
   see (4), they are a different bug.
4. **s3_clnt is ingestion-bound, not solve-bound.** `check()` is never
   reached in 40 s: the file declares 40958 `define-fun`s (131k lines), and
   a no-assert parse-only variant already costs nixie **7.8 s** (z3: 0.2 s;
   full file z3: 2.17 s). A perf profile of the stuck run shows the time
   spread across `parser::terms`, `encode`, and `bv_unified` linking with
   no single hotspot — macro-expansion volume. Fixing this cluster means
   parser/macro-processing throughput work, not solver work.
5. **The "z3 decides cjpeg by post-blast substitution" attribution is
   wrong for these files.** z3's trace on `predicate_2636` shows the
   `simplifier → propagate-values → … → bit-blast → simplifier → solve-eqs`
   cascade closing the goal at the *post-blast* `solve-eqs` — but feeding
   nixie **z3's pre-blast `simplify`-only output already solves the file in
   2.6 s** (vs >390 s raw, both IR arms). The gap was ours: the term
   cascade nixie already ships folds these files fine *when it gets to
   run*. (The same was independently true of the maxandminor family — the
   corrected recipe below supersedes the earlier `(apply …)` probe mistakes
   recorded in `2026-09-11-bv-constflow-results.md`.)

## The cascade-dump recipe (now trustworthy)

`(apply (then simplify …) :print true)` + reconstruction into a standalone
SMT2 file. Two traps, both of which silently flip the reconstructed
verdict to `sat`:

- **Declarations are not part of the goal print.** Re-attaching the
  original's `declare-fun`s is mandatory — z3 reports per-command parse
  errors *and continues*, then answers the empty problem `sat`. (This exact
  artifact produced two false "cascade flips verdict" readings before being
  caught.)
- **The printer emits internal div/rem variants** (`bvsdiv_i`, `bvudiv_i`,
  …): the "semantic-attached" total-function versions; mapping them back to
  the SMT-LIB names is faithful.

Assets: `docs/studies/assets/goal2smt.py` (goal→SMT2 converter),
`bisect_cascade.sh` (stage-prefix bisect), `cluster_sweep.sh` (the cell
table above). nixie side: `NIXIE_BV_DUMP_PRE=<path>` writes the
post-cascade assertion set (landed with this fix) — the same diff, against
our own cascade, no z3 needed.

## What landed

- `nixie-solver/src/solver/bv_preprocess.rs`: `solve_ring_equations`
  rewritten over an incremental `mentions` index (var → mentioning pair
  indices) + per-pair cached polynomials and variable sets; `drop_pair`
  swap-repairs the index. Per elimination round the work is the candidate
  scan (pure poly scan, no DAG walks) plus re-derivation of the ≤
  `MAX_OTHER_OCCS` substituted pairs — the same terms the historical code
  substituted, so the elimination sequence is unchanged (verified: 876
  eliminations on `predicate_227`, before and after).
- `Solver::bv_preprocess_cache: Option<(usize, PreprocessOutcome)>` — the
  dispatch's routing trial and the stage-4 parity pass share one
  computation per assertion set; invalidated on new assertions (count
  moved) and cleared on `push`/`pop`/`reset`.
- `NIXIE_PRE_TRACE=1` (stage timings + elimination counts) and
  `NIXIE_BV_DUMP_PRE=<path>` (post-cascade SMT2 dump) kept as diagnostics —
  the two instruments that localized the hang in minutes.
- Regression battery `nixie-solver/tests/bv_ring_elim_regressions.rs`:
  unsat through a 1500-link eliminable cycle, model telescope across
  replayed eliminations (`x_1 − x_N ≡ N−1 (mod 2^w)`), the odd/even
  invertibility gate, and cache invalidation across
  assert/check/push/pop sequences.

## Do-not-retry / next levers

- Do not reintroduce per-round rescans into the ring pass (the tests'
  1500-link chain is the canary — it exists to make that change visibly
  slow again).
- The remaining `cjpeg/predicate_2468` is search-hard after a 0.46 s
  preprocess; the z3 gap there is the SAT search, not preprocessing.
- The s3_clnt family needs parser/`define-fun`-expansion throughput work
  (7.8 s parse-only on a 2.17 s z3 file). A per-`define-fun` body-hash
  sharing check (expand once, hash-cons the expansion) is the obvious
  first probe — the bodies repeat heavily across the 40958 definitions.

## Session close (2026-09-12, early hours): the s3_clnt ingestion bug — define-fun asserts (5de0ccb8)

The parse-only measurement above was itself misread (`time | tail -1`
showed `sys`, not `real`): ingestion was not 7.8 s but **unbounded** —
16 k declares+defines already exceeded 120 s, and the full file never
reached `check()` at any cap.  Root cause: the Context asserted
`(= name body)` for every nullary `define-fun` (for `get-model`
visibility), and 40958 of those ran the full per-assert encode/blast
pipeline over chained inlined bodies — quadratic.

Two-round fix (both in `5de0ccb8`):

1. **Alias, not assertion** (z3 macro semantics): the name is declared
   for introspection; `get-model` lists it at its defined value,
   resolved by substituting model assignments into the body at each
   `sat` verdict (`Model::eval` has no BV operator arms — the
   substitute-then-simplify recipe `get-value` uses).  Ingestion of the
   16 k-declare prefix: >120 s → 3.5 s.
2. **Preprocessor seeding**: the definition equations enter
   `bv_preprocess_assertions`' working set (not the solver), where
   `solve_equations` substitutes them into the user assertions exactly
   as the old asserted form did.  This round exists because the naive
   alias-only build **regressed `challenge/integerOverflow` from 0.02 s
   to timeout**: that file closes through the *seeded equations* (the
   cascade folds the short named forms; the pure-inlined `sign_extend`
   concat trees do not fold) — a real A/B catch, not a hypothetical.
   Cost bounds in the same commit: a clean-subtree memo for the mention
   walk, a self-check skip for unsubstituted bodies, and a
   deterministic 100 k-call substitution budget.

Cluster state at close (all z3-consistent, serial pinned):

| file | z3 4.16.0 | nixie before session | nixie now |
|---|---|---|---|
| cjpeg 1804/988/2710 | unsat 14–24 s | timeout | **unsat 1.7–2.8 s** |
| cjpeg 1963 | unknown (25 s) | timeout | **sat 2.1 s** (z3@300 s ✓) |
| cjpeg 2468 | sat 11.7 s | timeout | **sat 3.7 s** |
| readelf/2300 | unknown (25 s) | timeout | **unsat 8.6 s** (z3@300 s ✓) |
| hdp/3365 | unsat 17.5 s | timeout | **unsat 19.3 s** |
| spear ×4 | sat 15–17 s | timeout | **sat 0.8–9.7 s** |
| s3_clnt_1_true | unsat 16.9 s | check never reached | **unsat 102 s** |
| s3_clnt_3_false | sat 17.0 s | check never reached | **sat 57 s** |
| s3_clnt_2_false, 3_true | sat/unsat 19–23 s | check never reached | >300 s (search) |

The two remaining s3_clnt cells now reach the search with the right
structure; their gap to z3 is search speed — a different work item from
ingestion.  `maxandminor032`: decided `unsat` with `NIXIE_BV_IR=1` in
~17 min under load (016: 16 s) — the family scales past the 25 s cap;
the next width rung needs the IR layer default-on or further cascade
work, not a new mechanism.

### The goal2smt verdict-flip artifact — recorded for the next session

Reconstructing z3 `(apply … :print true)` output into a standalone file
flips verdicts **to sat** unless the original's `declare-fun`s are
re-attached: z3 reports per-command parse errors and *continues*, then
answers the empty problem.  This produced two false "cascade changes
the verdict" readings before the trivial-probe check caught it.
`docs/studies/assets/goal2smt.py` carries the fixed recipe
(declarations + `_i`-variant mapping).
