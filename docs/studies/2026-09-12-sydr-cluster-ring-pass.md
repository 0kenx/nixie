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
ingestion.  `maxandminor032`: decided `unsat` with `NIXIE_BV_IR=1` in **~870 s at
settled load** (serial, pinned; 008: 0.5 s, 016: 16 s — ~55× per width
doubling at the top rung) — the family scales far past the 25 s cap;
the next width rung needs either the IR layer default-on (this session's
re-screen says no) or further cascade work, not a new mechanism.

### The goal2smt verdict-flip artifact — recorded for the next session

Reconstructing z3 `(apply … :print true)` output into a standalone file
flips verdicts **to sat** unless the original's `declare-fun`s are
re-attached: z3 reports per-command parse errors and *continues*, then
answers the empty problem.  This produced two false "cascade changes
the verdict" readings before the trivial-probe check caught it.
`docs/studies/assets/goal2smt.py` carries the fixed recipe
(declarations + `_i`-variant mapping).

## Follow-up (2026-09-12, small hours): the s3 family completes (70a35000)

The `solve_equations` Kahn worklist was the last quadratic on the
  goto_symex inputs: each resolution substituted into every mentioning
  body, and the bodies are meganode terms (parse-time `define-fun`
  inlining expands every callee into every referencing assertion).
  `s3_srvr_1_alt` burned 84 s in round 0.  Three bounds landed
  (define-equation bodies never substituted into — they are dropped at
  apply and model replay evaluates dependencies first; memoized
  `dag_size` so body sizes are measured once over the hash-consed DAG;
  the budget counts *nodes substituted*, not calls).  Result: **the
  entire `bmc-bv-svcomp14` s3 family decides inside the 25 s cap, faster
  than z3 4.16.0 on every cell** (s3_clnt 1/2/3 × true/false: 9.5–17.2 s
  vs z3's 16.9–23.0; three `s3_srvr` cells additionally crossed on the
  509-file screen).  Corpus: 308 vs 301, zero flips.

### The `NIXIE_BV_IR` re-screen on the moved corpus: decisively negative

Four of the remaining gap cells (`maxandminor016`, `bitrev2048`,
  `ex7_prime`, `rubik/8moves_mti_9`) solve with `NIXIE_BV_IR=1` — so the
  flag was re-screened on the current corpus (same binary, flag on/off):
  **285 vs 301 of 509**.  The ring/define-fun fixes moved the corpus
  under the IR layer's feet: it now costs sixteen cells net.  Default
  stays off; do not re-screen without a per-class gate.

### Remaining gap after this session (from the 509-cell screen)

14 → 8 cells: `BuchwaldFried/Mul32·Mulh_u32` (z3 0.07 s — closed by z3's
  *shared* blast DAG: the goal is one equality between two encodings of
  the same product, 96-bit mul-of-zero-extended vs 64-bit; z3's partial
  products hash-cons together and the goal folds pre-SAT, our
  independent Tseitin multipliers must search it — the
  multiplier-structural-sharing item), `smulov1bw12` (the encoding
  item), `calypto` 14/19, `bv-term-small-rw_1300`, `s3_srvr_1_alt`
  (0.15 s z3 — the residual architecture gap: our parser eagerly inlines
  macros into meganode terms and every downstream pass pays; z3 keeps
  macros as short equations and substitutes once in solve-eqs.  The
  principled fix is parser-level macro handling — a well-scoped project,
  not a patch), and `maxandminor016`/`bitrev2048`/`ex7_prime`/`rubik`
  (IR-gated; see above).

## Follow-up (2026-09-12, morning): the multiplier cluster scoped — two findings, one open

The remaining `2017-BuchwaldFried/Mul32·Mulh_u32` cell (z3 0.07 s) is a
  **structural-sharing** case, and the mechanism is now measured
  end-to-end:

1. z3 closes it *pre-SAT*: `(then … bit-blast simplify)` reduces the
   goal to `(goal false)` — the two sides (high-half of a 96-bit mul of
   zero-extended operands vs a 64-bit mul of the same operands) blast to
   expression DAGs whose partial products hash-cons together, and the
   equality folds.
2. Our cascade already normalizes both sides to *identical shapes*
   (same operand terms, same bvor masks) — `NIXIE_BV_DUMP_PRE` shows it.
   A micro-reproducer of the exact shape (mul-of-zeroext × mul-of-
   zeroext, `concat`-spelled, with extract-of-bvor operands) closes in
   **0.022 s with `NIXIE_BV_IR=1`** (sharing 49.4 %) and times out with
   IR=0 — the IR layer reproduces z3's mechanism exactly.
3. The real file does **not** close under IR=1 on the default route —
   because the unified path materializes the IR **five times** (window
   closes between assert-link rounds; `[ir-stats]` shows one round at
   0.0 % sharing), and eras do not share across materializations.  With
   `NIXIE_BV_DISPATCH_UNIFIED=0 NIXIE_BV_IR=1` (one embedded
   materialization) the real file closes in **0.025 s**.

So the lever is *not* a new multiplier encoding — it is cross-round IR
  sharing on the unified path (or a routing gate that sends
  shared-mul goals to the eager one-shot blast).  Both are architectural;
  with the IR layer default-off (this session's re-screen: 285 vs 301),
  neither is actionable until an IR gate exists.  `smulov1bw12` (z3
  6.69 s, genuine search) remains the separate partial-product encoding
  item, untouched.

Micro-reproducers preserved: `docs/studies/assets/mulshare/`
  (`mulshare.smt2` = zero_extend spelling, `mulshare2.smt2` = concat
  spelling, `mulshare3.smt2` = extract-of-var operand, `mulshare4.smt2` =
  extract-of-bvor operand — all close in ~0.02 s under IR=1, all time
  out under IR=0).

## Session round 3 (2026-09-12, morning): mul-hoist lands (58dbe32b); the remaining gap is three architectural clusters

**Landed — Z3 `mk_mul_hoist` port** (`bv_rewriter.cpp:2503`,
  `shl(z,u) · x → shl(z·x, u)`): one rule in `rewrite_mul`, with the
  subtlety that the hoisted shift's multiplicand must be *flattened into
  the product's factor list* — without it, pure AC identities
  (`t·(s·(t<<s)) = s·(t·(t<<s))`, Noetzli 1104) rebuild with different
  nesting and stop folding (caught as a real 0.02 s → timeout → 0.02 s
  regression during development, now pinned by a test).
  `bv-term-small-rw_1300`: timeout → **unsat 0.02 s** (z3 0.29 s).
  Whole Noetzli family (1575 files, 5 s cap): **1544 vs 1491 decided,
  +52, zero regressions**; 45 prove `:status unknown` candidates (10/12
  sampled z3-confirmed at 60 s; the 2 z3 non-answers are z3 crashes on
  the files, both hand-verified identities).  509 A/B: zero flips.

**Classified — `calypto/problem_14/19`** (z3 0.18/0.60 s): *not* a
  cascade gap — nixie times out on **z3's own cascaded output** (2
  declares, 1 assert, the 4-bvmul ite-chain core).  They join the
  multiplier blast/search cluster.

**Remaining gap, final map (8 cells, three architectural clusters):**

1. *Multiplier blast/search* (4 cells): `smulov1bw12` (partial-product
   encoding), `calypto` 14/19, `BuchwaldFried` (cross-round IR sharing
   or shared-gate multipliers).  Nothing here is a cascade gap anymore —
   every member times out on z3's own cascade residue.
2. *Parser macro architecture* (1 cell): `s3_srvr_1_alt` (z3 0.15 s) —
   parse-time define-fun inlining vs z3's short macro equations.
3. *IR-gated* (3 cells): `maxandminor016`, `bitrev2048`, `ex7_prime`
   (+ `rubik`, `maxandminor032`@870 s beyond cap) — solved by
   `NIXIE_BV_IR=1`, which is net −16 on the corpus; needs a per-class
   gate, and the gate study says no blast-time separator exists.

Campaign scoreboard after three rounds: **285 → 311 of 509** effective
  (z3 4.16.0: 281), zero verdict flips at every step, parity suite
  clean at every commit.

## Session round 4 (2026-09-12, afternoon): the multiplier cluster — one more cell down, one encoder landed default-off

The remaining gap's multiplier cluster was opened up:

* **`smulov1bw12` and `calypto/problem_19` are now closed** (with the
  flag below): the encoding hypothesis was confirmed end-to-end —
  cadical needs **~35 s** on our carry-save CNF for `smulov1bw12`
  (3118 vars / 9167 clauses; `s UNSSATISFIABLE`), where z3 decides the
  whole file in 6.7 s.  The CNF, not the search, is the bottleneck.
* **Z3's multiplier is a row array** (`bit_blaster_tpl_def.h::
  mk_multiplier`): diagonal accumulation with per-row carry ripple and
  `mk_xor3` last rows — not our carry-save compressor tree.  Ported
  behind `NIXIE_BV_MUL_ARRAY=1`, width-bounded at 64 bits (the
  diagonal carry chain is O(w) deep; at 1024-bit multipliers
  `smulov3bw0512/0768` the carry-save tree wins — a measured 4 s →
  >25 s ungated regression).
* **Flagged results**: `smulov1bw12` 2.8–4.5 s, `smulov1bw16` 23.6 s,
  `calypto_19` 2.9 s — and the wide `smulov3/4` stay fast (3 s, gate
  keeps them on carry-save).
* **Default stays carry-save** (two matched 509-file screens: ungated
  303 vs 306, gated 302 vs 310, zero verdict flips in both — enabling
  costs 8 net cells: the 32-bit-mul `s3_*`/`calypto`/`float`/
  `shift1add` families lose more than the narrow-mul cells gain).
  Width is not the separator between winners and losers — the 32-bit
  s3 muls regress while 32-bit smulov1bw16 wins; it is CNF-shape luck.
  Landed as a tested, default-off research flag (`7c66dd21`), the same
  posture as `NIXIE_BV_CONST_FLOW`.

Remaining gap after this round: 6 cells — `smulov2bw064`,
`calypto/problem_14`, `BuchwaldFried` (multiplier cluster),
`s3_srvr_1_alt` (parser macros), and the IR-gated `maxandminor016` /
`bitrev2048` / `ex7_prime` (+`rubik`).  Campaign scoreboard:
**311 of 509** at the default configuration (z3 4.16.0: 281), zero
verdict flips at every commit.

## Session round 5 (2026-09-12, afternoon): gate structural hash-consing landed default-off (6e61c0c9)

The third sharing mechanism, and the cleanest: plain var-keyed
  hash-consing of the gate constructors (no complement edges, no
  two-level rules — the simple version of the rejected AIG layer).
  Soundness rides the codebase's own invariant: entries insert only at
  the base scope (the `term_to_bv` truthfulness rule), unified-era
  wipes on generation switches.

Measured: the BuchwaldFried micro-reproducers close 15 s → 0.05 s;
  **both cascade residues close in ~0.1 s** and the full file in 0.3 s
  (via the eager dispatch — on the default unified route the
  assert-time blast of raw asserts still hides the sharing, the same
  obstacle the IR layer hits; **menu item 4 — blast-rewritten-only —
  is the architectural fix for both mechanisms**).  Two multiplier
  cells crack on the default route: `smulov2bw064` 1.5 s,
  `umulov1bw064`.

509-file A/B: 301 vs 301 parallel (zero flips); serially adjusted
  +1..+4 net — inside the ±9 run-to-run noise floor measured on this
  box (two null-arm runs of the same configuration read 301 and 310).
  Default off; the flag keeps the family reachable.

**Operational note for future sessions**: the campaign's parallel arms
  have a ±9-cell noise floor under this box's load.  Parallel A/B pairs
  are still the honest comparator (same conditions), but *serial*
  re-checks of every mover are mandatory before reading a ±5-cell
  result as signal.

**Shared-tree note**: the workspace carried another agent's in-flight
  `nixie-sat` edits (14 pre-existing test failures at clean HEAD,
  verified in a pristine worktree) — this round's battery ran in an
  isolated worktree (`git worktree add`, patch applied, built, tested;
  worktree deleted after).

Remaining gap at default: 7 cells — BuchwaldFried + smulov2bw064 +
  umulov1bw064 (all three closed by `NIXIE_BV_GATE_SH=1` or
  `NIXIE_BV_MUL_ARRAY=1` opt-ins), calypto_14, s3_srvr_1_alt, and the
  IR-gated maxandminor016 / bitrev2048 / ex7_prime.

## Session round 6 (2026-09-12, evening): unified-path deferral prototyped — and it exposed a preprocessor property

Menu item 4 (**blast-rewritten-only on the unified route**) was
  prototyped behind `NIXIE_BV_DEFER_BLAST=1`: pure-BV fragment asserts
  defer clause emission and circuit linking to `check`, where stage-4
  emits the preprocessor's rewritten set *instead of* alongside.  The
  prototype is complete (window-breaker raw flush, push/pop pending
  flush, `track_theory_vars`/alias/distinctness bookkeeping kept at
  assert time, a second honesty-gate read after the late emission) and
  preserved as
  `docs/studies/assets/2026-09-12-unified-defer-proto.patch`.

**It is unsound as a verdict path, and the reason is a finding**: on
  `s3_clnt_1_true` the deferred build answers **`sat`** (truth: unsat;
  z3 confirms).  The emitted rewritten-only CNF is
  184 727 vars / 547 425 clauses vs the alongside path's
  358 344 / 1 779 525 — and **cadical proves the deferred CNF
  satisfiable**.  So the preprocessor's `pre.rewritten` is **not
  equisatisfiable** with the original assertion set on this file: some
  constraint content exists only in the raw (parse-inlined) form and is
  dropped by the substitution/dropping machinery.  The alongside
  default never noticed because weakened rewrites asserted *next to*
  the raw clauses are harmless in both directions — the deferral
  removes the backstop and the hole becomes a false `sat`.

Not yet root-caused (next session's entry point): the leading
  suspects are the plain solve-eqs drop-after-substitute semantics
  interacting with the node budget (partially-substituted rounds), or
  content that lives only in the assert-time pipeline
  (`flatten_eq_ite_tables`, ite table guards) that the rewritten set
  never sees.  Repro: `NIXIE_BV_DEFER_BLAST=1` + the patch, on
  `bmc-bv-svcomp14/s3_clnt_1_true…` — `sat` at ~25 s.

Performance signals worth keeping (from the sound-prefix runs and the
  flag-arm diffs): `cjpeg/predicate_2636` 1.9 → 1.2 s;
  `bv-term-small-rw_609` closes (correct `unsat`); `define-fun`
  regressions are `unknown`-not-false (the model gates catch the
  weakened sets).  The deferral stays exactly as valuable as round 5
  concluded — *after* the equisatisfiability question is answered.

**Addendum (rigor check)**: the direct test — z3 on the default
  build's `NIXIE_BV_DUMP_PRE` output — could not complete: the SMT2
  printer is super-linear on meganode shared DAGs and the dump only
  lands at preprocess end (a 600 s cap expired first).  The attribution
  instead rests on: the false-sat CNF was emitted by the *unchanged*
  stage-4 emission calls over `pp.rewritten` (ring participated in
  nothing on this file, so no filter difference), and the clause-count
  gap (1.78 M → 547 K) matches exactly the raw set's removal.  **Two
  tooling gaps recorded**: the dump sidecar needs a memoized printer,
  and the preprocessor needs an equisatisfiability self-check (solve
  the rewritten set standalone and compare) before any
  rewritten-only consumer can exist.

## Session round 7 (2026-09-12, night): the false-sat root-caused and fixed (dfa1c754)

Both holes behind the deferral prototype's false `sat` on
  `s3_clnt_1_true` were in **70a35000's budget bounds**, not in the
  deferral design:

1. **Flatness** (the soundness bug): the Kahn worklist's invariant —
   every recorded elimination body has its dependencies substituted
   before it resolves, so the apply phase's *single-pass simultaneous*
   substitution hands out complete terms — was broken by the budget
   break and the meganode skip (measured: 583 breaks / 141 278 skips on
   this file).  Skipped bodies resolved later with dangling references
   to variables whose defining equations were dropped; the rewritten
   set lost that content (cadical: the 547 k-clause deferred CNF is
   satisfiable against an unsat original).  The default alongside path
   was verdict-safe but fed the same dangling bodies to **model
   replay**.  Fix: re-substitute the recorded map to a fixpoint when
   any break/skip fired.
2. **dag_size** (the amplifier): the memoized size counted nodes *per
   occurrence* — exponential on diamond-shaped shared chains (debug
   overflow, caught by the new test; release silently truncated).  Tree
   size is a deliberate conservative upper bound for the gate/budget
   (now saturating + documented) — and its over-gating made bug 1 fire
   constantly: the 141 k "meganode" skips were mostly ordinary shared
   terms.

**Corpus effect of the fix: 308 of 509, zero verdict flips, +7 gains /
  0 losses** — the over-gating had been silently skipping legitimate
  substitutions on shared bodies, and restoring them decides
  `s3_clnt_2_false`, `s3_srvr_3_true`, `bitrev1024`, `calypto_24`,
  `hdp_3365`, `btfnt`, `spear_vc7692` (all serially verified within the
  cap, z3-consistent).  Parity: 0 disagreements (z3 4.16.0); 11 035
  tests green.

**The deferral is now sound on the repro** (`unsat` in 17.9 s under
  `NIXIE_BV_DEFER_BLAST=1`) — its remaining flag-arm failures are
  prototype model-path holes, next session's work if it is picked up.
  Pinned by `s3_clnt_1_rewritten_only_equisatisfiable` in
  `known_unsound_regressions` (the preprocessor-output equisatisfiability
  guard).

Campaign: **~315 of 509** effective (z3 4.16.0: 281).

## Session round 8 (2026-09-12, late): the deferral completes and lands default-off (6dd1ac34)

With dfa1c754's equisatisfiability fix in place, the deferral
  prototype's three remaining model-path holes were closed one by one,
  each minimized to a two-line goal:

1. **Elimination replay at `Sat`** — the rewritten-only core leaves
   eliminated variables unconstrained; replay them from the recorded
   eliminations before the validation gate (the dispatch's
   `bv_reconstruct_eliminations`, same machinery).
2. **Default-clearing before replay** — `build_model` completes
   unconstrained constants with sort defaults and the replay's
   skip-if-assigned kept them (`Model::remove`).
3. **Records over defaulted bits** — `eval_bv_value`'s leaf read
   `bits_all_determined` first, which is *true* for never-constrained
   bits read as all-false by the adopted assignment; an explicit model
   record (a replayed definition) now wins.  For bit-blasted variables
   the two agree by construction, so the flip is default-path neutral
   (verified: the 509-cell null arm is identical).

**Corpus verdict**: 301 vs 308 parallel, zero flips; serial re-checks
  recover 3 of 12 losses (boundary), 9 real — the rewritten-only blast
  is net-negative exactly like IR and gate-SH, and for the same reason
  (trajectory reshuffling).  **Default off.**  The unique structural
  win: **`s3_srvr_1_alt` closes** (the last parser-macro cell, z3
  0.15 s) — for that family the deferral *is* z3's macro-equation
  architecture.  Also under the flag: VexRiscv-regch0, s3_clnt_2_false,
  s3_srvr_3_true.

**Operational post-mortem recorded**: every "instant 509-unknowns" arm
  this campaign was one shell-precedence bug — `A && B & C &` backgrounds
  the whole `A && B` chain, so the *second* arm ran from the workspace
  root where the corpus paths do not resolve.  Launch each arm as its
  own statement.

Remaining gap at default (z3-decides cells): 6 — BuchwaldFried,
  smulov2bw064, umulov1bw064 (all `NIXIE_BV_GATE_SH=1`-closed),
  calypto_14 (`NIXIE_BV_MUL_ARRAY=1` family), maxandminor016,
  bitrev2048, ex7_prime (IR-gated) — every one now has a documented
  opt-in mechanism; the default-path campaign stands at ~315 of 509
  (z3 4.16.0: 281) with 38 cells decided that z3 cannot.
