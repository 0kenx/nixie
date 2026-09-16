# Handoff: the set-family model finder — one minimized goal from `sat`

**Date:** 2026-09-16
**Arc:** `docs/studies/2026-09-14-model-finder-constructor-tables.md` (701 lines, twelve follow-ups — read it first; this handoff is the map, the study is the territory).
**Goal:** `smt-lib/non-incremental/UF/misc/set9.smt2`, `set16.smt2`, `set19.smt2` → `sat` (z3: `sat`/`sat`/timeout). All three are the same shape: uninterpreted `Set`/`Elem` sorts, `member`/`subset`/`seteq` observers, `union`/`intersection`/`difference` constructors, one ground assertion each.
**Current state:** all three answer `unknown` — set16 in **0 s**, set9 in ~1 s, set19 in ~10 s. The compound-closure chase that motivated the arc (62 s diverging, 4000-entry tables) is dead. Four of seven axioms **certify** on set16 (`seteq`-as-subsets, axiom 1, union, intersection). What remains is *one precise disagreement* between the nested checker's solver and the term-level walk.

## The one remaining question

The walk (`CompletionEval::run_recorded` over the raw substituted body) evaluates the **constructor axioms true at every odometer tuple**. The aux solver (`aux_refute`: `not body'[sk]` + Skolem restriction + distinctness + ite-var confinement) still returns **`Sat`** on q33 (union), q38 (intersection), q42 (difference), q57 (witness axiom), q20 (containment axiom). The aux is exploring a falsifying reading the walk cannot see.

**The next probe (start here):** minimize the aux goal at a q33 `Sat`:
1. Instrument `aux_refute` (print-only probes are all through the file already — copy the pattern) to dump the goal term `not body'[sk]`, the restriction clauses, the distinctness, and the ite-var confinements to a file when the verdict is `Sat`.
2. Solve that goal standalone (`z3` on the extracted SMT-LIB); the surviving model shows **which chain branch the aux prefers that the completed tables do not justify**.
3. Prime suspect: **stale constructor-table ground pins** — the ground solver's own assignments `union(b,a) ↦ a` etc., harvested into `function_interps` as entries that `compute_one` never overrides ("ground pins never override"), whose rows no longer match after a cardinality escalation re-derives the rows. The revision loop for *those* (the falsifier path emitting the defining-axiom instance so the ground solver re-solves the pin) is the mechanism the study has carried since the first landing — see "Why it still answers unknown" and the third-pass notes in the study.

If the minimized goal shows the aux legitimately exploiting *entry ordering* instead (two chain branches where the walk's first-match and the chain's outermost-first disagree), fix the ordering asymmetry: the walk's concrete lookup iterates `interp.entries` **first-match-wins**; the chain builder iterates `.rev()` making the **last** entry outermost. After the entry normalization (landed, `e44841ec`) same-point duplicates are deduped, so this should be consistent — but verify it on the minimized goal.

## What is landed (the full mechanism stack, in order)

All on `main`, all verified per landing (quant_fuzz 6 seeds × 150, parity 176/1/0 vs z3 4.16.0, full suites):

| commit | mechanism |
|---|---|
| `d49c8936` | **Constructor tables** (`mbqi/constructor_tables.rs`): quasi-macro extraction, semantic tables (row-matching), frozen table domains (Z3's cardinality semantics), semantic value normalization, row-determined fixpoint |
| `6e5ef76f` | **sat_certify saturation fix** (a quantifier is never ground) + the hint completion un-held |
| `b2de0bcc` | **Bounded-quantifier expansion** in the completed body (pointwise folds over frozen domains) |
| `f725362e` | **Stale-pin repair**: blocking disjunction over a fully-pinned falsifier's commitments, recording on the **raw** body |
| `7280f522` | **Table mode owns the whole problem**: sat_certify declines; every engine domain reads the frozen `table_domain` |
| `cc19759a` | **Aux solver's internal MBQI silenced** in table mode (the budget fire) |
| `27a41116` | **Targeted cardinality escalation** (`thaw_axes_only`): axes thaw, ranges stay frozen |
| `90619189` | **Aux merge exploit closed**: pairwise distinct over the restriction universe |
| `ceca2d31` | **`p => p` collapse** in the fold machine (the walk-vs-aux divergence's simplest instance) |
| `5a6bc16c` | **Entry-table semantic normalization**: entries rewritten through `semantic_value_of`, same-point duplicates collapsed |
| `68475bd5` | **The expansion is a completion choice**: the `Quant` frame flags `free_choice` in recording mode (closed a real false-`unsat` vector in the repair) |
| `37cc409a` | **Ite-abstraction confinement**: aux's `__nixie_ite_*` vars restricted to the frozen domain |

Key files: `nixie-solver/src/mbqi/constructor_tables.rs` (the tables), `model_checker.rs` (`CompletionEval`, `check`, `aux_refute`, the mining), `model_completion.rs` (the completion pipeline, `thaw_axes_only`, `semantic_value_of`), `integration/mod.rs` (the round loop, the repair emission, `emit_macro_defining_pins`), `sat_certify.rs`.

## Soundness rules this arc paid for (do not relearn them)

1. **A quantifier is never ground.** Nested binders in an eligibility check pass as "ground" premises and dodge at encode time → false `sat` via saturation (`6e5ef76f`).
2. **The recording walk must run on the raw body.** The completed body's *syntax* bakes completion choices in positions the walk never visits; "fully pinned" over it counts choices as pins → false `unsat` via the blocking clause (`f725362e`, re-derived the hard way).
3. **The expansion's domain is a completion choice.** Any falsifier whose falsity needed the domain restriction is not a function of its commitments (`68475bd5`).
4. **The completed structure's tables must agree with their own quotient.** Compound-keyed entries denote the same point as their semantic value; two values at one point is not an interpretation (`5a6bc16c`).
5. **Domain elements are pairwise distinct — tell the aux.** Otherwise it merges `a` with `b` and falsifies witness axioms at the degenerate point (`90619189`).
6. **Never emit a main-solver clause from commitments that include asserted facts** unless the falsity is genuinely a function of the commitments alone (rules 2–3 are the enforcement).

## Verification bar (every landing)

```bash
cargo build --all-features
cargo nextest run -p nixie-solver -p nixie-core --all-features --no-fail-fast
cargo clippy -p nixie-solver -p nixie-core --all-features --all-targets -- -D warnings
cargo fmt --all
./bench/z3_parity/run_parity.sh          # expect 176 Correct / 1 Inconclusive / 0 wrong (z3 4.16.0)
for s in 41 42 43 44 45 46; do python3 bench/differential/quant_fuzz.py target/release/nixie 150 $s; done   # all CLEAN
```
- The `twins` canary (content in the study; recreate as a file): must answer `unsat` (z3 agrees). It has caught two bugs within seconds.
- The heaviest convergence pin: `cargo nextest run -p nixie-solver --all-features -E 'test(scope_rebase_tests::re_running)'` — passes standalone in 139–159 s (fastest of the arc); under full-suite parallel load it can flake a timeout, and one concurrent agent's wisas regression (pre-existing, another arc) fails regardless.
- Set-family timing checks: `time ./target/release/nixie smt-lib/non-incremental/UF/misc/set{9,16,19}.smt2` — expect 0–15 s each, `unknown`.
- **Corpus**: `smt-lib/` is complete (270/270 sample paths). If missing, refill per `smt-lib/PROVENANCE.md`.

## Debug channels that exist (all print-only, follow the pattern)

- `NIXIE_DEBUG_MC` — model-checker decisions, body', aux verdicts, mined bindings
- `NIXIE_DEBUG_CT` — table extraction/computation/freezing, depth-tagged
- `NIXIE_DEBUG_QROUNDS` — the MBQI round loop
- The probes used this arc (re-add as needed, then **strip before landing** — a leftover once truncated a file): `[nontrue]` per-combo walk scan, `[skf-pin]` entry dumps, `[quant12]` expansion size, the aux falsifying-assignment dump, `[late-body']`.

## Repo conventions that bite

- **Never** `git stash` / `restore` / `checkout --` on the shared tree — multiple agents. Worktrees only (`git worktree add /tmp/wt-x -b branch main`), symlink `smt-lib` in, remove after landing.
- **main moves continuously** (5+ concurrent arcs). Land by: commit on your branch → `git merge main` in your worktree → rebuild + spot-verify (twins + quant_fuzz 60×1 seed) → from the shared tree when momentarily clean, `git merge --ff-only <branch>`. Expect several cycles; rebase-style merges of main into the branch keep ff possible.
- If the shared tree is dirty with *your own* content (an aborted ff), you may commit exactly those files yourself.
- Binaries: copy the release binary to `precompile/<full-or-short-sha>/` after landing; delete redundant merge-commit entries when cleaning.
- **Disk**: `/media/data` has run at 99% — budget builds, remove worktrees promptly, `git worktree prune`.
- Heuristic/path changes need a matched null (AGENTS.md); this arc's changes are interpretation-semantics fixes measured by before/after + the fuzzers, which is the recorded justification pattern in the studies.

## The negative results (do not retry blind)

In the study, each with its mechanism: the unconditional budget refunds (pin 400 s), the full thaw (re-stalls at higher cardinality), the unconditional aux-MBQI silence (loses wisas `unsat`), the completed-body recording walk (six false-`unsat`s), value normalization alone, the enum churn as a convergence driver. The held-back: the `thaw_table_domains` full-thaw hook (dead code, `MAX_TABLE_THAWS`); the hint's interaction with `sat_certify` saturation is fixed but the hint's convergence value beyond subset-completion is unmeasured.

## Adjacent arcs (don't collide)

- **Native sets theory** (`solver/set_theory/`): ground finite-set decision procedures — orthogonal to this UF-encoded family (they use `declare-sort Set`, not the built-in Set sort). The sets-arc agent also landed bags recently.
- **wisas/xs_8_13 regression**: owned by the arithmetic/simplex arc (handover exists in `docs/handovers/`).
- **FF/GB, CP-oracle, recfun, SAT-core perf agents**: active; their files (`nixie-theories/ff*`, `nixie-sat/`, `nixie-cli/`) are frequently dirty — check `git status` before ff.

## If the minimized goal closes the family

Land it, then: add the three files as named regressions (`set16_family_answers_sat` — they currently honestly answer `unknown`; the never-`unsat`/never-`sat` pins for set16 already exist in `nixie-solver/tests/uflra_quantifier_regressions.rs`), re-run the full battery, and write the closing study section. Then the natural continuations, in order of value: (1) the matched-null measurement for the constructor-tables unit (AGENTS.md requirement, still outstanding), (2) the unsat-forcing quant_fuzz generator family (the generator skews sat-heavy), (3) measure the hint's value on other definitional-predicate families.
