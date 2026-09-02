# LRAT as the default path: elimination-under-proof, and two proof bugs found (2026-09-02)

Directive context: LRAT (certified mode) is the default production path
and the main optimization target. This study opens that front.

## What the certified path actually costs (measured)

`oxiz --certified-mode` on propositional SMT-LIB (SAT-corpus files
re-encoded), pinned core:

| file | uncertified | certified | SAT preset (stats_solve) |
|---|---|---|---|
| crn_11_99_u | 1.7 s | 3.1 s | ~1 s |
| 6s167-opt | 117 s | 140 s | ~3.5 s |
| mrpp_4x4 | — | 248 s | ~8.7 s |

Profile of the certified run (6s167): `propagate` 50.4%, **theory glue
≈11% on a purely propositional input** (EUF `pop` 6.5%, congruence
propagate 3.2%, TheoryManager backtrack 1.5%), analysis ~9%, and
`lrat_check` only 1.2% — the checker is not the cost. Two structural
deficits: (a) the SMT bridge reports `is_real_theory() == true`
unconditionally, so EUF attaches to pure-Boolean inputs (the 11% glue)
and `destructive_preprocessing_safe` forces the freeze-set path; (b) the
freeze set covers every Tseitin var for propositional inputs, so BVE is
inert even where configured on.

## Landed: BVE under an attached proof (pre-search fixpoint only)

`elimination_allowed` no longer refuses proofs. Emission scheme, all
checker-validated (`lrat_file --lrat` + `check_lrat`, crn verified in
every arm):

* **Resolvent additions** carry the resolving pair as the RUP chain —
  negating a resolvent falsifies both parents except v/¬v, propagation
  derives v from C and ¬v from D, conflict. Parents retire after their
  resolvents are added, so chains verify at addition time.
* **Deletions** (retired originals, satisfied clauses, BVE parent
  removal) are emitted as deletion lines — justification-free in LRAT.
* **In-place strengthens** (`elim_shrink_clause`) reuse
  `proof_strengthen_clause`, restricted to drops whose literals are
  falsified by proof-backed units (the LRAT unit table), so the
  checker's propagation derives the shorter clause.
* **Unit/empty resolvents abort the pivot** under proofs (their
  justifications need elimination-local provenance — the follow-up
  item), and `subsume_round`'s strengthen arm is skipped under proofs
  (its chain would need the subsumer id, which the path does not
  thread). Both strictly weaker, never unprovable.
* **Mid-search scheduled elimination stays refused under proofs** — see
  the wrong-SAT finding below.

## Finding 1 (pre-existing, NOT from this change): default-path LRAT proofs are unverifiable on some inputs

`6s167-opt` **base config, no flags, LRAT attached**: verdict correct,
`check_lrat` rejects — derived-clause hint chains contain **0 ids**.
Instrumented hunt (all temporary, reverted): the zeros enter through
`analyze`'s level-0 unit collection (`ZERO-UNIT-CHAIN`): level-0
antecedent literals with **no recorded unit id**, i.e. the
"every level-0 literal is a unit with an id" invariant that
`flush_level0_unit` + the chain builders rely on is violated by some
assignment path. Narrowed: not CNF units, not the flush path itself, not
analysis reasons (`ZERO-ANTECEDENT` never fired), persists with
`--bare` (chrono/lucky/stabilize/vmtf/reuse all off), and
probing/ELS/BVE/inprocess/pure-literal are all proof- or config-gated
off in that arm. `proof_learn_clause` already carries a
`debug_assert!(!chain.contains(&0))` — **a debug-build run will catch
the culprit with a backtrace**; that is the fastest next step.

## Finding 2 (exposed by this change, gated): mid-search elimination + ELS-latch interaction produced a wrong SAT

With the original full relaxation, `lrat_file --bve --els` on crn and
6s167 returned **SATISFIABLE on UNSAT formulas** (kissat/z3 confirm
UNSAT; `--bve` alone correct; `--els` alone correct; no-proof arms
correct). The ELS pass itself never executes under proofs (own gate);
its flag's residual effect is the scheduled one-shot latch + a root
backtrack at the shared `lim_elim` boundary — and the false verdict
lives in the interaction with **mid-search scheduled elimination**,
newly enabled by the relaxation. Gated: `eliminating()` refuses under
proofs until root-caused. Reproducer (pre-gate binary):
`lrat_file crn_11_99_u.cnf --lrat /tmp/x --bve --els` → SATISFIABLE.

## Measurement knobs added

`lrat_file`: `--bve` (BVE under proof), `--els` (ELS), `--bare`,
`OXIZ_DIAG=1` (pass counters). These stay for reproducing both findings.

## Next (ranked)

1. **Root-cause the zero-unit invariant break** (Finding 1) — debug
   build + the existing assert; this makes default-path LRAT proofs
   verifiable, which is table stakes for the certified path.
2. Root-cause the mid-search elim/ELS wrong-SAT (Finding 2) and
   re-enable scheduled elimination under proofs.
3. Unit-resolvent provenance (BVE units as derived units with
   parent-pair chains) to recover full-strength BVE under proofs.
4. `is_real_theory` content-based predicate (pure-Boolean inputs should
   not attach EUF: kills the 11% glue and un-gates BVE for them) —
   needs its own soundness note (the freeze-set study's rigor).
5. Re-measure the certified path after 1–4.
