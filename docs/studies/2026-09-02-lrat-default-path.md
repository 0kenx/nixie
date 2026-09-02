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


## Addendum (same day, later): both findings root-caused and FIXED

### Finding 1 root cause: three level-0 assignment paths bypassed the unit flush

The "every level-0 literal is a unit with an id" invariant is maintained by
`flush_level0_unit`, called only from `propagate()`'s two assignment sites.
Three assignment paths assign level-0 **propagations** outside `propagate()`:

1. `assert_learned_clause` (`learn.rs`): a learned clause whose falsified
   siblings all sit at level 0 installs the asserting literal at level 0 —
   caught by the debug-assertions build (the existing
   `debug_assert!(!chain.contains(&0))` in `proof_learn_clause` fired with a
   backtrace naming the site).
2. `add_clause`'s `ForceUnitAtLevelZero` (binary + 3+-literal branches):
   parse-time effective-unit forcing (the ZERO-UNIT diagnostics showed trail
   positions 3–80 with mid-parse clause reasons).

**Fix**: flush at the `assert_learned_clause` install (mid-search, safe);
the two parse-time sites **defer** their flushes to solve entry — emitting
derived units mid-parse would allocate derived ids *inside the original
prefix* (which must stay contiguous 1..K in file order), desynchronizing
every later original's id (found the hard way: chains referencing valid
hints that mapped to the wrong clauses).

Verified: base-config LRAT proofs on 6s167 (the original failure), crn,
mrpp, FmlaEquivChain all pass `check_lrat`. (noL is SAT — its proof has no
empty clause by construction; the checker expects UNSAT proofs.)

### Finding 2 root cause: refused self-subsumption shrinks left resolution-closure holes (FALSE SAT — fixed in ALL configs)

Bisection (each alone fixed the wrong verdict → both were load-bearing only
together): the ELS flag's residual effect (one root backtrack at the shared
`lim_elim` boundary) only shifted *when* the newly-enabled mid-search
elimination ran; the corruption was in the elimination itself. Model
validation against the raw CNF (independent Python check) named violated
originals; the live-DB check showed every live clause satisfied — pure
**model-reconstruction failure**. Per-pivot resolution logging on var 6
showed its elimination complete — the hole was elsewhere in the chain.

The bug: `elim_resolve_clauses`' self-subsumption path returns `Skip` —
valid ONLY because the in-place shrink *substitutes* for the pair's
resolvent. The shrink can be **refused** (proof guard, or the pre-existing
live-reason guard that also fires in default no-proof runs) — and the old
code returned `Skip` anyway: the pair contributed neither the shrink nor a
resolvent, the resolution closure grew holes, and `save_model`'s BVE
reconstruction (provably sound only over a complete closure) extended a
partial assignment that violated retired originals.

**Fix**: `elim_shrink_clause` now reports whether it shrank; a refused
shrink falls through to adding the ordinary resolvent (exactly the
unoptimized form of the shrink). Both wrong-SAT repros (weakened-elim no-
proof, and proof+midschedule) now return UNSAT with verified proofs where
applicable. **This also closes a latent false-SAT in default no-proof
configurations** whenever the live-reason guard refuses a self-subsumption
shrink — the guard predates the proof work.

### Still gated: mid-search elimination under proofs

With the closure hole fixed, mid-search elimination under proofs now gives
correct *verdicts*, but its proof emissions can reference parent clauses
that a subsumption round (running inside `eliminate_phase` under proofs)
has already deleted — "hint is not unit" (crn line 2004). The gate stays;
the fix is subsumption-aware chain repair (use the subsumer in the chain).
