# Handoff: the MBQI persistent-model rewrite — the harvest architecture's verdict is in, the next design is z3's

**Date:** 2026-09-18
**Arc:** `docs/studies/2026-09-14-model-finder-constructor-tables.md`, follow-ups
sixteenth–eighteenth (read them first — this handoff is the map, the study
is the territory).  Companion: `docs/handovers/2026-09-16-model-finder-endgame.md`
(closed — the set family answers `sat`).
**Goal:** rewrite the completed-model layer as a **persistent structure** —
z3's proto-model-as-search-object architecture — replacing the
harvest-rebuild cycle that the eighteenth follow-up proved cannot carry
honest semantics.

## Where things stand (all landed on main)

- **The set family is closed**: set16 0.1 s, set9 ~8 s, set19 ~14 s —
  z3 4.16.0 *times out* on set19.  Pins: `set{9,16,19}_family_answers_sat`
  in `nixie-solver/tests/uflra_quantifier_regressions.rs` (set19 has a
  nextest slow-timeout override).
- **The mint is budgeted**: `MINT_BUDGET_PER_ROUND = 1`, post-walk,
  odometer-prefix; matched null `NIXIE_MINT_NULL=<seed>` ships in-tree;
  treatment/null 0.83–0.91 (conflicts, the deterministic counter).
  `NIXIE_DEBUG_QROUNDS` prints a `[qround-stats]` cumulative-aux-conflicts
  line — use it, never wall-clock, as the primary metric.
- **The unsat-forcing fuzz family is landed**:
  `python3 bench/differential/quant_fuzz.py <nixie> N SEED unsat` — six
  generators (chain/skolem/pigeonhole/card/cycle/extensional), goals
  **unsat by construction** (oracle needs no comparator; z3 is the
  generator's cross-check).  Standing on main: zero false-sats; the
  completeness gaps are **pigeonhole ~20/30 unknown** and **extensional
  ~6/24 unknown**.  These are the next targets and one-invocation
  reproducers.

## The verdict chain (why a rewrite, not a tune)

1. **Sixteenth**: the export of ground-model equality values for
   S-valued applications (the pigeonhole gap's root: the model readback
   never records them, so unowned S→S functions harvest empty tables and
   complete to a constant `else`).  Global export → **false `sat`s** on
   the extensional family, via a fully decoded chain: pins on
   table-owned compounds → entry normalization re-keys them onto minted
   elements → minted rows mutate post-mint → row-canonical names lie →
   the (real) duplicate-domain-push bug bloats the structure → chains
   bury the ground pins the certification reads → the aux certifies a
   corrupted body'.  Ownership-gated export → sound but inert.
2. **Seventeenth**: the row memory built; both pollution channels found
   and fixed — **(a) the polarity override** (the loop's own falsifier
   lemmas commit atoms *at minted elements*; the completion evaluator's
   whole-term assignment lookup answers before any entry) and **(b) the
   same-key twin** (the harvest converts those polarities into entries
   whose args coincide with the mint's own; a key-based retain keeps
   both — purge by touch, then re-inject the remembered rows).  With
   both fixed the mint's names become honest (the `!bits` suffix
   matches the element's actual row — verified in dumps).
3. **Eighteenth**: with honest rows and **10× the global conflict
   budget** (50k→500k) the family still answers `unknown` — 99 rounds,
   constructor checks `Sat` 59–73× each.  The ground rows churn every
   round; each churn mints new target rows; each Elem-domain growth
   re-names old ones through the row-point fingerprint; the closure
   never fixpoints.  The landed (dishonest) build converges *because*
   vanished rows collapse to a stable all-false core.

**The architectural conclusion**: honest semantics require row
stability, and a completed model re-derived from a freshly-re-modelled
ground solver every round cannot provide it — nothing makes the
falsifier-driven refinement monotone.  z3 converges because its model
IS the search object: one persistent structure, repaired in place.

## The rewrite design (what ports, what changes)

**Ports directly** (all decoded, all in the study):
- the **row algebra** (`semantic_value_of`, the row-determined fixpoint,
  the quasi-macro/constructor extraction, `constructor_tables.rs`);
- the **mint** with row-canonical names — keep the
  sorted-points+FNV-fingerprint form (it survives axis-domain growth);
- the **pollution invariants** as structure rules: minted points speak
  only through the structure's own rows, never through harvested
  polarities or their twin entries;
- the **freeze/cardinality semantics** (`frozen_table_domains`,
  `thaw_axes_only`);
- the **assertion gate** (validate quantifier-free assertions against
  the completed structure before printing `sat` — built and sound in
  the sixteenth session, held back with the revert; it closes the
  completed-vs-asserted divergence class independent of the rewrite).

**Changes**: the `CompletedModel` stops being rebuilt per round from
`partial_model`.  It lives on the integration (or completer), survives
across rounds, and each round only *applies* the falsifier instances'
effects: the ground solver stays the lemma engine (its instances remain
sound consequences), but the structure's rows/domains/tables change
only through explicit repair steps (mint, row pin from a falsifier,
freeze growth) — never wholesale re-harvest.  The signature/veto/memo
machinery keys on the structure's version, not a content hash.

**Validation per step** (non-negotiable, in this order): the three
family pins stay `sat`; the unsat-forcing family stays CLEAN (zero
false-sats — it is the fastest soundness canary this arc has had);
quant_fuzz {41..46}×150 random + {51..54}×150 unsat; parity 176/1/0;
the full battery from AGENTS.md before any landing.

## The two fuzz gaps (targets after the rewrite's skeleton)

- **pigeonhole ~20/30**: needs values for unowned S-valued
  applications.  The mapped route: export at the *theory layer* (EUF
  `find()` representatives into the model readback), gated on table
  ownership (unowned only).  The Eq-atom-harvest route is a documented
  failure — do not retry it.
- **extensional ~6/24**: the model finder on the refutation side;
  expected to move with the rewrite (the completed structure must
  genuinely refute the membership collision).

## Held-back code: where it actually is

**Not in git.**  The seventeenth/eighteenth solver changes (row memory,
purges, dedup, refund) were reverted uncommitted and the branches were
deleted — the studies' "in this worktree's history" notes predate the
cleanup.  Every piece is *completely specified* in the study sections
(mechanism, placement, measured effect); re-derive from the text.  The
seventeenth's two pollution channels and the sixteenth's assertion gate
are the pieces worth re-building verbatim.

## Negative results (do not retry blind)

Each with its mechanism in the study: the Eq-value export (both
variants); honest rows + budgeted mint on the harvest architecture (10×
budget, no convergence — the verdict); mint budget > 1 (B=4 blows up
set19's conflicts); eager/in-walk minting (odomoter extension covers
`(fresh, fresh)` tuples against in-flux rows); sticky-miss minting (the
seeded null beat it ~8.5×); the unconditional budget refunds; the full
thaw; the unconditional aux-MBQI silence.

## Repo conventions that bite (unchanged, plus this arc's additions)

- **Never** `git stash`/`restore`/`checkout --` on the shared tree.
  Worktrees only; land via `git push . HEAD:main` from your worktree
  (`receive.denyCurrentBranch=updateInstead` is now configured in the
  shared repo — it refuses rather than clobbers; expect several
  merge-and-retry cycles, main moves continuously).
- **Disk**: root and `/media/data` both run near-full; build in one
  profile at a time, delete `target/debug` between phases, symlink the
  corpora (`smt-lib`, `bench`, `precompile`, `satcomp2024/5`, `satlib`)
  into worktrees — a missing corpus makes tests fail *environmentally*
  (this cost two false alarms this arc).
- Binaries to `precompile/<sha>/` after landing; clean your worktrees
  and branches when idle.
- Heuristic changes need matched nulls (AGENTS.md); interpretation
  fixes ride before/after + the fuzzers (the arc's recorded pattern).

## Adjacent arcs (don't collide)

SAT perf (XOR-congruence just landed, standing table re-run pending),
arithmetic items (simplex territory, active), FF/GB, CP-oracle, bags
(`nixie-sat`/`nixie-theories` files frequently dirty — check
`git status` before any ff).  The release-profile workspace suite has a
known-clean state as of `77f66489` — keep a release run in the rotation.

## If the rewrite closes the gaps

Land, then in order of value: (1) the pigeonhole/extensional gap
closures as named regressions; (2) the assertion gate (if not already
in); (3) re-run the SAT standing table vs kissat (it predates the XOR
landing); (4) a standing SMT-side perf benchmark vs z3 (QF_LIA/QF_BV
slices, tick counters — the parity suite's wall columns are
harness-contaminated and mean nothing); (5) the matched-null formality
for the constructor-tables unit.
