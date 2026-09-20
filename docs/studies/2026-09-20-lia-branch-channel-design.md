# The CDCL-visible LIA branch channel — implementation reconnaissance and design

**Date:** 2026-09-20 (third continuation; the map's item 1).
**Status:** design only — no code.  This is the implementing session's
entry point: every mechanism it needs already exists in the tree, named
below with file/line anchors from main `71ea492d`.

## Why this is the item that owns the LIA class

The standing evidence chain (parent studies): `problem__022` burns its
full 20 000-node internal B&B budget inside ONE theory check (~80 k
pivots, ~500 M gcd calls, 73 % of wall) where z3-old does the whole
instance in 44 pivots + **4 CDCL-visible branches** and z3-6 in 2 patches.
The internal tree cannot learn: every node re-feasibilizes blind, and the
`Unknown` that ends it ends the whole search.  A branch that CDCL can see
gives the split literals to the SAT core, which learns from each side's
theory conflicts — the pruning the internal B&B structurally lacks.

## The enablers that already exist

1. **Mid-search clause addition from the theory side** — the MBQI
   blocking loop (`solver/mod.rs`, the "Block `atom = value`" site:
   `self.sat.add_clause(lits)` on candidate models) and the
   distinct-guard clause site (`trail.push(TrailOp::
   DistinctGuardClauseAdded …)` + `add_clause`).  `add_clause` handles
   the internal backtracking-to-consistency; the trail op keeps it
   undoable.
2. **Valid-disjunction assertion + re-solve** — `int_case_split.rs`
   already asserts theorems of the form `(or (= t lo) … (= t hi))` and
   re-solves.  Its shape (reset-and-re-solve, capped rounds) is a
   *narrow non-convexity guard* (UF arguments, level-0 bounds, range
   ≤ 8) — NOT this feature, but it proves the atom-creation and
   disjunction-assertion plumbing.
3. **Branch bounds with reasons** — `bnb_search`'s `take_branch`
   (`set_upper_exact`/`set_lower_exact` with `BRANCH_REASON`) already
   drives the simplex per branch; what changes is who owns the loop.

## The design

At `lia_branch_and_bound`'s fractional point (after `patch_int_columns`
and the bounded cut rounds), for the best fractional integer variable
`v` with `floor(v) = k`:

1. Emit the **valid clause** `(v ≤ k) ∨ (v ≥ k+1)` — valid over ℤ
   unconditionally (sound by construction, no model guard needed).
2. Return a decline that **does not end the search**: the blocker today
   is that `TheoryResult::Unknown` at final check sets
   `resource_exhausted` (`theory_manager.rs`, the
   `TheoryCheckResult::Unknown` arm) and the solver answers `unknown`.
   Two options:
   - **(a) a new `TheoryResult::Branch(Vec<(TermId, TermId)>)`**
     (left/right atom pairs); the manager internalizes the atoms,
     asserts the disjunction clause via the MBQI-style `add_clause`
     path, and returns "keep searching" — or
   - **(b) reuse `Unknown` + a manager-side pending-lemma queue** the
     final-check drains before declaring exhaustion.
   (a) is the honest interface; (b) touches less surface.
3. **Dedup**: a seen-set keyed `(v, k)` — re-emitting the same split per
   check is the infinite-loop hazard; the trail/SAT side already
   dedups clauses, but the THEORY must stop proposing once emitted.
4. **Fallback**: keep a small-node internal B&B (the dive +
   `MAX_FREE_SPLITS` paths) for leaf cases and wide values with no
   `i64`-representable split bound — the clause route needs
   representable bounds; `wide_floor_ceil_exact` is the boundary case.
5. **Explanation wiring**: each side's theory conflict must explain
   through the branch atom's reasons so CDCL learns the right clause —
   the existing `note_bnb_conflict_reasons` machinery transfers if the
   branch bound's reason is the ATOM (not `BRANCH_REASON`), which is
   exactly what asserting the atoms through the standard
   `assert_true` path gives.

## Risks named up front

- Mid-search atom creation must not race the incrementality contracts
  (`term_to_var`, Tseitin memos — the case-split round's reset-and-
  re-solve sidesteps this; the mid-search variant may need the
  encode-at-root discipline the distinct-guard site uses).
- The 0-conflict `nec-smt` unknown class interacts: those never reach
  a theory check (encoding-depth refuse) — unaffected.
- Heuristic risk (which `v` to split): start with the existing
  `find_fractional_int_var` (smallest range); a tuned rule needs the
  matched-null discipline.

## Probes the implementing session starts from

`problem__022` / `problem__011` (CAV), `RC-13`/`RF-14` (SMPT sat-side),
the mirror (`docs/studies/assets/ddm_mirror.py`), and the standing
table.  Success bar: QF_LIA 32→40+/60 without a single lost cell or
disagreement.
