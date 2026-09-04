# Freeze-set collapse: destructive preprocessing under a real theory (Priority-5 enabling slice) (2026-08-25)

## The slice

`2026-08-cdclt-gates-audit.md` identified the freeze set as the
precondition for any SMT pre-search collapse: BVE/ELS/purelit skip
frozen variables, exactly like assumption freezing.  A key discovery
shaped the design: **the SMT encoder maps every term to a SAT var**
(And/Or gates included — `get_or_create_var(term)` throughout), so
"freeze all term-mapped vars" would freeze everything and leave the
passes nothing to do.  The *operational* freeze set is
**`var_to_constraint`** — exactly the atoms the theory manager replays
to theories via `on_assignment`.  Boolean-structure gate vars (And/Or/
ite-condition encodings) carry no constraint entry and are what the
passes may collapse.

## Mechanism (landed)

- `Solver::freeze_theory_vars(vars)` — inserts into `frozen_vars` and
  sets `theory_vars_frozen`.
- `destructive_preprocessing_safe() = !real_theory_attached ||
  theory_vars_frozen` replaces the raw `!real_theory_attached` gates in
  `elimination_allowed`, inprocess's ELS gate, and inprocess's
  pure-literal gate.
- Per-pass skips: `mark_elim_one` refuses frozen vars; the ELS SCC fold
  leaves any class containing a frozen var unfolded (folding would
  stop the frozen atom from reaching the theory — the on_assignment
  desync); pure-literal's `assigned` exclusion treats frozen as
  assigned.  Frozen entries are retained forever (conservative
  direction: the set only ever shrinks what the passes may do).
- SMT layer: `NIXIE_FREEZE_COLLAPSE=1` enables `enable_bve` +
  `enable_equiv_substitution` in the embedded core and freezes the
  `var_to_constraint` keys at every check entry (idempotent, covers
  atoms asserted since the previous check).
- Model reconstruction rides the existing machinery: BVE's `bve_def`
  witness replay and ELS's representative extension already fill
  eliminated/folded vars in `save_model`, and the whole-assertion
  model validation gates every `Sat` regardless.

## Measurement (60-file QF_LIA/QF_UF/QF_UFIDL/QF_IDL sample, 20 s)

| | collapse ON | OFF |
|---|---|---|
| verdicts vs z3 (ON arm) | **0 wrong** | — |
| on/off verdict mismatches | — | **0** |
| solved | 41 | 41 |
| geomean, >2 s files (5) | 0.914 | 1 |

Single-seed screening: one strong win (`PO4-6-PO4` 18.8 → 12.3 s),
rest ~tied; the 1.14 all-file geomean is sub-second noise.

## Amendment (same day): ENABLED BY DEFAULT under the relaxed enablement rule

Direction received: the multi-seed PMU bar is for *improvement claims*,
not for enabling a sound mechanism — "if it logically makes sense and
doesn't have obvious regress, it shall be enabled".  Codified as the
**enablement rule** in `docs/BENCHMARKING.md` §3.  Applied here:

| gate | result (default-on binary) |
|---|---|
| differential vs z3, 270 files | **solved 162 (off-arm: 159), 0 disagreements** |
| paired per-file diff | **+3 gained, 0 lost** (`sorted_list_insert_noalloc9`, `xs-20-12-3-1-5-2`, `hash_sat_08_03`) |
| par2 | 2267 vs 2313 (off) |
| canaries | cxs-bp `unsat`, 25s `unsat`, wisas `unsat`, sorted_list `sat` |
| Z3 parity | 167/0/1 identical |
| full bar | 10 102 tests, clippy/fmt/doc |

Default-on strictly dominates on this corpus.  `NIXIE_FREEZE_COLLAPSE=0`
remains the A/B off-switch.  The strict statistical program still
applies to any *quantified* claim about the win.

## Soundness argument

Every destructive transform remains excluded for exactly the vars the
audit named load-bearing: theory-mapped atoms (frozen), assumption
vars, multi-scope assertion levels, proof/LRAT tracing.  What changes
is only that non-frozen (never theory-observed) Boolean-structure vars
may now be eliminated/folded under a real theory — their assignments
never surface to `on_assignment`, and their model values are
reconstructed or structurally evaluated.

## Go/no-go (from the established-candidates spec)

The spec's full go/no-go asks for BMC/symbolic-execution *traces* with
push/pop trees — not yet exercised (`assertion_levels.len() <= 1`
still excludes incremental scopes from every destructive pass, so
traces are unchanged-by-construction today).  That is the recorded
next step for the calculus proper: versioned transformations with
per-scope rollback, then replay.  This slice is the prerequisite the
audit named, landed with the measurement surface to evaluate it.
