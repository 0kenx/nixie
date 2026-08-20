# Item 3 audit: CDCL(T) inprocessing gates + branching decision re-validation

Date: 2026-08-19
Scope: the two bounded, high-certainty pieces of the handover's Item 3 —
(1) re-validate the `focused_vmtf = false` decision against the *post*
walk-glue/shrink search core, and (2) the inprocessing-gate audit
(load-bearing vs over-conservative).  The theory-conflict 1-UIP comparison
against Z3's `smt_theory.h` remains open (listed at the bottom).

## 1. `focused_vmtf = false` re-validated on QF_UF

The 91:45 measurement predates the walk-glue restart-EMA and block-UIP
shrinking landings, which changed the search core enough to re-check on the
benchmark class the decision was made for (not CNF).  A 63-file QF_UF sample
(60 `QG-classification` + `TypeSafe`, seed-7 draw, 60 s cap, paired
instructions via `perf stat`, arms toggled by the new debug knob
`OXIZ_SAT_VMTF_FOCUS=1`):

- **0 verdict disagreements** between arms;
- paired vsids/vmtf instructions geomean **0.768** (VSIDS, the current
  default, ~1.3× faster in aggregate; >1 would have favored VMTF);
- wildly bimodal per file: VMTF wins up to 67× (`iso_brn813/872`), VSIDS up
  to ~100× (`iso_brn727/150`) — *within the same family*, i.e. classic
  trajectory divergence, not a family property.

Single seed, screening label — but the direction matches the original
measurement and the decision stands: **`focused_vmtf = false` stays.**
`OXIZ_SAT_VMTF_FOCUS=1` is kept as a documented debug knob so the next
re-validation needs no rebuild.

## 2. Inprocessing-gate audit (gate → verdict)

The SMT layer never enables these passes today, so the gates matter for the
*future* ability to port Item 2's pre-search-collapse value into CDCL(T).

| gate | where | verdict |
|---|---|---|
| `proof.is_some()` / `lrat` | BVE, inprocess, ELS | **load-bearing, not conservative**: the passes cannot emit justified proof lines (in-place rewrites, deletions without derivation chains). Relaxing = implementing proof emission, not removing a check. |
| `assertion_levels.len() <= 1` | BVE, purelit | **load-bearing**: `pop` re-exposes eliminated/folded variables with no sound way to honor later clauses (`add_clause` on a BVE-eliminated var is already `fatal_error`). Incremental scopes must stay excluded. |
| `assumptions_active` | BVE | **load-bearing**: an eliminated variable can no longer be assumed (cadical freezes assumed vars for the same reason). |
| `real_theory_attached` (purelit) | inprocess | **load-bearing**: `save_model` pins the pure polarity, a value the theory never blessed — a real-theory trail can legitimately force the opposite. |
| `real_theory_attached` (ELS) | inprocess + pre-search | **load-bearing**: folding `a ≡ b` stops the folded variable's atom from ever reaching the theory (`on_assignment` desync — the pr26 failure class). |
| `real_theory_attached` (BVE, via `elimination_allowed`) | eliminate | **load-bearing, same class** + the SMT layer's `term_to_var`/`var_to_term` maps would dangle for eliminated atoms. |
| *no* `real_theory` gate on subsume/vivify/transred | inprocess | **correctly ungated**: all three only strengthen/delete via clauses entailed by the *combined* theory∪Boolean semantics (theory lemmas enter as learned clauses; subsuming an original by an entailed lemma preserves the combined problem). Verified by reading; no CDCL(T) measurement yet. |

**The enabling path for SMT pre-search collapse** (not built here): a
*freeze set* — the SMT layer passes its term-mapped variables as frozen
before invoking the pre-search passes, and BVE/ELS/purelit skip frozen
variables, exactly like `assumptions_active` freezing today.  That is the
precondition; after it exists, the value case must be measured on
QF_LIA/QF_UF (Item 2 found the value is entirely in the pre-search collapse,
not the schedule).

## 3. Still open (next session)

- Theory-conflict 1-UIP reason handling vs Z3 (`smt_theory.h` lazy
  explanation / theory-propagation reasons) — the handover's third thread;
  `cdclt_propagation_fixpoint_soundness.rs` and the pr28/pr29 regression
  files are the required reading.
- The freeze-set mechanism + QF_LIA/QF_UF measurement, per above.


## 4. Theory-conflict 1-UIP audit vs Z3 (follow-up, same date)

Completed the remaining Item-3 thread on both axes:

**Code read** (`analyze_theory_conflict` vs `smt_theory.h` /
`smt_context.cpp` usage patterns): every Z3-mirrored property is present —
all-false validation with the Undef→asserting-lemma reroute (Z3: a lemma
with an open literal is a propagation, not a conflict); the genuine
conflict-level anchor (`max level of conflict literals`, not
`decision_level()` — the level guard landed this release cycle);
level-0-literal skipping; the chronological-backtracking pivot guard
(`analyze_scan_pivot`, Z3's `lvl(c_var) != m_conflict_lvl` skip); and lazy
theory-propagation resolution through `theory_reason_tail` (Z3's
`th_propagate` records, `explain` consulted only on resolution).

One deliberate conservativeness verified: **block-UIP shrinking never
resolves through a theory reason** — `shrink_block` requires
`Reason::Propagation` (bails to plain minimization otherwise) and
`minimize_literal_plain` likewise; `Reason::Theory` lazy tails are never
walked by the shrink machinery, so theory-justified literals survive
shrinking by construction.  Shrink *is* active on the CDCL(T) path
(`SatConfig::default()`, landed default).

**Differential evidence**: 155-file stratified sweep over
`smt-lib/non-incremental/{QF_LIA,QF_UF,QF_IDL,QF_UFIDL,QF_UFLIA}`
(seed-11, 60 s OxiZ / 30 s Z3, verdict cross-check; `unknown`/timeout of
either side not counted): **88 verdicts, 0 disagreements** with Z3 5.0.0
(the parity-suite pin is 4.15.4; for ground-logics verdict comparison this
is immaterial, and any future disagreement gets minimized + certified-mode
re-validated before analysis anyway).

Verdict: the theory-conflict 1-UIP path is audited clean.  Remaining
Item-3 residue is only the *enabling* work (freeze set + measurement)
described in §2 — no known soundness gap.
