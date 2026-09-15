# Handover: `wisas_xs_8_13` unsat→unknown regression (2026-09-15)

**Audience:** the round-13 CSR investigation (nixie-sat `watched.rs`) and the
model-finder/mbqi owner. Deterministic **incompleteness** regression (honest
`unknown`, never a wrong verdict), reproducible in 171 ms, load-independent.

## Symptom

```bash
nixie nixie-solver/tests/fixtures/wisas_xs_8_13.smt2   # -> unknown (z3: unsat)
cargo nextest run -p nixie-solver --test int_case_split_determinism_regressions
   # wisas_xs_8_13_is_unsat                FAIL
   # wisas_xs_8_13_verdict_is_stable_...   FAIL (same verdict, still not Unsat)
```

Failing on `main` today; the guards pin the *z3-certified* `unsat`. Verdict is
deterministic per binary (6× repeats, load ~19 machine: identical), so this is
NOT the historical wall-clock disease the test file documents — it is a
commit regression.

## Bisect (via the precompile binary cache — no rebuilds)

181 cached binaries swept (`precompile/cd544511/benchmark/wisas_verdict_sweep.txt`).

* **First bad: `2fa7d9a2` "Merge branch 'main' into mfinder" (2026-09-15).**
* Both parents verified good by direct binary runs:
  * `d1dc7f0d` (main side: arith wide-value + finite-set AST + sat round-13) → `unsat`, clean.
  * `47888de7` (mfinder tip) = `d49c8936` (mbqi constructor tables) + docs-only
    diff → `unsat` via `precompile/d49c8936/nixie`.
* The merge's `nixie-sat/` content is **byte-identical to the good parent's**
  (`git diff d1dc7f0d 2fa7d9a2 -- nixie-sat/` is empty) — the SAT-core code
  did not change; only the solver-side content (mbqi/ematching/mod.rs hunks)
  did, which perturbs the term/clause data layout reaching the SAT core.

## Probes (all on `precompile/2fa7d9a2/nixie`, the first-bad build)

| probe | verdict | canary |
|---|---|---|
| plain run | `unknown` | `[csr-shadow] scan precondition violated at literal code 889: combined 1 vs vec 0 — mirror suspended` |
| suspension-hunk reverted (9-line `mod.rs` delta of the merge) | `unknown` (unchanged) | fires | 
| `NIXIE_CSR_SCAN=1` (swapped scan: CSR-primary, Vec mirrored) | **`unsat`** | silent |
| `NIXIE_CSR_SHADOW=1` / `=0` / `NIXIE_CSR_READ=1` | `unknown` | fires |

Search signatures at the merge build:

| | conflicts | restarts | decisions | propagations |
|---|---|---|---|---|
| default scan (`unknown`) | 1184 (aborted) | 41 | 79 227 | 105 255 |
| `NIXIE_CSR_SCAN=1` (`unsat`) | 6620 (refuted) | 814 | 213 042 | 887 656 |

## Reading

* The default **Vec-primary watch-list scan is the wrong path on this
  instance**: the CSR mirror says literal 889 has 1 watcher while the live
  `Vec` has 0 — a watcher was lost Vec-side (or never written), so scanning
  the `Vec` skips a clause, the search's propagation stream is silently
  curtailed, it dies at 1 184 conflicts, the int-case-split refinement cannot
  close, and `check` honestly returns `unknown`.  Scanning the CSR instead
  traverses the correct watcher set and refutes the instance.
* This is the exact divergence class the round-13 study line is hunting
  ("add's `Vec` write shown load-bearing"; `end_scan` frame reset). The
  instance is a fast, deterministic reproducer with a **localized** first
  divergence (literal 889, `combined 1 vs vec 0`).
* The canary prints even with `NIXIE_CSR_SHADOW=0`: mirror *maintenance*
  runs unconditionally in this build; only the swapped-scan/reader consumers
  are env-gated.
* **Current `main` has evolved**: both the default and `NIXIE_CSR_SCAN=1`
  return `unknown` there (canary silent). Something after the merge
  (relations/QF_UFFF/sat continuations) moved the surface again. The merge
  commit remains the clean isolation point — start there, then walk forward
  commit-by-commit with the two test guards as the oracle.

## Artifacts

* Reproducer fixture: `nixie-solver/tests/fixtures/wisas_xs_8_13.smt2` (QF_UFLIA, z3-certified `unsat`).
* Cached binaries: `precompile/2fa7d9a2/nixie` (first bad — newly cached for
  this handover), `precompile/d1dc7f0d/nixie` (good main-side parent),
  `precompile/d49c8936/nixie` (good mfinder-side content),
  `precompile/cd544511/nixie` (current `main` at time of writing).
* Full 181-binary verdict sweep: `precompile/cd544511/benchmark/wisas_verdict_sweep.txt`.
* Unrelated observations from the same suite run: `bv_odd_width_blast_differential::odd_width_identity_pairs_hold`
  and `recfun_e2e::symbolic_argument_solves_for_the_variable` timed out at
  the 180 s nextest cap under load ~19 — not yet re-examined on a quiet
  machine; may be environmental.
