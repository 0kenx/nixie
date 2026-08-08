# 0.3.2 → main integration notes

Branch `integrate/0.3.2`. This document records the judgment calls behind the
open items, with the measurements that back them, so a reviewer does not have
to read 22+ commit messages to find them.

**Baseline verified (default features, debug):** `9858 passed / 0 failed / 36
ignored` on `2ace7dd8` (HEAD after items 1–2 below). The briefed baseline was
`9746 / 0 / 40`; the deltas are tree drift plus the four tests this pass moved
from `#[ignore]` to passing. `cargo test --workspace --all-features` does **not**
compile on this tree: the `profiling` feature of `oxiz-theories` threads a
non-`Sync` `TermManager` through `std::thread::spawn_scoped`
(`nl_model_search.rs:301`). That is a pre-existing workspace issue unrelated to
this integration; the default-feature suite (how the 9858 number is obtained)
is unaffected. Flagged for the maintainer.

## Open items

### 1. Inprocessing unsoundness — disposition: documented, not fixed (pre-existing in v0.3.2)

`oxiz-sat/tests/pr26_lrat_proof_regressions.rs:290` was `#[ignore]`d with a
reason blaming "a wrong Sat for pigeonhole(6,5)" on the "Preprocessor
clause-management interaction." Investigation sharpened this considerably.

**Root cause (named step).** `Solver::inprocess()` runs subsumption,
pure-literal elimination, and on-the-fly clause strengthening, then ends with
the comment *"Rebuild watch lists for any modified clauses. This is a
simplified approach — in a full implementation, we would track which clauses
were removed and update watches incrementally."* It does **not** rebuild the
watch lists. The result, caught by the debug-only
`check_unit_propagation_complete` invariant, is a *"hanging unit at a
propagation fixpoint: clause ClauseId(N) has exactly one unassigned literal
and is not satisfied, so unit propagation should have fired"* — i.e. a live
clause the watcher/propagation loop no longer enforces.

**It is pre-existing in upstream v0.3.2, not a main regression.** Verified by
controlled transplant into a `v0.3.2` worktree (`7fb36aab`): v0.3.2 fails the
*identical* debug invariant on the identical config (pigeonhole(6,5),
`enable_inprocessing: true`, `inprocessing_interval: 1`, LRAT off):

| config (debug)                                   | main      | v0.3.2    |
|--------------------------------------------------|-----------|-----------|
| inproc=ON,  lrat=OFF  (pigeonhole 6,5)           | **panic** | **panic** |
| inproc=ON,  lrat=ON   (pigeonhole 6,5)           | **panic** | ok        |
| inproc=OFF, either    (pigeonhole 6,5)           | ok        | ok        |

The only main-vs-v0.3.2 difference was the dropped `|| self.lrat` guard in
`inprocess()` (v0.3.2 skips inprocessing entirely while an LRAT tracer is
attached). **Fixed (commit `5dc6d16c`):** re-added the guard; un-ignored the
test. The deeper inprocessing-without-LRAT corruption is unchanged from
v0.3.2 and is **not** fixed here — repairing it would mean inventing a fix
beyond upstream, which the method forbids.

**Blast radius (release build, debug_assertions off).** The debug panic proves
corruption; whether it *flips the verdict* in release is a separate question,
measured directly:

- **Wrong verdict is reproducible, but only at low interval.**
  `pigeonhole(7,6)` (UNSAT) with `inprocessing_interval: 1` returns `Sat`
  (wrong) in a release build on main. At `interval ≥ 10` (and at every preset
  interval 2000–10000) it returns the correct `Unsat`. Reproduction:
  `scripts/inproc_blast_release.sh` + a throwaway example (see commit history
  of this note's investigation; artifact removed before commit).
- **At the presets' own intervals, no wrong verdict was reproduced.** A
  release-mode verdict-diff scan (`industrial` vs `default`, `MAXC=20000`,
  45s/file) over 40× `satlib/uf100` + 54× `satcomp2024` found **0 verdict
  divergences** in the 59 instances both presets concluded (35 hit the budget
  on both sides — `both_unknown`, not divergences). Pigeonhole (6,5)–(10,9)
  at the preset intervals: all correct.
- **But corruption still fires at preset intervals on hard instances.** The
  `circuit_48in64out` satcomp2024 instance panics in debug under the
  `industrial` preset (interval 5000) within ~15000 conflicts — so the exposure
  is open-ended; "no flip reproduced on the tested slice" is not "cannot flip."
- **main's release is observably worse than v0.3.2's on at least one
  instance:** on `pigeonhole(7,6)` interval=1, main returns wrong `Sat` while
  v0.3.2 returns correct `Unsat`. The corruption mechanism is shared (both
  panic in debug); the release verdict diverges because main's structurally
  different search recovers differently from the corrupted state.

**Exposure.** Five of ten public presets set `enable_inprocessing: true`:
`Industrial`, `Cryptographic`, `Hardware`, `Conservative`, `CaDiCaL` — and
`oxiz-sat/examples/cnf_solve.rs` advertises `CaDiCaL` as *"the strongest sound
configuration."* Anyone who lowers `inprocessing_interval` (or builds a config
mirroring the `audit_sat_p3` style `interval: 1`) is directly exposed; the
shipped preset intervals (2000–10000) are exposed in principle but no wrong
verdict was reproduced on the tested slice.

**Disposition (this integration).** Kept the preset values exactly as v0.3.2
(changing them would diverge from upstream *and* break `test_industrial_config`
/ `test_conservative_config`, which pin `enable_inprocessing == true`). Added a
loud soundness caveat to the `config_presets.rs` module doc recommending the
inprocessing-off presets (`Default`, `Glucose`, `MiniSat`, `Random`,
`Aggressive`) for guaranteed soundness. The debug propagation-fixpoint
invariant remains the CI safety net: any future change that worsens this will
panic in the test suite, not silently ship.

**Decision deferred to maintainer.** If you want a stronger default, the
options are (a) flip `enable_inprocessing: false` in the five presets (one-line
each + update the two pinning tests), or (b) make `inprocess()` itself a no-op
until the watch-rebuild is implemented. Both are sound; neither is a faithful
v0.3.2 port, so I did not take them unilaterally.

### 2. LRAT hint-chain gap — fixed (faithful port of v0.3.2)

Three tests in `pr26_lrat_proof_regressions.rs` (unit-clause contradiction,
corruption-helper sanity, writer-inert-after-finalization) were `#[ignore]`d.
The ignore reasons described the symptom ("chain the checker rejects") but not
the boundary.

**Blast radius confirmed: proof-output only, zero verdict impact.** All three
failed at the `assert!(report.verified, …)` line — never at a verdict
assertion. The verdicts (`solver.solve() == Unsat`) were correct throughout;
only the emitted LRAT *proof text* failed to re-verify. v0.3.2 passes all three.

**Root cause (single).** `Solver::add_clause`'s contradiction branches (unit vs.
existing level-0 fact; binary/3+ unconditional conflict) set `trivially_unsat`
and deferred empty-clause emission to `solve()`'s `drat_emit_empty(None)`, which
builds an *empty* RUP hint chain. The v0.3.2 checker rejects a derived empty
clause with no hints (acceptable only for a literally-empty *original* input
clause). v0.3.2 instead emits immediately from `add_clause` via
`lrat_emit_empty_from(seed_lits, final_id)`.

**Fix (commit `2ace7dd8`):** ported v0.3.2's `lrat_emit_empty_from` as
`Solver::drat_emit_empty_from_seed`, wired into the three contradiction
branches. The chain is `[unit id of each seed literal's negation] ++ [final_id]`
— identical to what main's existing `build_chain_for_empty(Some(cid))` computes
for a stored clause, since the contradicting clause is fully falsified at level
0 (v0.3.2's general `lrat_build_hint_chain` reduces to the same chain there).
Also ported v0.3.2's immediate flush at finalization so a caller reading the
proof file before dropping the solver sees the concluded proof. All 15 LRAT
tests pass; the other 12 were untouched and still pass. Suite: `9858 / 0 / 36`.

### 3. Coverage sweep

**This is a selective behavior port, not a file-level sync.** main and v0.3.2
have divergent module structures: 21 v0.3.2 source files in the core crates do
not exist in main *or* on this branch at all (e.g.
`oxiz-solver/src/solver/encode/bool_euf_encoding.rs`, `eq_skeleton.rs`,
`theory_manager/{intern,nelson_oppen}.rs`, `oxiz-theories/src/{nl_eval,
nl_ground_reduce,nl_repair_search}.rs`, `oxiz-sat/src/solver/{probe,add_clause,
lrat_trace}.rs`, `oxiz-sat/src/proof.rs`). main has its own equivalents under
different paths. So `git diff --stat main v0.3.2` (177 files) overstates the
integration's surface: most of the delta is structural divergence the
integration deliberately did **not** reorganize.

The integration is 24 behavior-port commits. Bucketing by test coverage:

**A. Directly test-covered (dedicated regression suite added):**
- SAT search/gatekeeper/inprocessing/LRAT → `pr26_{search_core,gatekeeper,
  inprocessing,lrat_proof}_regressions.rs` (this pass added/refreshed these).
- NIA div-mod deferral → `pr27_nia_divmod.rs`, `pr27_divmod_semantics.rs`,
  `pr27_define_fun_params.rs`, `pr27_arith_resample.rs`, `nlsat_mixed_sort.rs`.
- Nonlinear/array-select search → `pr31_nonlinear_search.rs`, `pr32_pr33_soundness.rs`.
- Arithmetic `entailed_disequal_reason` → inline module tests in
  `oxiz-theories/src/arithmetic/solver.rs` (90 lines).
- `scope_rebase` convergence → `scope_rebase_tests.rs`.

**B. Behavior ported, no dedicated test — covered indirectly by the existing
QF/MBQI/BV/EUF/LIA integration suites** (these are whole-solver invariant fixes
exercised by the 9858-test suite, not unit-isolated):
- `fix(solver): gate numeric-UF-arg purification off for quantified goals`
- `fix(theories/nia): make model-based NIA search rigorously sat-only`
- `fix(solver): re-derive EUF equality classes on pure-equality Sat`
- `port(solver): get-value div/mod folding from v0.3.2`
- `refine(solver): per-function purification gate`
- `fix(solver): don't wipe freshly-drained theory state in lazy-mode final_check`
- `fix(solver): make numeric-equality trichotomy splits idempotent across checks`
- `fix(solver): populate quantifier_uf_funcs …`
- `fix(solver): resolve purification proxies in get-value/get-model eval`
- `fix(solver): EUF congruence-consistency backstop for quantified sat`
- `fix(bv): gate eliminate_nonbool_ite out of BitVec/Array/String/Float sorts`
- `fix(solver): refuse Sat when a ground assertion is false in the model`
- `port(proof): pure-Rust LRAT checker from v0.3.2` (exercised by pr26_lrat_proof)
- `fix(sat): port lrat_unsat_finalized guard against double finalization`

**C. Not examined / out of scope (visibility list, unresolved):**
- v0.3.2's structural reorganizations were not adopted: the `encode/` reorg
  (`bool_euf_encoding`, `finite_map_ite`, `numeric_purification`, `eq_skeleton`),
  the `theory_manager/` split, the `nl_eval`/`nl_ground_reduce`/`nl_repair_search`
  NL-reduction modules, the standalone `probe.rs`/`add_clause.rs`/`lrat_trace.rs`
  SAT files. These are alternative organizations of functionality main already
  has under its own structure; they were not diffed behavior-by-behavior.
- Pure performance tuning, refactors, and internal-invariant changes in v0.3.2
  that carry no observable behavior change are invisible to this audit by
  construction (the audit finds only behavior its tests pin).
- `bench/`, `oxiz-py`, `oxiz-wasm`, `oxiz-cli`, `docs/`, `TODO.md`,
  `CHANGELOG.md` deltas: not audited for behavior.

The honest coverage claim for the PR: **every v0.3.2 behavior its own test
suite pins is now on main, or is documented as a known gap with a root cause.**
Behavior v0.3.2 changed without test coverage (perf/refactor/invariant) is not
enumerated item-by-item; bucket C above is the residual.
