# 0.3.2 → main integration notes

Branch `integrate/0.3.2`. This document records the judgment calls behind the
open items, with the measurements that back them, so a reviewer does not have
to read 22+ commit messages to find them.

**Baseline verified (default features, debug):** `9859 passed / 0 failed / 40
ignored` on `ef731000` (branch HEAD after the post-review fixes). The briefed
baseline was `9746 / 0 / 40`; the deltas are tree drift plus the tests this
pass moved from `#[ignore]` to passing plus the new soundness guards. `cargo
test --workspace --all-features` does **not** compile on this tree: the
`profiling` feature of `oxiz-theories` threads a non-`Sync` `TermManager`
through `std::thread::spawn_scoped` (`nl_model_search.rs:301`). That is a
pre-existing workspace issue unrelated to this integration; the default-feature
suite is unaffected. Flagged for the maintainer.

## §0. Post-review correction — the branch DID introduce a soundness regression

An earlier draft of these notes (and the §1 framing) claimed the inprocessing
unsoundness was the only soundness concern and was "pre-existing in v0.3.2, not
a main regression." A differential benchmark against z3 (§4) disproved the
spirit of that: the branch introduced a **new** wrong-`Sat` on
`smt-lib/.../QF_UFIDL/.../vhard7.smt2` (z3: unsat). `git bisect` localized it
to `0c526e9c` ("gate eliminate_nonbool_ite out of BV/Array/String/Float
sorts"), whose ported `collect_ground_subterms` treats `let` as opaque — so the
mux axioms for the `ite`s inside vhard7's wrapping `let` were never emitted.
**Fixed in `bb73c30c`** (descend into `let`, keep `Forall`/`Exists` opaque);
pinned by `oxiz-solver/tests/known_unsound_regressions.rs::vhard7_is_not_sat`.

This is an **imported upstream bug** (oz = v0.3.2 returns the same wrong
`sat`; main timed out), but it is still a regression by the branch's own
standard — main did not return `sat` here, the branch did. The lesson, now
encoded in §1's preset decision and §3's coverage caveat: **v0.3.2 is not the
gold standard** (it is ~4× less sound than main on the differential sample — 16
vs 4 disagreements), so "faithful to v0.3.2" is right for *mechanism* but is
**not** a soundness argument. Port-don't-invent stays the rule for how to
implement a fix; it is no longer the justification for whether a v0.3.2
behavior should be kept.

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

**Disposition (resolved post-review).** Inprocessing is now **disabled in all
presets** (`bbf9ff9cc`): Industrial, Cryptographic, Hardware, Conservative,
and CaDiCaL all set `enable_inprocessing: false`, with `test_industrial_config`
updated to match and the module doc rewritten. A differential benchmark
against z3 (see §4) settled the previously-open preset question: upstream
v0.3.2 disagrees with z3 on 16/270 sampled instances vs main's 4 — matching
upstream's inprocessing-on presets is matching a solver ~4× less sound on a
pipeline already proven to have a wrong-verdict path, so the fidelity argument
does not survive the data. Callers who want inprocessing and accept the known
unsoundness can still opt in via `SolverConfig`; no preset turns it on by
default. The real fix — a correct watch rebuild in `inprocess()` — is the
follow-up ticket, now well-scoped since the mechanism is named.

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

**§3 addendum (the audit's blind spot, now empirically instantiated).** The
v0.3.2-test-suite audit cannot see a v0.3.2 behavior that no v0.3.2 test pins.
The differential bench instantiated exactly that: `bench_679` (QF_BV,
bvule/bvshl-heavy) is wrong on main (`sat` where z3 says `unsat`), unchanged by
24 commits of behavior porting — because no v0.3.2 test covers that BV path —
yet v0.3.2 itself answers it correctly. So `bench_679` is a concrete **port
candidate** (diff main vs v0.3.2 on the BV comparison/shift encoding) and a
free win; it is pinned as an `#[ignore]`d guard in
`known_unsound_regressions.rs` until that port lands. The other three
pre-existing disagreements (`ext_con_064`, `storecomm_t3`, `xs_8_13`) are wrong
on v0.3.2 too and are tracked, not port candidates.

## §4. Differential benchmark (soundness + perf vs z3)

The pinned-sample differential run that found vhard7 is checked in at
`bench/differential/` (`bench_diff.py` + `sample/selected.json`, seed 20260807,
270 instances). Run it as a PR gate for any change touching the solver core:

```
cargo build --release -p oxiz-cli && \
  python3 bench/differential/bench_diff.py --bin target/release/oxiz --label pr
```

It exits non-zero on any soundness disagreement (oxiz `sat`/`unsat` ≠ z3 on a
sat/unsat instance); timeouts/`unknown` do not fail the gate. Baseline numbers
at the time it was added (z3 4.16.0, τ=10 s):

| build | solved | agree z3 | disagree (soundness) | timeout/unknown |
|-------|-------:|---------:|---------------------:|----------------:|
| oz (v0.3.2 `7fb36aab`) | 159 | 143 | **16** | 95 |
| main (`ebbced38`)      | 123 | 119 |  4    | 147 |
| integrate pre-vhard7-fix (`bd380ec0`) | 125 | 120 |  5 | 145 |

Post-vhard7-fix, integrate drops to 4 disagreements, **all pre-existing on
main** — so the branch introduces no net new soundness regression once vhard7
is resolved. **Measured** on the post-fix tip (`d293d91db`, this script):

| build | solved | agree z3 | disagree (soundness) | timeout/unknown |
|-------|-------:|---------:|---------------------:|----------------:|
| oz (v0.3.2 `7fb36aab`) | 159 | 143 | **16** | 95 |
| main (`ebbced38`)      | 123 | 119 |  4    | 147 |
| integrate pre-fix (`bd380ec0`)  | 125 | 120 |  5    | 145 |
| **integrate post-fix (`d293d91db`)** | **124** | **120** | **4** | **146** |

The only pre→post-fix delta is `vhard7` (wrong `sat` → `timeout`): a
soundness correction, not a collateral completeness loss — no other solved
instance was pushed over τ and no new disagreement appeared. The headline for
the PR is therefore *124 solved, 120 agreeing with z3, 4 unsound — all
pre-existing on main, none introduced by the branch*, +1 solved over main on
the sound subset and gmean 1.01× vs z3 on it (speed is fine; the gap is what it
can't finish — see the strategic note in the PR description).
