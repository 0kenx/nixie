# Differential SMT bench (soundness + perf vs z3)

This is the harness that found the `vhard7` soundness regression that 9,858
passing unit tests did not (see `../../INTEGRATION_NOTES.md`). It runs an oxiz
binary over a **pinned** SMT-LIB sample and diffs every verdict against z3, so
two builds / two PRs are compared over exactly the same instances.

**The `smt-lib/` corpus is not in git** (`.gitignore`d — it is ~100k external
benchmark files). Fetch SMT-LIB under `smt-lib/` before running; the harness
fails fast with instructions if it is absent.

## The pinned sample

`sample/selected.json` — 270 instances, ≤30 per QF_* logic, sampled with
`SEED=20260807` from the z3-solvable (≤5 s) subset of `smt-lib/`. z3's verdict
and time are embedded, so a normal run does **not** invoke z3; only the oxiz
binary under test is run. Checked in so every run is reproducible and directly
comparable.

## Run

```bash
# from the repo root: build the solver under test, then bench it
cargo build --release -p oxiz-cli
python3 bench/differential/bench_diff.py --bin target/release/oxiz --label integrate
```

Flags:
- `--validate-models` — for every `sat`, re-run the solver to emit a model and
  ask **z3** whether `asserts ∧ model` is consistent (`unsat` ⇒ the model
  contradicts the assertions ⇒ the `sat` is not trustworthy). Needs z3 on PATH
  (`--z3`, default `z3`). Off by default; the bare gate never calls z3.
- `--baseline <summary.json>` — compare this run to a committed baseline and
  exit `2` on regression (`agree_z3` down, or `disagree_soundness` up).
- `--logic QF_ANIA,QF_BV` / `--limit N` — slice the sample (fast iteration).
- `--timeout`, `--jobs`, `--out`, `--label`, `--extra` — as before.

Outputs land in `bench/differential/results/<label>/`:

- `results.jsonl` — per instance: path, logic, family, z3 verdict, oxiz verdict, time, and (with `--validate-models`) `model_status`.
- `unsound.json` — every instance where oxiz disagrees with z3 on a sat/unsat.
- `families.json` — per-family rollup (disagreements, sat model-status counts); the family-neighbour view.
- `summary.json` — solved / agree_z3 / disagree_soundness / timeout / PAR-2, plus (with `--validate-models`) the **trust breakdown** below.

The script exits **non-zero on any soundness disagreement** (oxiz `sat` where z3
`unsat`, or vice-versa). Timeouts / `unknown` are not soundness failures and do
not fail the gate. With `--baseline`, it also exits `2` on a completeness
regression.

## Trust model (what `--validate-models` adds)

z3's embedded verdict is the satisfiability oracle: an oxiz `sat` that agrees
with z3 *is* a correct answer (the instance genuinely is satisfiable), so
`agree_z3` remains the **completeness** count. But "correct" and
"trustworthy-as-evidence-to-port" differ, so `--validate-models` reports:

- `sat_model_valid` — oxiz `sat`, z3 `sat`, and oziz's model is consistent with the assertions (real solve).
- `sat_model_invalid` — oxiz `sat` whose model contradicts the assertions (bogus `sat` **or** a broken model emitter — either way not trustworthy).
- `sat_family_suspect` — an agreeing `sat` in a family that contains *any*
  disagreement (verdict or invalid-model) for this solver. The QF_ANIA pattern:
  one over-eager-sat mechanism scores on the satisfiable half and errs on the
  unsatisfiable half; the family flag says "don't credit this as a capability."
- `sat_trusted` — agreeing `sat` AND `model_valid` AND not `family_suspect`.
- `unsat_trusted` — an agreeing `unsat` (an over-eager-sat mechanism can never
  produce a correct `unsat`, so an agreeing `unsat` is trusted by construction).
- `trusted_total` = `sat_trusted + unsat_trusted` — **the number to plan ports
  against.**

The validator is **z3-based, not oziz's own** `--validate-model`/`eval_in_model`:
oziz's internal evaluator was measured to false-alarm on genuinely-satisfiable
UF instances, so it cannot be the oracle. Function models are skipped during
pinning — this can only make the check *lenient* (more `sat`), never a false
`unsat`, because `(asserts ∧ pinned-constants)` unsat already implies no
function extension rescues the formula.

## As a PR gate

For any PR touching the solver core (`oxiz-solver`, `oxiz-theories`,
`oxiz-sat`, `oxiz-nlsat`), run the gate on the pinned sample:

```bash
cargo build --release -p oxiz-cli && \
  python3 bench/differential/bench_diff.py --bin target/release/oxiz --label pr
```

A non-zero exit means the PR introduced or kept a wrong-verdict instance and
must not merge until that instance is either fixed or added as a documented
`#[ignore]`d guard in `oxiz-solver/tests/known_unsound_regressions.rs`.

## Regenerating the sample

Only when the corpus or the sampling changes (not per-PR). Requires `z3`:

```bash
# 1. list every .smt2 under smt-lib/
find smt-lib -name '*.smt2' > bench/differential/sample/all_smt2.txt
# 2. screen with z3 (≤5 s), then re-sample with SEED=20260807
python3 bench/differential/z3_screen.py            # -> results/z3_screen.jsonl
# 3. re-derive sample/selected.json from the screen (see bench_diff.py / the
#    original bench_smt.py sampling logic; keep SEED=20260807 for continuity,
#    or bump it and re-baseline the numbers below)
```

## Baseline numbers (measured with this harness)

Differential run vs z3 4.16.0, sample seed 20260807, release builds, τ=10 s.
The `integrate-d293d91d` row is **measured** by this script on the branch tip
after the vhard7 fix; the `oz`/`main` rows are from the original screening run
(reproducible by passing those binaries with `--label`).

| build | solved | agree z3 | disagree (soundness) | timeout/unknown |
|-------|-------:|---------:|---------------------:|----------------:|
| oz (v0.3.2 `7fb36aab`)           | 159 | 143 | **16** | 95 |
| main (`ebbced38`)                | 123 | 119 |  4    | 147 |
| integrate pre-vhard7-fix (`bd380ec0`) | 125 | 120 |  5    | 145 |
| **integrate post-fix (`d293d91db`)**  | **124** | **120** | **4** | **146** |

The only delta from pre- to post-fix is `vhard7` moving from a wrong `sat`
(counted as solved, but unsound) to a `timeout` — a soundness correction, not a
collateral completeness loss: no other solved instance was pushed over τ and no
new disagreement appeared. The 4 remaining disagreements (`storecomm_t3`,
`bench_679`, `ext_con_064`, `xs_8_13`) are all pre-existing on `main` and are
pinned as `#[ignore]`d guards in
`oxiz-solver/tests/known_unsound_regressions.rs` — which is why the gate's
non-zero exit (it reports those 4) is acceptable for merge: every disagreement
is already a documented guard, satisfying the gate rule below.

Two strategic reads from these numbers (full discussion in
`../../INTEGRATION_NOTES.md`): (1) v0.3.2 is **not** the gold standard — it is
~4× less sound than main on this sample, so "faithful to v0.3.2" is not a
soundness argument; (2) the opportunity next to this integration is
completeness/perf (33 instances oz solves that main times out on), not more
v0.3.2 porting.
