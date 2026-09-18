# Handoff: exact arithmetic in the simplex — the wide-LP build that dissolves the width walls (2026-09-18)

**Read `AGENTS.md` first — it is canonical.** The arc's memory is
`docs/studies/2026-09-13-lia-wide-literal-arithmetic.md` — items 1–76;
read at least the item list and items 9–11, 25–37, 42–43, 49–50, 55–66,
70–76 before touching arithmetic. Where they disagree, the guide wins.
The campaign's site map is item 67; the standing survey numbers are in
items 72–73 (gap 115 = 111 SAT-side + 4 UNSAT-side on seeds 20261000–02
at `f60e26c8`; 1 648 decisive).

## The example case that motivates this build (verify it first)

```smt2
(set-logic QF_LRA)
(declare-const xr Real)
(assert (< xr (/ (- 9223372036854775808) 1)))
(check-sat)
```

* z3: **`sat`** (its arithmetic is arbitrary-precision; any `xr < −2^63`
  works).  nixie (`precompile/f60e26c8/nixie`): **`unknown`** — the honest
  decline, and today the only sound answer.
* Why: the simplex's row channel is fixed-width `Rational64` (i64
  numerator/denominator).  Asserting `lhs < rhs` builds the row
  `lhs − rhs`, which needs `-rhs`; at `rhs = −2^63 = i64::MIN` that
  negation does not fit, and in two's complement **negating `i64::MIN`
  wraps back to `i64::MIN`** — pre-fix, the tableau silently held a row
  for a *different constraint* than the one asserted (a debug panic, a
  release wrong-verdict hazard).  Item 56's guard (`checked_neg_r64` at
  every `assert_*` entry — shared by Int AND Real rows, both sorts live in
  the same channel) declines instead: the atom stays unconstrained and a
  sticky flag makes `check()` answer `Unknown` forever after.
* `unknown` is not a claim about the formula — it is nixie saying "I
  cannot represent this faithfully; I refuse to guess."  Per AGENTS.md
  that is always sound; the loss is completeness.  These are the survey's
  "4 honest `i64::MIN` members" and the class generalizes: **every wall
  below is the same boundary** — the point where the narrow channel meets
  a value that leaves i64/Rational64 width.
* The cheap rewrite is a recorded dead end: flipping the row to
  `rhs − lhs ≥ 0` moves the overflow into the coefficient negations and
  cannot serve the strict/δ encodings (item 56; reals are strictly worse
  off — they have no `k±1` tightening route at all).  **Do not rediscover
  it.**

## What this build dissolves (measured, item 67's map)

* **~29 survey members**: B&B `FracVar::Underivable` — branch bounds
  (floor/ceil of an exact value beyond 2^63) leave i64, so no sound
  branch exists (item 42's `wide_floor_ceil_big` already recovers the
  recoverable).
* **4 members**: the `i64::MIN` corner above.
* **Part of the 5-member certification wall**: models that genuinely fail
  under the big-const abstraction because the abstracted column floats
  (item 67's `no-combination` class) — exact rows can *pin* the column.
* **fi1** (`docs/studies/assets/2026-09-17/false-unsat-fi1.smt2`): the
  2^62-width honest `unknown`; z3 decides it because its tableau computes
  exactly everywhere.

## What is already built (extend it; do not rebuild it)

The arc spent items 9–73 turning every fixed-width channel honest and
building the exact side-channels this project generalizes:

* **checked + exact-retry discipline** (items 14/25/26): every i64
  arithmetic site in the simplex is checked with a `BigRational` retry
  that narrows the final — intermediates may overflow, finals that fit
  are recovered; only a non-narrowing final sets the honest
  `resource_limit`.
* **the wide-row side table** (`wide_rows: FxHashMap<VarId, BigLinExpr>`,
  items 28–31, 35–37, 47–48, 59, 66): rows whose finals leave width are
  captured exactly, classified exactly at convergence (`wide_row_violated`
  via `eval_big_raw`), refuted by exact interval reasoning
  (`wide_row_refuted_by_bounds`), repaired by exact wide pivots, and
  entered by positive rescaling (`scale_big_to_narrow`) when a λ brings
  them back.
* **exact parse** (items 33–35): coefficient-wide comparisons re-parse in
  `BigRational` (`parse_arith_comparison_exact`) with the shared scaler.
* **exact publication** (item 63): `wide_basic_value_exact` /
  `value_exact` publish `BigRational` model values (`(/ n d)` via
  `mk_rdiv` — NEVER `mk_div`; the printer renders `Div` by sort for the
  round trip).
* **the strengthened `debug_verify_invariant`** (item 60): rows reference
  only nonbasics; entry == row eval; wide basics certified against EXACT
  evaluation.  A silent debug suite IS a soundness pass; a firing one
  names the wrong-verdict site.
* **crossed-window guards** (item 73): interval derivations decline on
  strictly inverted pairs — keep this invariant when the bound storage
  widens.

## The build

Z3's answer to all of this is structural: `lar_solver` stores rows and
bound values in `mpz`/`mpq` — **exact everywhere, no walls** (read
`../temp/z3`'s `src/smt/theory_arith*` and its simplex before designing;
that is the ground truth per AGENTS.md).  The equivalent here, in
increasing scope:

1. **Widen the BOUND channel** (`lower`/`upper` hold `DeltaRational` =
   two `Rational64`s): this is the missing piece behind the
   `Underivable` class and the `i64::MIN` corner — a `BigDeltaRational`
   (BigRational real + delta) bound store, with `set_*`/`record_crossing`/
   the endpoint selectors (item 73's guards included) operating exactly.
   The `assert_*` entry negations become exact, retiring item 56's
   decline.
2. **Widen the ROW channel**: rows as `BigLinExpr` wholesale, or — the
   cheaper shape consistent with everything landed — keep the narrow
   fast path and let the existing capture/rescale/migration machinery
   feed a *first-class* wide tableau (pivots through wide rows already
   exist; what does not is wide rows as pivot SOURCES with narrow
   dependents updated exactly).
3. **Widen the BRANCH/B&B channel**: branch bounds from
   `wide_floor_ceil_big` land in the widened bound store (1) — the
   `Underivable` arm disappears.

Decide 1-then-2-then-3 vs a wholesale `BigRational` tableau with a
measured cost gate.  **The perf discipline is mandatory** (read
`docs/BENCHMARKING.md` FIRST): exact arithmetic is slower per operation,
this is the solver's hot path, and the ±5% neutrality band applies —
the landed gates require conflicts/decisions ≤ 1.05 vs the pinned
baseline (`bench/perf_gate/BASELINE`, currently `f60e26c8`, binary under
`precompile/f60e26c8/`).  The dual-width design exists precisely to pay
exactness only where width demands it; a wholesale widening must beat
the band or gate itself.

## The verification bar

Unchanged and non-negotiable: `cargo build --all-features`; the full
suite (release-mode acceptable under disk pressure — document it; the 15
corpus-missing failures are pre-existing); doc tests; clippy/fmt/rustdoc
clean; `./bench/z3_parity/run_parity.sh` (z3 4.16.0; record the version);
`bench/differential/wide_fuzz.py` + `mixed_fuzz.py` ≥3 fresh seeds EACH
(the arc's rule: extend the generator's SHAPES, not its seeds — every
wrong verdict this arc found came from a fresh seed within 400
instances); `debug_panic_sweep.py` over the parity corpus (every abort
is an unchecked fixed-width site — after this build it should stay 0);
the perf gate; and the survey delta on the fixed seeds as the
attribution (expect the 4 `i64::MIN` members and much of the 29-member
`Underivable` class to close; pin each closed class with a regression —
the example case above belongs in
`nixie-solver/tests/arith_wide_literal_regressions.rs` pinned `sat`,
with its model validated by binding it as `define-fun`s and re-solving
with z3 — a green test is not a correct model).

## Working knowledge that cost real time (the arc's, condensed)

* **`unknown` before `wrong`, always.**  Every decline site this arc
  added is a place where a wrap used to fabricate a verdict.  When
  widening removes a decline, the removed guard's TEST is the contract.
* **Reason ids recycle across epochs** (reset+replay) — bounds die with
  the reset, but any id→term resolution outside one epoch is a
  single-atom-core factory (items 54, 55, 70).
* **Consumers of `assignment[]` near wide state must read the EXACT
  evaluation** (`eval_big_raw`/`wide_basic_value_exact`) — the stored
  entry is stale-by-design (items 63, 66).
* **The shared `target/` serves whatever another agent last built into
  it** — measure with binaries you built in a private `CARGO_TARGET_DIR`,
  and copy the landed binary to `precompile/<sha>/` yourself.
* `/media/data` runs 93–100% full; debug-mode full-suite links have
  SIGBUSed on ENOSPC twice.  Check `df -h / /media/data` before blaming
  your code (one "false unsat on main" was withdrawn as exactly this
  artifact).
* Multi-agent git: main moves mid-session; ff-merge from the primary
  only when your changed files are disjoint from the dirty set;
  `git push . HEAD:main` is refused for a checked-out main — merge
  `--ff-only` from the primary, and re-verify any "red on main" reading
  against the CURRENT tip before believing it (it may be one commit
  stale; item 72's process note).

## Where things live

* The study (items 1–76) and the site map (item 67):
  `docs/studies/2026-09-13-lia-wide-literal-arithmetic.md`.
* The survey: `bench/differential/gap_survey.py` (seeds 20261000–02
  reproduce the 115 members; fresh seeds hunt).
* Reproducers: `docs/studies/assets/2026-09-17/false-unsat-fi1.smt2`,
  `assets/2026-09-18/*` (the item-69/70 pair, the ndir2-only false
  unsat); the example case above is three lines — inline it.
* Binaries: `precompile/<sha>/nixie` for every recent landing
  (`f60e26c8` is the perf-gate baseline).
* Methods: `docs/BENCHMARKING.md`, `bench/differential/METHODOLOGY.md`,
  `bench/z3_parity/METHODOLOGY.md`.
* A parallel session is active on the same study (items 75–76 landed
  2026-09-18); check `git log` and the study tail before editing.

The one-sentence version: **the width walls are one wall — the
fixed-width channel — and every honest decline this arc shipped is a
marker on it; widen the bound and row stores to `BigRational` behind the
landed dual-width machinery, with the perf band as the gate and the
survey delta as the proof, and the 33+ member residual gap (and fi1)
closes at the root.**
