# Handoff: the arithmetic arc, items 86–95 — the corruption at the bottom found and closed; the reads were wrong, the rows never were (2026-09-19)

**Read `AGENTS.md` first — it is canonical.** This handoff continues the
arithmetic arc whose memory is
`docs/studies/2026-09-13-lia-wide-literal-arithmetic.md` — **items 1–95**;
read at least items 86–95 (continuations 42–51, this stretch) before touching
arithmetic. The predecessor handoffs are
`docs/handovers/2026-09-18-arithmetic-arc-items69-78-handoff.md` and
`docs/handovers/2026-09-19-wide-lp-post-landing.md`. Where they disagree, the
study wins.

## What this stretch was

Six sessions emptying the residual gap survey slice by slice, each landing
root-caused with its own reproducer: item 86 (the floating-constant pins),
87 (the interval refutation's sign), 89 (the exact B&B snapshot), 90 (the
snapshot's real half), 92 (content-addressed wide rows + the atom-row
canary), 93–94 (the tripwire), and **95 — the corruption at the bottom: a
wide point shadowing a wide row in every exact read**. Code landed:
`bf9f5b71`, `d542bd56`, `d0d5880c`, `65228ee8`, `6d8ee66f`, `7972fb4e`,
`01fc31a0`, `6b581764` (plus docs-only items 88/91/95). Binaries under
`precompile/<sha>/` for each.

**The wrong-verdict ledger stayed empty the whole stretch** — every survey
step, every differential seed, zero verdict disagreements, zero refuted
models, every recovered member's model z3-validated by binding it as
`define-fun`s and re-solving the negation.

## The verdict map (measure before believing)

Gap survey on the fixed seeds (20261000–02 × 600, binary
`precompile/6b581764/nixie`, z3 4.16.0): **78 members**, every one honest
`unknown`, zero wrong verdicts. The arc's cumulative run through this
stretch: **150 → 110 → 91 → 79 → 75 → 73 → 78** (the last step: 3 members
recovered, 8 reshuffled to honest `unknown` — see item 95's note on the
stale point as an accidentally-useful search guide).

Attribution of the 78 (from the item-92-era probes; re-attribute before
choosing a slice — the probe recipes are in the study):
* **A2, B&B node/depth budgets (~24)** with Q1/Q2 int-eq companions — the
  largest named slice. Any budget bump is a heuristic change: matched nulls,
  ≥10 seeds, `docs/BENCHMARKING.md` FIRST. The parallel session's
  `patch_basic_columns` landing (`be5033a2`) reshaped this area — re-read it
  before tuning.
* **8 reshuffle members** (item 95's cost) — decidable `sat`s that the
  stale-point guide used to find; the honest search must reach them another
  way (budgets, or a real branching heuristic).
* **Tails**: S3 wide-repair remnants, probe-silent timeouts.

## Open items, in priority order

1. **A2 B&B budgets (~24 members)** — matched nulls and the benchmarking
   discipline FIRST. Entry points: `LIA_MAX_NODES`/`LIA_MAX_DEPTH`
   (solver.rs), the dive's `MAX_DIVE_NODES`, and Z3's per-firing cut budget
   (landed by the parallel session). Check first whether the wide-point fix
   already shrank the class (the probe recipe: statement-position `Unknown`
   tags — A2-bnb-budget, A2b-leafbudget, A2c-cut-rounds, A2d-final-budget,
   Q1/Q2-inteq — sites named in items 86/88).
2. **The 8 reshuffled members** — cheap to attribute: run each with the
   decline probes; if they are A2-budget, they fold into item 1.
3. **fi1** (`docs/studies/assets/2026-09-17/false-unsat-fi1.smt2`) — still
   open, still the named unfulfilled prediction. The exact channels all
   exist now; with item 95's read fix landed, re-run it before assuming the
   old blocker still applies.
4. **Item 75's strict-stranding reproducer** (from the items-69-78 handoff;
   differential-screened only) and **item 71's re-assertion channel
   question** — both still open, both cheap.
5. **The doc gate**: `RUSTDOCFLAGS="-D warnings" cargo doc` currently fails
   on `nixie-core/src/ast/manager/query/simplify.rs` link errors — a
   parallel session's in-flight landing (`MIN_SHARED_SUBTREE_SIZE`,
   `CTX_GROWTH_LIMIT` unresolved/private links). Not ours; verify it is
   fixed before gating on it.

## The defect classes this stretch closed (do not re-derive them)

* **A wide point never shadows a wide row** (item 95, THE root): a variable
  parked at a wide bound as a nonbasic keeps its `wide_points` entry; when
  it later becomes wide-BASIC, `point_value_exact` read the FROZEN point
  while the constraint machinery composed through the LIVE row — published
  models violated their own committed atoms, the evaluator refuted, the
  gate degraded decidable `sat`s to `unknown`. Fixed on both sides: the row
  is read first, and gaining a defining row retires the parked point.
  **Every "detachment" observed in items 91–94 was this read, not a row
  corruption.**
* **The leaf snapshot must be exact at any width, both sorts** (items 89/90):
  the dive's scopes pop after the snapshot; integers beyond width and reals
  (δ-instantiated INSIDE the leaf's scopes) must survive the pop, or the
  model builder defaults them to `0` and the certifier refutes a genuine
  leaf.
* **The interval refutation's endpoint sign** (item 87): for `c < 0` the
  contribution is `+ c·endpoint`, never subtracted — the widened range only
  ever failed to refute (conservative), but it starved the repair step into
  NOCOL declines.
* **The floating-constant classes** (item 86): constant columns are PINNED
  to their exact value (tautological reason, dropped from cores knowingly);
  fractional beyond-width constants synthesize a numerator column at
  `−1/d`; the column replaces the moved-to-RHS constant (`coef·col =
  −moved`) — the sign inversion was latent behind the λ fast path.
* **Wide rows are content-addressed** (item 92): rebuild rounds re-assert
  the same atoms; without `BigLinKey` every round minted a duplicate
  (~150-row zoo), each pivoted and classified forever.
* **Honest-read guards cover BOTH wide channels** (item 86): `value()`,
  `can_increase`/`can_decrease`, and the model builder's DL-potential
  ordering all learned the wide-point cases; a row carrying a
  wide-constant column breaks DL purity (the difference graph cannot see
  the pin).

## The instrument set (all landed, all env-gated — recipes in items 93–95)

* **`NIXIE_LEAF_TRIPWIRE=1`** (release-runnable): at the dive's
  snapshot/dive-pre/dive-post, every live atom row's slack must satisfy
  `slack = r·(key form)` at the current exact points. Prints
  entry/own-row/key-form/dir per fire — the discriminator that separates
  staleness (entry ≠ own-row) from read corruption (entry == own-row ≠
  key-form). Four false-positive classes are gated (popped atoms,
  floating columns, stale vectors, rowless/unevaluable slacks); it is
  silent on the whole arith suite and the 224-file debug corpus — **any
  new fire is a real defect**.
* **The debug atom-row canary** (debug builds, check() entry): the same
  equivalence as a `debug_assert`. Silent post-gates.
* **The tracer recipes** (session-local, rebuild from the study):
  pivot form-preservation (`NEW[v] = OLD[v] + sc·E[v]`, BOTH commit loops),
  intern-time equivalence (input eval vs landed row eval, with
  `fresh=` per fire), the snapshot term-read dump (a wide row's own reads
  vs the value returned — this is the one that caught item 95),
  `[cert-false]` + `INTERP` with `manager.resolve_str` (which conjunct the
  published values violate), and the decline-site tags.
* Standing: `NIXIE_BOUND_TRIPWIRE`, `bench/differential/gap_survey.py`
  (fixed seeds attribute, fresh hunt), the polarity pipeline.

**Tracer discipline that cost real time** (item 94 records the full
embarrassment): verify a tracer's algebra on a known-good run before
trusting its fires — the pivot tracer's first version had a sign error and
"fired" 3 times on healthy rewrites; the canary needed four gated
false-positive classes before it went silent. A firing instrument is a
hypothesis, not a verdict, until its identity is hand-checked on one live
fire.

## The verification bar (unchanged, plus this stretch's traps)

`cargo build --all-features`; `cargo nextest run --workspace --all-features`
(expect ~4.7k in the arith crates / ~12k workspace; the
known_unsound/model_soundness/qfidl failures are corpus-missing in
worktrees — they pass in the main checkout; load-cap timeouts re-run in
isolation); doc tests; clippy (DEBUG profile) / fmt / `RUSTDOCFLAGS="-D
warnings" cargo doc` (see open item 5 — currently red on a parallel
landing); `./bench/z3_parity/run_parity.sh` (z3 4.16.0, record the
version); the wide + mixed differentials (≥3 fresh seeds each; extend
SHAPES, not seeds); `debug_panic_sweep.py`; **the perf gate for anything
touching solving**; the survey delta on the fixed seeds as the
attribution. A bug fix ships with the reproducer as a test; revert-check
the whole fix.

Traps that fired this stretch:
* **`bench/perf_gate/BASELINE` was re-pinned twice mid-session** by
  parallel sessions — an explicit `GATE_BASELINE` override against a stale
  pin produces spurious `base=none` VERDICT MISMATCHes once the old binary
  is cleaned. Re-read BASELINE immediately before gating; when it moves,
  re-gate against the new pin.
* **Main raced 2–3 times per session.** Land fast, rebase late, ff from a
  clean tree; `git rev-parse HEAD` after every landing (the ff-merge
  silent-abort trap from the predecessor handoff still applies).
* **`/media/data` hit 100% repeatedly** (shared `target/`, concurrent
  agents). The debug full-suite links SIGBUS on ENOSPC. Completing the
  battery with `CARGO_TARGET_DIR` on the root disk (~10G, deleted after)
  is the recorded precedent — document it, clean it.
* **Probe placement**: a print placed AFTER a clearing statement reports
  the cleared state (the "model is empty at J5" false lead — item 88).
  Place probes before mutations.
* **Doc nits and dead code ride in on merges** (one empty `if` from the
  stamps landing broke clippy; another agent landed the same removal
  independently — the rebase kept theirs). Re-run clippy after every
  rebase.

## Working knowledge that cost real time

* **The two wide stores are a lattice, not a cache**: a variable is
  nonbasic-at-a-wide-bound (point) OR basic-with-a-wide-row (row) — never
  both, and the row is authoritative for basics. Any new code that parks,
  retires, or reads wide state must maintain that invariant;
  `retire_wide_point` is the choke point.
* **Rows are search-global; their constraints are scoped.** A popped atom's
  row legitimately rests anywhere — only live bounds make a row's state
  evidence. Every canary gates on `has_live_bound`.
* **The atom-row cache keys are pre-normalization forms**: equality rows
  are sign-normalized at intern (first coefficient positive), rescaled
  rows are positive multiples — any key-vs-row comparison must accept
  nonzero `r` for Eq and positive `r` for ineqs, and skip floating
  (unpinned) constant columns.
* **`intern` mid-search while the assignment vector is stale is legal**
  (the documented allowance) — an intern-time value comparison must record
  `fresh` or it will mislead (item 95's own tracer did, twice).
* **The J5 gate certifies; it does not refute.** `certify_quantified_sat`
  returning false on a MISSING model is not a refutation — and a candidate
  that fails certification with an honest model is a real upstream defect
  (items 89/90/95 all presented this way).
* Reason ids recycle across pops; the two interning systems
  (`intern_row_reported` vs `intern_row_cached`) never collide — both
  still hold from the predecessor handoff.

## Where things live

* The arc's memory: `docs/studies/2026-09-13-lia-wide-literal-arithmetic.md`
  (items 1–95; continuations 42–51 are this stretch — each item records
  its own probe recipes and measured deltas).
* Regressions: `nixie-solver/tests/arith_wide_literal_regressions.rs` —
  this stretch added the `pinned_*`, `fractional_wide_constant_*`,
  `constant_column_sign_*`, `wide_point_model_*`, `wide_row_interval_*`,
  `bnb_snapshot_*`, `leaf_snapshot_*`, and
  `wide_point_never_shadows_a_wide_row` families.
* Binaries: `precompile/<sha>/nixie` for every landing above
  (`6b581764` is the current tip's).
* Methods: `docs/BENCHMARKING.md`, `bench/differential/METHODOLOGY.md`,
  `bench/z3_parity/METHODOLOGY.md`.

The one-sentence version: **items 86–95 closed every residual the survey
could name — the last of them a read-side shadowing defect four layers deep
(the rows were never corrupt, the reads were) — with the ledger empty, the
tripwires silent, and the remaining 78 honest `unknown`s mapped to the B&B
budget slice (heuristic work, matched nulls first) and named tails; the
instruments to take any of them are wired and their false-positive classes
are gated.**
