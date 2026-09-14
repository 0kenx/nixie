# Handoff: the arithmetic-soundness arc (2026-09-13 → 09-14)

**Read `AGENTS.md` first — it is canonical.** This handoff covers one arc's
state, its open items, and the working knowledge that isn't written down
anywhere else. It complements the guide; where they disagree, the guide wins.

## What this arc was

The TLA+ front end's encoder cross-check reported three LIA defects
(a panic at `i64::MAX`, `Unknown` above it, `Unknown` for literal `\div`).
Chasing them turned up a false `sat` underneath, and the chase kept paying:
**17 numbered findings** across the builder, the parser, the mixed-integer
mode, the linear parse, the certifier, the simplex, and the SAT core.
Every one is written up, layer by layer, in
`docs/studies/2026-09-13-lia-wide-literal-arithmetic.md` — that file is the
arc's memory; read its item list before touching arithmetic.

All 15 fixed items are landed on `main` with regressions; each landed with
the full verification battery green. The arc is closed except for the open
items below.

## Open items, in priority order

1. ~~**Invalid-model snapshot divergence (SAT core, item 17).**~~ **CLOSED
   2026-09-15** — see the study's Continuation 6 (items 18–20): the
   divergence was elimination-*reintroduction* (pure-literal pins, BVE
   ext-stack witnesses, and a poisoned `equiv_substitution` grown tail),
   fixed with per-layer regressions in `nixie-sat`. The reproducer family
   sweeps panic-free. Remaining from this item: rerun
   `bench_diff --validate-models` when the external corpora return to the
   shared tree (they were removed mid-session 2026-09-15; the 14
   `[corpus-missing]` workspace-test failures are that, nothing else).
   Through the `final_check`/rejection/re-entry cycle, the candidate the
   search accepts and the candidate `save_model` snapshots disagree on a
   variable's value. My guard fix (item 16) contains the symptom
   (originals-clause scan re-enabled under `push`/`pop`), but the divergence
   itself is unfixed. Reproducer:
   `smt-lib/non-incremental/AUFLIA/20170829-Rodin/smt3878551918658299427.smt2`
   (debug build; `debug_verify_model_input` fires). The study's item 17 has
   the full probe trace (per-save values, BIG edges present, pure/ext stacks
   empty) — three plausible hypotheses already eliminated.
2. **The wide-LP wall (items 11/15).** Value-dependent reasoning over
   constants ≥ 2^63 needs row arithmetic at that width inside the simplex;
   every encoding-level fix ends at the tableau's `Rational64`. Z3 decides
   these in `mpz`. The named reproducer is the delta-vs-reeval
   `debug_assert` in `pivot` (QF_NIA/VeryMax
   `From_T2__streamserver...terminationS_1_0.smt2`). The design shape:
   fixed-width fast path + promote-to-exact on overflow (the
   checked-plus-exact-retry pattern from item 14 is the local version; the
   project is the systemic one). **Benchmarking-gated** — read
   `docs/BENCHMARKING.md` (matched nulls, ≥10 seeds) before starting.
3. **Symbolic real division `(/ x y)`** (variable divisor): honest gate,
   defining identity is nonlinear; wants NLSAT dispatch.
4. **B&B budget exhaustion on hard disjunctive LIA+div/mod** — the residual
   fuzz `unknown` class. Pure search-capacity work; heuristic rules apply
   (matched nulls or don't ship it).

## Tools you inherit (all in-repo)

* `bench/differential/mixed_fuzz.py` — random differential vs z3 over the
  mixed-arith surface, stratified over declared logics (QF_LIA/QF_LRA/
  QF_LIRA/none). It found items 5, 10, and the item-9 gate bug within
  minutes. Extend the generator, not just the seeds.
* `bench/differential/debug_panic_sweep.py` — any corpus through the
  DEBUG binary; every abort is an unchecked fixed-width site (a silent
  release wrap). Baseline: 490 files + 1,200 generated instances clean.
  **Run it over any theory you touch.**
* `bench/differential/bench_diff.py --validate-models` — the pinned
  270-instance sample with z3-validated models; `TRUSTED_TOTAL` is the
  headline, `model_invalid=0` the bar.
* `./bench/z3_parity/run_parity.sh` — the parity gate (z3 4.16.0; record
  the version). Non-negotiable for anything touching solving/theories.

## The verification bar (unchanged, restated because it was used ~10×)

`cargo build --all-features`; `cargo nextest run --workspace --all-features`
(~11.4k tests, grows weekly); doc tests; `cargo clippy --all-features
--all-targets -- -D warnings`; `cargo fmt --all -- --check`;
`RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --all-features`; parity;
`bench_diff --validate-models` for anything model-adjacent; a fuzz soak on
the changed surface. A bug fix ships with the reproducer as a test.

## Working knowledge that cost real time

**Multi-agent git (the important part).** The primary tree is usually dirty
with other agents' in-flight work. Never `stash`/`restore`/`checkout --`
there. Workflow that worked: do the work in a `git worktree add --detach`;
merge current `main` in; verify the *merged* tree; land with
`git update-ref refs/heads/main <merge>`; then sync the primary: `git
restore --source=HEAD --staged --worktree` **only your files** that show as
stale (`M `/`D ` in status), and for any file where your landed diff
overlaps another agent's live edits, apply your delta as a `patch -p1` on
top of their state so their `git diff` keeps showing only their work.
**Re-check `git log main` immediately before `update-ref`** — another agent
landing in the window between your merge and your ref-write means you would
rewind `main` past their commit (this happened once; caught in seconds only
because the check ran; fixed by merging their commit and re-pointing).
After landing: copy the release binary to `precompile/<sha>/`, then remove
your worktree and branch the same session.

**Disk.** `/media/data` runs at 97–100%. Long builds die with linker bus
errors and — worse — **a disk-full mid-write can silently truncate a source
file** (it happened to `builder.rs`; symptom: impossible syntax errors
hundreds of lines from your edit; recovery: `git checkout` the file and
re-graft your diff). Mitigate: `CARGO_INCREMENTAL=0` always;
`CARGO_PROFILE_DEV_DEBUG=0` for test builds; `rm -rf target/debug/incremental`
between phases; symlink the corpora (`smt-lib`, `satcomp2024/2025`, `satlib`)
into fresh worktrees or every corpus test fails with `[corpus-missing]`.

**nextest runs every test as its own process.** In-process `RwLock` guards
around temp-dir scans guard nothing under it; filter scratch files by the
PID embedded in their name (see `interpolate.rs`'s scan). Parallel full-suite
runs also race on temp files — check whether a "new" flake is a race before
chasing a logic bug (the interpolate flake was one).

**Debug prints.** Every `NIXIE_DBG_GATE`-style eprintln added while digging
was removed before landing — grep for your marker before you commit. Keep
the instrumentation discipline: print *several views of the same state*
(trail vs model vs raw codes vs polarity) — the Rodin root-cause only
broke open when four plausible hypotheses had to face one probe.

## Patterns that fixed things (use them again)

* **Checked + exact-retry + narrow**: i64 checked arithmetic on the hot
  path; on overflow, recompute *that one derivation* in `BigRational` and
  narrow the final (intermediates legitimately overflow while finals fit —
  denominators cancel); decline to the honest-`Unknown` channel only when
  the final itself doesn't fit. Sound, and it preserves completeness
  everywhere the final fits.
* **No silent fallthrough**: every decline must reach an honesty gate, not
  vanish. When you make a parse/propagation fail *conditionally*, verify
  the failure is **visible** to the gate that reports it (item 9's bug was
  a synthesis registered after the scan that should have collected it —
  a false `sat` that existed only because the check ordering was wrong).
* **Per-layer fixes with per-layer regressions**: one fix can mask another
  defect in the same path; each of the 17 items has its own test, so an
  outer fix cannot hide an inner one again.
* **The soundness oracle stack**: debug-panic sweep (unchecked arithmetic),
  differential with model validation (wrong verdicts and wrong witnesses),
  parity (everything). Run the cheapest one that covers your change; run
  all of them before landing.

## Where things live

* The arc's memory: `docs/studies/2026-09-13-lia-wide-literal-arithmetic.md`
  (items 1–17, each with its layers and evidence).
* Methods: `docs/BENCHMARKING.md` (heuristic changes), `bench/differential/
  METHODOLOGY.md`, `bench/z3_parity/METHODOLOGY.md`.
* Binaries: `precompile/<sha>/nixie` per landed commit (never commit them).
* The other agents are active and productive — SAT (elimination/watches),
  TLA+ (set/function theory, BMC), mbqi, strings. Land only your files;
  read their commit messages; their studies under `docs/studies/` are the
  state of their fronts.

The one-sentence version: **the arithmetic arc is closed and verified;
the SAT-core snapshot divergence is the live soundness thread (reproducer
waiting), the wide-LP is the named milestone (benchmarking-gated), and the
debug-panic sweep is the cheapest test you can run before you trust any
change — run it.**
