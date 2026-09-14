# Handoff: the arithmetic-arc continuation (2026-09-15)

**Read `AGENTS.md` first — it is canonical.** This handoff continues
`docs/studies/2026-09-14-arithmetic-arc-handoff.md` (read that one too —
its working-knowledge section still applies). Where they disagree, the
guide wins. The arc's memory is
`docs/studies/2026-09-13-lia-wide-literal-arithmetic.md` — **items 1–40**;
read the item list before touching arithmetic.

## What this arc was

The 09-14 handoff's open items 1–3, executed: the SAT-core snapshot
divergence (closed: elimination-*reintroduction*, items 18–20), symbolic
real division `(/ x y)` (closed: guarded defining clause through the NL
dispatcher, items 21–24), and the wide-LP wall — five landed slices
(intermediate-overflow recovery, the wide-row side table, positive
rescaling, the exact-coefficient parse retry, dual-width entering rows,
items 25–37) plus one **unlanded** slice (wide-row bound propagation — see
open items). Mid-arc, the wide differential found a **false `unsat`** the
arc itself had introduced (slice 2); it lived on `main` for six landings,
was root-caused to the lying `assignment_current` flag, and is fixed
(items 38–40). Every landing shipped with the full battery green except
the standing `[corpus-missing]` set (the external corpora are still
absent — see below).

Landed this arc: `33273991` (reintroduction), `df13616e` (real division),
`d673f786`/`5bda924d`/`e433bf6e`/`6ccfc6e1`/`47e71bb3` (wide-LP slices
1–5), `3f4227b2` (the false-`unsat` fix). Binaries under
`precompile/<sha>/`.

## Open items, in priority order

1. **One unchecked release-wrap site, proven live** (`simplex/mod.rs`,
   `on_nonbasic_bound_change`): `self.assignment[bi] += delta * c;` —
   unchecked `DeltaRational` ops. The debug-panic sweep fired here
   (`mul_r64_fast` overflow via `note_bound_change`) the moment the
   unlanded propagation set derived bounds on wide-coefficient rows; the
   fix shape is the item-14 pattern (checked, defer via
   `assignment_current = false`), verified in the abandoned worktree. One
   small commit; land it before touching anything else in the simplex.
2. **The unlanded slice-6: wide-row bound propagation** — exact
   both-direction bound derivations through wide rows, exact crossing
   tests (never on weakened forms), weakened-integer storage, bounded
   fixpoint. Sound on every oracle when built; NOT landed because it was
   built on top of the then-unexplained f1 false `unsat`. That blocker is
   gone. The full rebuild description is in the study (Continuation 13's
   record + the session notes it points to); the two `narrow_pair`
   lessons matter most: cross on the EXACT value (integer-rounded bounds
   erase crossings inside their unit interval — the `−1/2^63` class),
   weaken only for STORAGE; and a `2^63`-quotient can blow up the DELTA
   component of a derived strict bound while the real part fits — weaken
   `floor/ceil ± 1, delta=0` (always implied, sound).
3. **Wide-LP residuals** (all pinned by regression, all honest
   `unknown`): astronomically-prime rows (no representable scale — the
   `large_prime_constant_rows_stay_honest` pin); the mixed-magnitude unsat
   twin (needs item 2's propagation chained — the analysis showed the
   derivation closes to `v1 ≥ −1/2^63` and then blocks on the `>0` bound
   not being visible on any row the propagation sees); mid-search
   pivot-site width beyond the wide store.
4. **B&B budget exhaustion** (the 09-14 handoff's item 4) — unchanged,
   heuristic-gated, corpus-blocked.
5. **`bench_diff --validate-models`** — still owed from the item-17
   landing; corpus-blocked (see below).

## The corpora are still gone

`smt-lib/non-incremental` (and `satlib`, `satcomp2024/2025`) were removed
from the shared tree mid-2026-09-15 by an outside intervention and are
still empty at this writing. Consequences: every corpus test fails with
`[corpus-missing]` (currently 14–15 failures — **do not chase them as
logic bugs**), `bench_diff` and the wide-LP canary's named reproducer
(QF_NIA/VeryMax) are unrunnable, and the handoff-4 B&B work has no
benchmark surface. The synthetic wall corpus (chain/cancellation/
uniform/mixed shapes) is in the study and the regression tests — it
replaced the corpus for the arc. When the corpora return: rerun
`bench_diff --validate-models`, the debug-panic sweep over
`smt-lib/non-incremental` (the stratified sample), and the VeryMax
canary.

## Tools you inherit (all in-repo now)

* `bench/differential/wide_fuzz.py` — **the wide-literal differential**
  (NEW with this handoff; it had lived only in `/tmp` and was deleted
  each session — that gap is closed). Coefficients at/past the `i64`
  boundary, odd-prime relief shapes, a `2^100`-scale prime (the honest
  wall), `not/and` nesting over div/mod (the f1 shape — keep it), model
  validation on nixie-sat-vs-z3-unknown splits. **z3-error-aware**: z3's
  `QF_LRA` front end errors on `(- 0 2^63)`-shaped literals while its
  no-logic mode decides them correctly — errors are non-evidence.
* `bench/differential/mixed_fuzz.py` — the mixed-arith surface (found
  items 5, 10, 9-gate within minutes; extend the generator, not the
  seeds).
* `bench/differential/debug_panic_sweep.py` — every abort is an unchecked
  fixed-width site. Run it over any theory you touch.
* `./bench/z3_parity/run_parity.sh` — the parity gate (z3 4.16.0; record
  the version).

## The verification bar (unchanged)

`cargo build --all-features`; `cargo nextest run --workspace --all-features`
(~4.4k tests + the standing `[corpus-missing]` set); doc tests; `cargo
clippy --all-features --all-targets -- -D warnings` (note: other agents'
freshly-landed code has carried clippy debt lately — verify YOUR crates
in isolation before treating the whole-tree gate as yours);
`cargo fmt --all -- --check`; `RUSTDOCFLAGS="-D warnings" cargo doc
--no-deps --all-features`; parity; the wide + mixed differentials for
anything arithmetic; a fuzz soak on the changed surface; the debug-panic
sweep. A bug fix ships with the reproducer as a test.

## Working knowledge that cost real time

**The f1 post-mortem is the load-bearing lesson set (study item 40).**
(a) *Bisect by binary, not by commit adjacency* — the first attribution
was wrong by one slice; four `precompile` builds of the window's commits
pinned it. Build bisect binaries in throwaway worktrees, cache them in
`precompile/<sha>/`, delete the worktrees same-session. (b) *Shape
coverage beats seed count* — the false `unsat` survived three
differential extensions; the fourth's `not/and` nesting over div/mod
found it in one run. When a class of input shape is plausible, add the
shape. (c) *The debug canaries are usually right* — the delta-vs-reeval
assert (the old item-15 canary) pointed at the lying flag from day one;
the reproducer just needed to get small.

**Flags that gate consumers must be set by the producer's outcome, not
by the consumer's optimism.** The `assignment_current` bug was four guard
sites forcing `= true` after a re-derivation that could fail. The
pattern to hold: a "state is consistent" flag may only be set through
the one code path that actually makes it consistent. Audit neighboring
flags the same way when you touch one.

**Instrumentation discipline that worked** (all markers removed before
landing — grep for yours): print *several views of the same state*
(assignment vs row-content vs the writer's identity vs the consumer's
read); number the passes (`static AtomicU64` counter) so "which pass
skipped row 10" is answerable; put the probe at the TOP of loops, not
only at write sites — the f1 break was found by a probe that proved a
loop *never reached* an entry; backtrace-force-capture at suspicious
writes answers "whose pass is this" in one run.

**Rejected design, do not retry without redesign**: the pivot-site
linking row (`var = σ·t` between two basic variables) breaks the
"rows reference only nonbasics" invariant — `find_pivot_col` offered a
basic variable as entering and the debug column checker caught it. The
wide-entering-row approach that DID land is the sound alternative.

**z3 quirks as comparator traps**: the `QF_LRA` error-on-wide-literals
above; and always cross-check a z3 "disagreement" against z3's own error
output before believing the disagreement.

**Multi-agent git** — unchanged from the 09-14 handoff (worktree per
change, merge main, `update-ref` only after re-checking main's tip,
sync only your files, `precompile/<sha>/`, clean up same-session). The
window between "merge" and "update-ref" has caught two more landings
since — the double-check is not optional. Disk: /media/data runs
95–97%; `CARGO_INCREMENTAL=0` always; `CARGO_PROFILE_DEV_DEBUG=0` for
test builds; `rm -rf target/debug/incremental` between phases.

## Where things live

* The arc's memory: `docs/studies/2026-09-13-lia-wide-literal-arithmetic.md`
  (items 1–40, each with layers and evidence).
* The f1 reproducer: `docs/studies/assets/2026-09-15/false-unsat-f1.smt2`
  (2 variables; z3: sat; pinned never-`unsat` by
  `stale_assignment_never_drives_false_unsat`).
* Wide regressions: `nixie-solver/tests/arith_wide_literal_regressions.rs`
  (23 tests — the chain/cancellation/uniform/mixed/prime families and the
  honesty pins).
* Methods: `docs/BENCHMARKING.md`, `bench/differential/METHODOLOGY.md`,
  `bench/z3_parity/METHODOLOGY.md`.
* The other agents are active and productive — SAT (CSR migration),
  TLA/BMC, mbqi/quantifiers, FF, sets. Land only your files; read their
  commit messages; their studies under `docs/studies/` are the state of
  their fronts.

The one-sentence version: **the arc's wrong-verdict debt is paid (both
directions — the f1 false `unsat` closed at the root, every wrong-verdict
class has a pinned regression); the live thread is one small unchecked
site, then the unlanded propagation slice whose rebuild description and
two narrowing lessons are in the study; and the wide differential is
finally in-repo — run it over anything you touch.**
