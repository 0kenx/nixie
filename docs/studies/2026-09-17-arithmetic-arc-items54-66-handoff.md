# Handoff: the arithmetic arc, items 54–66 — the wrong-verdict debt paid, the wide endgame landed (2026-09-17)

**Read `AGENTS.md` first — it is canonical.** This handoff continues
`docs/studies/2026-09-17-arithmetic-arc-item54-handoff.md` (read that
one too; its probe methodology section still applies). The arc's memory
is `docs/studies/2026-09-13-lia-wide-literal-arithmetic.md` — **items
1–66**; read the item list before touching arithmetic. Where they
disagree, the guide wins.

## What this stretch was

The item-54 handoff's open items, executed across five sessions — item
54 itself, both `24cb0567` casualties, the wide-LP endgame, the gap
survey and three of its four classes, and the provenance question
answered. Every wrong verdict the differentials found in the window is
closed with a root-cause fix and a regression; the remaining gap is
honest `unknown` on documented capacity walls.

Landed this stretch (binaries under `precompile/<sha>/`):
`3ed26a71` (item 54's fix re-landed: rescaled slack integrality +
`i64::MIN` honest declines + optimizer hardening), `d256003b` (item 58:
the repair pivot's snap), `70e705e9` (item 59: the wide-driven repair
step), `bc8254bc` (item 60: the pop re-snap + strengthened definitional
invariant + the provenance answer), `152e8326` (item 61: pinned
direction-2 default-ON, scoped to wide states), `14d2057a` (item 62:
the recfun boundary-escape probe), `f0e00b12` (item 63: wide-value
publication), `93126df2` (item 64: the blocking downgrade scoped),
`d1e70d5f` (item 65: the B&B dead-leaf backtrack), `3817f3ff` (item 66:
the unbounded-side refutation bail + exact violated-side read).

## The verdict map (know it before you measure)

* `f1` and `fi1` bytes live under `docs/studies/assets/`: f1 `sat` ✓,
  fi1 honest `unknown` (z3 `sat`; the `11·xi=7`-class refutations land
  but fi1's own width wall stands).
* `wisas_xs_8_13` `unsat` ✓ deterministic ×3; the recfun reproducer
  `sat (k=3)` in ~1 s. Both `24cb0567` casualties closed.
* The mixed-fuzz gap (nixie `unknown` where z3 decides, 3×600-instance
  survey, seeds 20261000–02): **~177/1800 ≈ 9.8%**, from 210 at the
  survey's start. Split: ~170 SAT-side, 7 UNSAT-side.
* The 7 UNSAT-side residuals, site-mapped: B&B node budget (1), LP
  pivot budget (1), the honest `i64::MIN` row-assert corner (4), one
  outer. All honest declines.
* The SAT-side is the div/mod disjunctive search-capacity class — the
  campaign-shaped item below.

## Open items, in priority order

1. **The SAT-side gap campaign (~170 instances)**. This is search
   capacity, not wrong verdicts — heuristic rules apply in full
   (matched nulls, ≥10 seeds, `docs/BENCHMARKING.md` FIRST). The
   shapes: `not(or …)` nesting over `div`/`mod` with wide constants
   (60% of the gap), LIRA mixes. Entry point: the survey script is
   reconstructible from `bench/differential/mixed_fuzz.py`'s generator
   plus a capture loop that keeps `nixie=unknown ∧ z3-decisive`
   instances (the seeds 20261000–02 reproduce ~181 members; a fresh
   seed set is one line). Probe map for decline sites: env-gated
   prints at every `return Ok(TheoryResult::Unknown)` in
   `solver.rs` and every `self.resource_limit = true` in
   `simplex/mod.rs` — the sites are stable, the line numbers drift.
2. **NDIR2 default-on.** `NIXIE_S6_NDIR2=1` still deflects the fi1
   regression into a 180 s timeout (its deflection cost persists,
   post-repair-step). The general form needs the same scoping thought the
   pinned form got (item 61): measure where its derivations pay before
   unconditioning it. `NIXIE_S6_PINNED=0` disables the landed default.
3. **B&B/pivot budget residuals** (2 instances): pure capacity; the
   node/pivot budget constants are `LIA_MAX_NODES`/`max_pivots` — any
   bump is a heuristic change (campaign rules).
4. **The `i64::MIN` corner's decidability** (4 instances): the honest
   decline is correct; the flip design (build the row as
   `rhs − lhs ≥ 0` at the corner) is recorded in study item 56 — it
   moves the overflow into the coefficient negations and cannot serve
   the strict/δ encodings; measure before building.

## The provenance question — CLOSED, do not rebuild it

Item 60 answered it: rows are DEFINITIONS (constraints live only in
bounds with reason sets); substitution through a basic consumes only the
definitional equation, so cores through substituted rows are complete
by construction. The three properties the argument rests on are each
mechanically enforced: row equation-preservation (the strengthened
`debug_verify_invariant`, wired at `check`'s convergence point as a
`debug_assert` — it runs in EVERY debug test), truthful integrality
(`RowInternMode`), full bound justification (reason-resolution assert +
the corner auditor). Item 54's single-atom core was complete over a
FABRICATED constraint, not a provenance gap. A provenance-carrying
redesign is unnecessary.

## Tools you inherit (all in-repo)

* `bench/differential/wide_fuzz.py` / `mixed_fuzz.py` — the standing
  soundness oracles; run over ANYTHING you touch (≥3 fresh seeds each;
  the arc's rule: extend the generator's SHAPES, not its seeds).
* `bench/differential/debug_panic_sweep.py` — every abort is an
  unchecked fixed-width site; stratify over
  `/media/data/proj/nixie/smt-lib/non-incremental` when the corpora are
  present.
* `./bench/z3_parity/run_parity.sh` (z3 4.16.0; record the version) and
  `bench/perf_gate/run_gate.sh` (`GATE_BASELINE` points at
  `precompile/$(cat bench/perf_gate/BASELINE)/nixie` — worktrees have
  no `precompile/`, set it explicitly).
* The gap survey (capture-loop variant of `mixed_fuzz.py`'s generator,
  seeds 20261000–02): the cheapest completeness telescope; rerun on the
  same seeds to attribute, on fresh seeds to hunt.
* The strengthened `debug_verify_invariant` (rows-reference-only-
  nonbasics; entry==row-eval; wide basics certified against their EXACT
  evaluation): a silent debug suite IS a soundness pass; a firing one
  names the wrong-verdict site directly.

## The verification bar (unchanged, plus one)

`cargo build --all-features`; `cargo nextest run --workspace
--all-features` (expect ~11.9k tests; the only standing failure is the
`nixie-testcorpus` env self-test under `NIXIE_CORPUS_MISSING=skip` —
self-inflicted, skip it; load >70 turns the documented slow tests into
cap-timeouts — re-run those in isolation before believing a failure);
doc tests; `cargo clippy --all-features --all-targets -- -D warnings`;
`cargo fmt --all -- --check`; `RUSTDOCFLAGS="-D warnings" cargo doc
--no-deps --all-features`; parity; the wide + mixed differentials; the
debug-panic sweep for anything arithmetic; **the perf gate for anything
touching solving**. A bug fix ships with the reproducer as a test; when
the verdict changes, re-pin it (f1 went `ne unsat` → `eq sat` this way).

## Working knowledge that cost real time

**A green test is not a correct model.** Item 63's first cut printed
the FLOOR of the exact rational (`mk_div` instead of `mk_rdiv`) — the
verdict was right, the test was green, and only validating the printed
model against z3 caught it. The round-trip discipline: a model value
must re-parse to the same value (`(/ n d)` not `(div n d)`) — the
printer now renders `Div` by SORT for exactly this reason.

**The unit-test revert-check needs the whole fix.** Two regressions
this stretch passed with only part of the change stashed (the second
layer closed the same contract through a different route). The survey
delta on fixed seeds is the load-bearing attribution; unit pins are the
contract, not the proof.

**A stale wide entry lies in BOTH directions.** Items 66's second half:
the repair read the stored entry to infer the violated side — the entry
is stale-by-design for wide basics, and the repair searched the
reversed direction. Every consumer of `assignment[]` near wide state
must read the EXACT evaluation (`eval_big_raw` / `wide_basic_value_exact`).

**Infrastructure traps, this stretch's crop**: the shared `target/` was
deleted twice more (recreate; worktrees symlink it); /media/data hit
100% twice (another agent's 140G `/tmp` worktree filled the ROOT disk
once — check `df -h / /media/data` before blaming your own /tmp; run
fuzzers with `TMPDIR` off a full disk); a mid-write ENOSPC TRUNCATED a
study append — verify the doc tail (`tail -3`, grep for the section
marker) after any failed `cat >>`; `git update-ref` under contention
fails on `main.lock` — wait and retry after re-checking the tip; my
commits were re-landed once by another agent's merge (content on main
wins, don't fight the hashes).

## Where things live

* The arc's memory: `docs/studies/2026-09-13-lia-wide-literal-arithmetic.md`
  (items 1–66, continuations 22–31 are this stretch's).
* Reproducers: `docs/studies/assets/2026-09-15/false-unsat-f1.smt2`,
  `docs/studies/assets/2026-09-17/false-unsat-fi1.smt2`; the recfun
  script is inline in study item 62 and
  `nixie-solver/tests/recfun_e2e.rs`; the gap instances are
  regenerable from the survey seeds (not persisted — they are the
  generator's output, not artifacts).
* Regressions this stretch: `nixie-solver/tests/
  arith_wide_literal_regressions.rs` (36 tests now — the rescaled-slack,
  `i64::MIN`, wide-publication, dead-leaf classes) and
  `nixie-theories/src/arithmetic/simplex/tests.rs` (the snap, repair,
  wide-refutation, pop-re-snap units).
* Methods: `docs/BENCHMARKING.md`, `bench/differential/METHODOLOGY.md`,
  `bench/z3_parity/METHODOLOGY.md`.

The one-sentence version: **every wrong verdict and both `24cb0567`
casualties are closed at the root with the full battery green; the
remaining work is one benchmark-disciplined capacity campaign on the
SAT-side div/mod gap, one scoped NDIR2 measurement, and the honest
residuals the study maps — and the instruments to keep it honest (the
strengthened invariant, the survey, the differentials) are all wired.**
