# Handoff: the arithmetic arc, items 51/54 and the wide-LP endgame (2026-09-17)

**Read `AGENTS.md` first — it is canonical.** This handoff continues
`docs/studies/2026-09-15-arithmetic-arc-continuation-handoff.md` (read
that one too). The arc's memory is
`docs/studies/2026-09-13-lia-wide-literal-arithmetic.md` — **items
1–54**; read the item list before touching arithmetic. Where they
disagree, the guide wins.

## What this stretch was

The 09-15 handoff's items 1–5, executed across four sessions — plus
every wrong verdict the differentials found along the way. The
wrong-verdict classes came in layers, each one found only after the
previous was closed: the fabricated wide-basic value (false `sat`), the
wide-row narrow-back staleness (false `unsat`), the double-counted
exact retry (both), the strict-atom one-sided endpoint (false `unsat`),
the mid-`make_feasible` staleness (false `unsat`) — and finally item
54: a wrong row FORM produced by `intern_row`'s basic-substitution,
which is the live false `unsat` on `main` right now and the top open
item.

Landed this stretch (all with binaries under `precompile/<sha>/`):
`b110c2b8`/`d1dc7f0d` (wide-value honesty, items 41–45),
`96e95fb7` (study correction), `0d3d2378` (the exact-retry
double-count, item 46 — pre-existing, exposed by any enriched bound
state), `24cb0567`/`83b985a6` (the wide-row propagation, slice 6,
items 47–48), `8f313c42`/`02f6ca58` (the value-overflow migration —
**f1, the original false-`unsat` reproducer, now decides `sat`**,
items 49–50), `7b914516`/`281ef5ed` (the mid-loop staleness guard,
item 52), `ac68eed9`/`89fe767b` (item 54's diagnosis).

## Open items, in priority order

1. **Item 54 — the wrong `intern_row` substitution (a live false
   `unsat` on `main`)**. The reproducer (z3: `sat`, nixie: `unsat`):
   a QF_LIA three-disjunct nested `not(or(…mod/div…))` with
   `(= (* -1 yi) -4611686018427387904)` pinned; bytes in study item
   51, minimized to any-three-disjunct form. The mechanism is FULLY
   decoded (study item 54): atom 72's row (`1 − mod(8−xi,3)`) is
   interned by `assert_lt` as `(1 − s22_axiom)/52` — a rescaling of
   the DIVISION-AXIOM row instead of the mod row (exact arithmetic at
   z3's model: 1/52 vs 1). Everything downstream (the bound, the
   conflict, the `[division-axiom]`-only core) follows mechanically
   from that one wrong form. **The next probe is surgical**: at
   s135's intern (backtrace `assert_lt → cached_row_slack →
   intern_row`), dump the PRE-substitution expr and every tableau row
   the substitution consumed (s7's row and the xi-rows it chains
   through) — one of them is already corrupted. The honest-derivation
   oracle for any candidate fix: `{atom 12, atom 72}` is z3-
   satisfiable, so no sound derivation may refute it. Attribution:
   introduced by `0d3d2378` (the propagation landing made the wrong
   row's bound load-bearing); the substitution defect itself is older.
2. **The ndir2/pinned gates (env-gated, default off)**:
   `NIXIE_S6_PINNED=1` (pinned-basic narrow direction-2) closes the
   mixed-magnitude LRA unsat twin AND makes f1 decide `sat` — but
   deflects the chain-sat twin's pivot trajectory into the
   violated-unrepairable wide-row wall (study item 50's site-1950
   analysis). Default-on needs wide-driven repair steps (a
   pivot-analogue through wide rows; Z3 has no such wall because it
   computes exactly everywhere).
3. **B&B budget exhaustion** on hard disjunctive LIA+div/mod — pure
   search capacity; heuristic rules apply (matched nulls, ≥10 seeds,
   `docs/BENCHMARKING.md` first).
4. **Corpus residuals**: QF_BV/sage and three other families are
   still absent from the returned corpus — the `wisas_xs_8_13` pair
   fails on every parent (fixture-level `Unknown`, NOT this arc's;
   see the other agents' handoffs under `docs/handovers/`). Rerun the
   debug-panic sweep over `smt-lib/non-incremental` when the missing
   families return.

## The standing verdict map (know it before you measure)

* `fi1` (item 51): **`unsat`, WRONG** (z3: sat) — the open item.
* `f1` (`docs/studies/assets/2026-09-15/false-unsat-f1.smt2`): `sat`
  ✓ (decided by the value-overflow migration; pinned by
  `stale_assignment_never_drives_false_unsat`, strengthened to
  `assert_eq!(…, "sat")`).
* The chain-sat twin, the wcancel shape, the LIA mixed-magnitude twin:
  all correct (regressions in
  `nixie-solver/tests/arith_wide_literal_regressions.rs` — 29 tests).
* The LRA mixed-magnitude unsat twin: honest `unknown` by default,
  `unsat` (correct) under `NIXIE_S6_PINNED=1`.

## Tools you inherit (all in-repo)

* `bench/differential/wide_fuzz.py` — the wide-literal differential
  (found four wrong-verdict classes; fresh seeds are the cheapest
  soundness oracle — run it over ANYTHING you touch).
* `bench/differential/mixed_fuzz.py` — the mixed-arith surface (found
  item 51).
* `bench/differential/debug_panic_sweep.py` — every abort is an
  unchecked fixed-width site.
* `./bench/z3_parity/run_parity.sh` — the parity gate (z3 4.16.0;
  record the version). Current: 176/177 correct, 0 disagreements.
* **The corner auditor** (landed, env-gated `NIXIE_S6_AUDIT=1`,
  debug builds): recomputes every wide-row propagation derivation by
  full corner enumeration — an independent check of the endpoint
  arithmetic. It caught two real bugs; run it over any derivation
  change.
* The probe set that decoded item 54 (all stripped from the tree; the
  shapes are in the study): term-identity dumps (`term_to_var` +
  reason table via small `debug_*` getters), row-history logging
  (INTERN/PIVOT-COMMIT/WIDE-UPD with `was_wide`), set-bound
  backtraces, and **exact-arithmetic validation of any suspect row at
  z3's model** — the instrument that separated "unsound row" from
  "unsound bound" in one run.

## The verification bar (unchanged)

`cargo build --all-features`; `cargo nextest run --workspace
--all-features` (~4.5k tests; the `wisas` pair is the standing
non-corpus failure — pre-existing, another front's); doc tests;
`cargo clippy --all-features --all-targets -- -D warnings`; `cargo fmt
--all -- --check`; `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps
--all-features`; parity; the wide + mixed differentials (≥3 fresh
seeds each); the debug-panic sweep for anything arithmetic. A bug fix
ships with the reproducer as a test — and when the fix lands, check
whether the reproducer should be pinned to its TRUE verdict (f1 went
`ne unsat` → `eq sat` when the migration decided it).

## Working knowledge that cost real time

**A wrong verdict's first plausible cause is a symptom.** This arc
peeled five layers off one reproducer family before reaching the
substitution defect. The order that worked: (1) get the exact z3 model
and validate every suspect row/bound against it by exact arithmetic —
this alone killed two wrong hypotheses; (2) map simplex vars to terms
EARLY (the `debug_term_var_pairs`-style dump — guessing identities
wastes hours); (3) log row HISTORY, not just row state (the
`was_wide=true` flag on one commit was the thread that unraveled
items 49 and 54); (4) backtrace-forced-capture at bound stores
answers "whose assertion is this" in one run.

**Substituted rows are the arc's recurring crime scene.** The
narrow-back staleness (item 43), the wide-update corruption chain
(item 54's s135), and the provenance question (a substituted row's
justification is invisible to conflict explanations — the reason
cores fold to single atoms) are all the same structural gap. Any fix
in this area should consider whether rows need to carry their
defining-reason provenance; that is also the design question behind
open item 2's repair steps.

**Enriched bound state activates latent defects.** The propagation
landing (0d3d2378) introduced no new arithmetic — it made
pre-existing wrong rows load-bearing. Expect the same when you turn on
the pinned gate or add any propagation: the differential must run
before AND after, and attribution needs the precompile binaries
(`d1dc7f0d` is the pre-propagation control).

**Infrastructure traps**: the shared `target/` was deleted once
mid-session (recreate it — every worktree symlinks it); merges can
leave stale-mtime poison builds (`touch` the merged sources and
rebuild); `git worktree remove --force` + scratch cleanup
same-session; disk runs 85–95%.

**Multi-agent git** — unchanged: worktree per change, merge `main`,
re-check `main`'s tip immediately before `update-ref`, sync only your
files into the primary, `precompile/<sha>/` for every landing. The
other fronts are active (sets rel-compounds, mbqi, SAT/CSR, TLA,
FF); read `docs/handovers/` — it is their state.

## Where things live

* The arc's memory: `docs/studies/2026-09-13-lia-wide-literal-arithmetic.md`
  (items 1–54, each with layers and evidence).
* The slice-6 negative-result study (rounds 1–3, the auditor
  methodology): `docs/studies/2026-09-15-wide-row-bound-propagation-negative-result.md`.
* The fi1 reproducer bytes: study item 51 (inline).
* Wide regressions (29): `nixie-solver/tests/arith_wide_literal_regressions.rs`.
* Methods: `docs/BENCHMARKING.md`, `bench/differential/METHODOLOGY.md`,
  `bench/z3_parity/METHODOLOGY.md`.

The one-sentence version: **the wrong-verdict debt is one decoded
substitution away from paid — item 54's probe is surgical, the oracle
(`{12,72}` is satisfiable) is standing, and the probe set that got
here is written down; after that, the wide store's remaining work is
the repair-step design and the provenance question, both scoped.**
