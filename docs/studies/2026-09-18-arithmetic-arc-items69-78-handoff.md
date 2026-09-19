# Handoff: the arithmetic arc, items 69–78 — the wrong-verdict ledger emptied, the width wall breached at intern time (2026-09-18)

**Read `AGENTS.md` first — it is canonical.** This handoff continues the
arithmetic arc whose memory is
`docs/studies/2026-09-13-lia-wide-literal-arithmetic.md` — **items 1–78**;
read the item list before touching arithmetic. The predecessor handoffs
(items 54–66, then the item-69 fence in continuation 32) describe the
machinery this stretch built on. Where they disagree, the study wins.

## What this stretch was

Five sessions closing every wrong verdict the differentials found, plus
the capacity campaign's first landing. Items 69–70 (the seed-20261102
false `unsat`), 74 (the seed-20261130 false `unsat`), 75 (strict atoms
join the rehome), 77 (weak-side bound writes never made), 78 (the
intern-time width wall). Landed: `740c16bd`, `d75fa881`, `010f0e7e`,
`f4415a0e` (plus docs-only `267391b3`, `d1e164d4`; binaries under
`precompile/<sha>/`). The wrong-verdict ledger for the mixed-fuzz family
is **empty**: 13+ fresh mixed seeds ×400, the 1 800-instance fixed-seed
sample, and the gap survey all clean at the final binary.

## The verdict map (know it before you measure)

* The seed-20261102 core + full and the seed-20261130 shrunk instance
  all answer `sat`, matching z3 (models hand-verified). `f1` `sat`, `fi1`
  honest `unknown` (its width wall stands — see the item-78 note: the
  wall MOVED, it did not fall).
* Gap survey on the fixed seeds (20261000–02 ×600) at `f4415a0e`:
  **114 members**, every one honest `unknown`. Attribution after item 78:
  **A3 26** (B&B `FracVar::Underivable` — branch bounds leave `i64`),
  **A2 24** (B&B node/depth budgets), **S3 16** (wide-repair NOCOL),
  A5 4, A6 1, plus tails. The S1/S2 intern-time sites are GONE.
* `parity_infeasibility_four_free_vars` answers honest `unknown`
  (the pin demands ≠ `sat`); the rehome tests take 8 s–625 s (the
  full-instance one is load-capped at 180 s under parallel test runs —
  re-run in isolation before believing a failure).

## Open items, in priority order

1. **The B&B width wall (A3, 26 members)** — the campaign's next slice.
   `find_fractional_int_var` returns `FracVar::Underivable` when the
   branch bounds (`floor`/`ceil` of the exact value) leave `i64`; item
   42's `wide_floor_ceil_big` recovers "the recoverable". The named
   project is **dual-width branch bounds**: represent the branch bound in
   the wide side table exactly and branch on it without narrowing. Entry
   point: the `A3` site (the `Underivable` return in
   `lia_branch_and_bound`'s dive loop); the decline-site probe recipe
   below names the exact arm.
2. **The B&B budget residuals (A2, 24 members)** — `LIA_MAX_NODES` /
   `LIA_MAX_DEPTH` burns. Any bump is a heuristic change: matched nulls,
   ≥10 seeds, `docs/BENCHMARKING.md` FIRST. Check whether item 1's fix
   shrinks this class first (they overlap heavily).
3. **S3 (wide-repair NOCOL, 16 members)** — `find_wide_pivot_col` finds
   no eligible entering column for a violated wide row whose achievable
   range overlaps its window. The repair-eligibility rule is the design
   question; the convergence loop (`MAX_WIDE_REPAIRS`) is the budget.
4. **Item 71's open channel question** (understanding, not a defect):
   WHY is the rehome's re-assertion load-bearing when the stranded slack
   stays equation-tied (5–9 narrow refs, `old_val == form_val` at strand
   time)? The effect runs through what re-assertion FEEDS (re-check
   cadence, `int_equalities`, B&B's view). The forensics pattern that
   answered 69–74 (reason-side tracing, below) is the tool.
5. **A strict-stranding reproducer** for the item-75 extension (the
   strict rehome is screened by differentials only; no targeted
   reproducer exists). Cheap insurance against regressions in the
   `Lt`/`Gt` arms.

## The defect classes this stretch closed (do not re-derive them)

* **Bound values never cross the stranding boundary.** The rehome
  re-asserts only the ATOM's own `∘ 0` bound (scale-invariant), with a
  live reason id — never the old slack's current VALUES (item 69/70:
  `(20/7)·old = 7/20` fabricated, singleton conflict blamed one Euclidean
  axiom, learned unit `¬axiom`, false `unsat`). `copy_bounds` is deleted.
* **Endpoint reasons pick their own SIDE.** On an EQUAL bound pair (a
  pin whose sides carry different justifications), the `want_min ==
  a_first` tie-break cited the opposite side's reasons (item 74: `hi(v)=0`
  attributed to the `(< 2 X)` atom when only the `(= 2 X)` pin justified
  it). Pick by side; inverted pairs decline first (item 73, the parallel
  session's half).
* **Weak-side writes are never made** (item 77): `assert_eq` and the
  rehome skip a pin's weak side when a live tighter bound subsumes it.
  The GCD-infeasibility witness KEEPS its live-column placement — the
  fresh-var redesign was built, passed unit targets, and flipped the
  item-69 core back to false `unsat` (a unit `¬equality` collapses
  against a unit axiom). **Reverted; do not retry without richer
  conflict reasons.**
* **The intern path was the width wall's last global decline** (item 78):
  S1/S2 set only the staleness flag; `update_assignment` migrates the row
  to the wide store; convergence classifies it exactly.

## Tools you inherit (all in-repo, all env-gated)

* **`NIXIE_BOUND_TRIPWIRE=1`** — eprintln probe at every weakening
  live-bound write (`set_{lower,upper}_delta`). Found items 77's sites;
  fires today only on the raw-API loosen contract (its own unit test).
  Any new hit on a production path is a silent-constraint-drop.
* **The decline-site attribution recipe** — env-gated prints at the
  statement-position `TheoryResult::Unknown` returns (solver.rs) and bare
  `resource_limit = true` sites (simplex), run over the survey members,
  counted per site. Rebuild the tags when lines drift; keep tags to
  statement positions or the build breaks (match arms).
* **The conflict-set polarity pipeline** (the 69/74 decoder): print each
  `conflict_from_terms` set with the printer + current polarity
  (`T{tid}[T|F]:sexp`), then evaluate each set's polarity-conjunction
  with z3 — an UNSOUND conflict is one z3 says is satisfiable. This is
  the fastest wrong-`unsat` decoder built on this arc.
* **`bench/differential/gap_survey.py <nixie> <outdir> <n> <seeds...>`**
  — the completeness telescope; fixed seeds attribute, fresh seeds hunt.
* The standing gates: `./bench/z3_parity/run_parity.sh` (z3 4.16.0;
  record the version), `bench/perf_gate/run_gate.sh`
  (`GATE_BASELINE=/media/data/proj/nixie/precompile/$(cat
  bench/perf_gate/BASELINE)/nixie` from a worktree), the wide + mixed
  differentials (≥3 fresh seeds each; the arc's rule: extend SHAPES, not
  seeds), `bench/differential/debug_panic_sweep.py` for anything
  arithmetic.

## The verification bar (unchanged, plus this stretch's traps)

`cargo build --all-features` (watch the plain `cargo build --release`
too — the full workspace default set has broken twice this week on
landed code); `cargo nextest run --workspace --all-features` (expect
~11.9k; the known_unsound/qfidl/iso_brn1083 failures are corpus-missing
in worktrees — they pass in the main checkout; the rehome/equal_pin
tests cap-timeout under load, re-run in isolation); doc tests; clippy
(DEBUG profile — the release profile dead-codes `check_fixpoint`
pre-existing); `cargo fmt`; `RUSTDOCFLAGS="-D warnings" cargo doc`;
parity; the differentials; the panic sweep; **the perf gate for anything
touching solving**. A bug fix ships with the reproducer as a test;
**revert-check the whole fix** (partial stashes have passed twice on
this arc). Watch for doc nits and undocumented signatures riding in on
merges between your verification run and your landing — two did this
stretch.

## Working knowledge that cost real time this stretch

* **The ff-merge silent abort**: a dirty working-tree file that the
  merge would overwrite makes `git merge --ff-only` print `Updating…`
  and then fail — pipe-through-`tail` swallows the error and the landing
  LOOKS raced. Check `git rev-parse HEAD` after every landing; diff the
  dirty file against the candidate's blob before `checkout --`-ing it.
* **Reason ids recycle across pops** (the `reasons` table truncates).
  Correlate ids to terms by ORDER at the moment of interest, never
  statically. Bounds and their reasons pop in lockstep, so a live
  bound's ids stay mapped — that invariant is what item 77's guards
  preserve structurally.
* **Two interning systems**: atom asserts go through
  `intern_row_reported` (fresh slack per (form, reason); strict and
  non-strict atoms over one form mint SEPARATE rows); simplex-level
  adds go through the content-addressed `intern_row_cached`. They never
  collide — several "structural hazard" theories die on this fact.
* **Build in worktrees on `/media/data`, never `/tmp`** (the root disk
  fills; the directive stands). Symlink or accept rebuilds; delete
  `target/debug/incremental` and stale >100M deps when /media/data
  hits 100% — it did four times this stretch. `/tmp` worktrees belong to
  other agents; leave them.
* **Land fast, land small**: main moved 5+ times mid-landing this
  stretch. Commit from your worktree, rebase onto main late, ff from a
  clean tree, verify the ref actually moved. Another agent may land the
  same fix in parallel (the congruence build break happened exactly so)
  — rebase drops your duplicate; content on main wins.

## Where things live

* The arc's memory: `docs/studies/2026-09-13-lia-wide-literal-arithmetic.md`
  (items 1–78; continuations 34–40 are this stretch).
* Reproducers: `docs/studies/assets/2026-09-18/` (seed-20261102 full +
  core). Regressions: `nixie-solver/tests/arith_wide_literal_regressions.rs`
  (the `rehome_*`, `equal_pin_*`, `strict_*` families).
* Binaries: `precompile/740c16bd/`, `precompile/d75fa881/`,
  `precompile/010f0e7e/`, `precompile/f4415a0e/`.

The one-sentence version: **every wrong verdict the differentials can
find is closed at the root with the battery green and the ledger empty;
the survey's remaining 114 members are honest `unknown` mapped to three
named slices (B&B width 26, budgets 24, wide-repair 16), and the
instruments — the tripwire, the decline-site tags, the polarity
pipeline, the survey — are all wired for whoever takes the next one.**
