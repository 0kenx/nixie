# Handoff: the MBQI arc is closed, the SMT perf gap is attributed — the map for the next agent

**Date:** 2026-09-19 (evening).  **Arc:** `docs/studies/2026-09-14-model-finder-constructor-tables.md` follow-ups nineteenth–twenty-second + the perf attribution; input handoff `2026-09-18-mbqi-persistent-model.md` (fully executed).  Companion: `docs/studies/2026-09-19-smt-perf-gap-attribution.md` (the perf territory).
**Goal for the next agent:** two owned, mechanism-named projects — the arithmetic layer's **eq-chain pivot storm + integer-reasoning (DIO) gap** (owns both LIA loss classes), and the **deep-encoder flip** (already built, held off) once that lands.

## Where things stand (all landed on main)

- **The persistent-model rewrite is done and closed** (`7e0abe46`): the completed model is one structure per search (z3's proto-model), monotone first-wins merge, element canonicity, self-consistency, version-keyed signatures, repair channels.  Set family `sat` on **honest rows** (set16 ~9 s, set9/19 ~8–10 s; z3 still times out on set19).
- **Both fuzz gaps are closed** (`6792afd3`): the unsat-forcing battery solves **150/150 on every seed** (51–54 × 150).  Pigeonhole via the EUF-representative export; extensional via the literal-binding channel (armed by the gate's materialization; **self-pairs only**; the odometer gains the goal's own compounds).
- **The assertion gate** (always-on, structural evaluation, persistence-armed materialization), the Bool-constant equality fold, and the export's mention-split are all in (`474bba8a`).
- **The matched-null formality closed** (`7e5075db`): `NIXIE_CT_NULL` — set9 null 5/5 sat and cheaper, set19 7/10 vs 10/10; the row-match content buys 30 % where closure discipline is load-bearing.
- **The standing SMT perf table exists** (`54a4ed17`, `bench/smt_perf/run_perf.sh`): QF_LIA **32/60 vs z3 54/60**, QF_BV **50/60 vs 53/60**, zero disagreements.  Every loss attributed (below).
- **The CLI conflict budget is real** (`df69ef0c`): `--conflict-limit` binds the SAT core on every path (was: theory-conflicts only — a facade on bit-blasted goals).  Deterministic-neutral at limit 0; pin `conflict_limit_binds_end_to_end_on_sat_core_conflicts`.
- **The deep-split rescue is built and held off** (`1b6a0bd2`): `solver/deep_split.rs`, `NIXIE_DEEP_SPLIT=1`, default off.  Fully iterative, unit-pinned.  Held because it buys no verdict alone — see the second pathology.

## The perf territory (read the attribution study first)

`docs/studies/2026-09-19-smt-perf-gap-attribution.md` names every loss with repros:

1. **QF_LIA −22 = two mechanisms, both arith-arc-owned**:
   - *9 instant `unknown`s* — deep-encoding class (nec-smt: 2537-deep ite/`=`/`let` spines vs `ENCODE_DEPTH_LIMIT` 512).  The depth-limit-lift probe (another session's addendum in the same study) and my deep-split **converge on the same finding**: once encoded, these still grind — the binding constraint is not the encoder.
   - *timeouts* — **z3 decides these in its Diophantine solver** (`arith-dio-calls 1`; CAV 45-var problems z3 answers at 0–1 conflicts).  Nixie's branch-and-bound instead grinds **simplex rational blowup**: ~100 % of samples in `Ratio::reduce`/BigInt `gcd`, conflict-free, inside the deadline-checked search (proven by the budget probe + the deadline discriminator).  A *second* face of the same disease: the **pivot storm on wide equality chains** — a trivially-sat 600-var synthetic (deep-split on) searches past 20 s, profiled as `pivot`/`find_violating`/`slice_contains`, thousands of conflict-free pivots.
   - **Near-miss datum (decisive): 0/28 losses flip at 3.5× the cap** — categorical, not constant-factor.  No percentage-level LIA work moves this table.
2. **QF_BV −4** — multiplier-identity problems z3 folds at 0 conflicts (BuchwaldFried/Sage2/sage-app7-12); the wienand/SOM preprocessor class; the pure-BV dispatch's own comments name the route.
3. **Both-solved median conflict ratio is 1.0** — competitive per conflict; the mechanisms, once fixed, land on a solver already fast where it decides.

## The deep-split: how to flip it

When the arith eq-chain fix lands (the pivot storm), set `NIXIE_DEEP_SPLIT` on by default (flip `enabled()` in `solver/deep_split.rs`), re-run: the nec-smt class (9 standing-table instances), the `bench/smt_perf` table, and the full battery.  If the class still doesn't flip, the remaining blocker is the preprocessor-fold gap (z3 folds the spines outright at 0 conflicts — the other session's addendum says the same).  The iterative encoder (~970 lines, 32 sites) remains the alternative if the split's definition-shape ever proves limiting — but two independent probes now say encoding is not the binding constraint.

## Negative results (do not retry blind)

All with mechanisms in the studies (twentieth–twenty-second follow-ups + the attribution):
- Blanket pollution purges / wholesale assignment adoption / blanket duplicate-invalidation / unconditional minted-args hint repair / structural mining / unarmed or merged-pair compound odometer points (each regressed the family).
- The composed-consistency pass as built (regressed set16).
- The depth-limit lift alone and the split alone (unknowns become timeouts, no verdicts).
- `getenv` in per-assert paths — the deep-split gate uses a `OnceLock`; keep it that way (the env-probe regression class).

## Repo conventions that bite (this arc's additions)

- **Landing through a dirty tree on *overlapping* files** (done twice this arc): `git push . HEAD:main` refuses on any dirt.  If the dirt doesn't overlap your files: materialize yours → `git update-ref refs/heads/main <sha>` → `git reset` → verify build.  If it DOES overlap: 3-way under-merge first (`git merge-file` base=main, ours=their working copy, yours=branch), then the same sequence — their commit later adds their hunks without reverting yours.  Never materialize over their edits; never `update-ref` bare over overlapping dirt.
- **`--conflict-limit N` is now a legitimate harness instrument** (use it for phase probes: "no verdict at limit 1" = the spin is pre-search/in-theory).
- **The SAT standing table's corpus is gone** (gitignored external data; 4 files left).  Refill out of band (see `bench/differential/README.md`) before any full SAT table; the 4-file spot and the corpus-gap record are in `2026-08-satcomp-standing-gap.md`'s addendum.
- Binaries for every landing live under `precompile/<sha>/` (latest: `cc350da6`).  Load is heavy (other arcs); time pins under load, not single runs.

## Adjacent arcs (don't collide)

Arithmetic (simplex/wide-LP — active, `encode.rs`/`mod.rs` were hot this evening), graph constraints (active), SAT/BVE/fold-dedup, bags, let-printer.  `nixie-solver/src/solver/` sees concurrent edits — check `git status` before any ff.

## Ordered next steps

1. **The arith eq-chain work** (owning session): the pivot storm on wide equality chains + the DIO/integer-reasoning gap.  Probes that work: the 600-var deep-split synthetic (`NIXIE_DEEP_SPLIT=1`), CAV `problem__022`, `NIXIE_DIAG=1` pivot counters, perf with a `debug=1` release build (`CARGO_PROFILE_RELEASE_DEBUG=1` — the stripped release gives `[unknown]` frames).
2. **Flip the deep-split** with it; re-run `bench/smt_perf` (expect QF_LIA +9 if nec flips).
3. **The BV identity preprocessor** (wienand/SOM extension) for the −4.
4. Re-run `bench/smt_perf/run_perf.sh` after any of these and update the README table; the MBQI arc needs nothing further.
