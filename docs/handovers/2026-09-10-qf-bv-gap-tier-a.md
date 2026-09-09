# Handover prompt — QF_BV gap vs z3, Tier A (rewriting/preprocessing)

Written 2026-09-10 for the next session. Everything below is verified and
banked; nothing here is speculation.

## The prompt (paste into a fresh session)

> Work in a git worktree (never checkout/restore the shared tree). Your
> task: **close the Tier-A part of the QF_BV performance gap vs z3** —
> ~17 of the remaining 44 one-sided losses where z3 solves in **under one
> second** (a rewriting/preprocessing gap, not a search gap). Start with
> the biggest lever:
>
> **1. Port z3's `elim-unconstrained` tactic** (10 files:
> `brummayerbiere4/unconstrained01..10`, z3 0.1 s each). Each file
> declares ~6 × 1024-bit variables that occur **exactly once**; z3's
> unconstrained-variable propagation replaces the whole goal with a free
> atom. Nixie has an **empty stub**:
> `nixie-core/src/tactic/core/elim_unconstrained.rs` (every method is an
> `#[allow(dead_code)]` no-op). The reference is
> `../temp/z3/src/tactic/core/elim_unconstrained_tactic.cpp` +
> `elim_unconstrained.cpp` (operator rules), plus Brummayer/Biere
> MEMICS'09. Soundness is the hard part, read AGENTS.md first:
> - the tactic is **satisfiability-preserving, not equivalence** — the
>   established in-repo pattern for that is the stage-4 dispatch
>   preprocessor's *assert the rewrite alongside the originals*
>   (`docs/studies/2026-09-07-bv-dispatch-unification.md`, and its
>   ring-elimination gating bug is the cautionary tale);
> - every per-operator rule has a reachability condition (e.g. `bvand`
>   propagates unconstrainedness only if the other operand can supply a
>   zero bit) — port them exactly, no shortcuts;
> - gate model production or reconstruct values (an unconstrained
>   variable's model value is chosen, not searched).
>
> **2. Structural rewriting** (~7 files: `maxandminor016`, `bitrev1024`,
> `calypto/problem_14|19`, `sage/app7/bench_4443`, `BuchwaldFried
> counterexample...`): concat/extract normalization (extract-of-concat,
> concat-of-extracts merge) and AND/OR/NOT constant push. Reference:
> `../temp/z3/src/ast/rewriter/bv_rewriter.cpp`. Check what
> `nixie-core/src/tactic/bv/bv_rewriter.rs` + `advanced_rewriter.rs`
> already do before adding anything.
>
> **3. Polynomial normalization** (3 files: `cohencu.c_2..4`, z3 0.1 s):
> 32-bit mul/add chains encoding z=3n², y=3n+3n²−1. The dispatch
> preprocessor already has a SOM/poly-identity pass — these files fall
> below its width routing (`goal_is_pure_bv` / wide-`bvmul` gates, see
> the stage-4 study). Extend or re-route; measure.
>
> Do Tier A before touching Tier B (the ~27 search-class losses — Sydr
> cjpeg, bmc s3_clnt, spear — need CEGAR/search work and are not
> rewriting wins).
>
> **Verification bar** (all of it, in this order):
> 1. `cargo build --all-features`; `cargo nextest run --workspace
>    --all-features`; `cargo clippy --all-features --all-targets -- -D
>    warnings`; `cargo fmt --all -- --check`; `cargo doc --no-deps
>    --all-features -- -D warnings`.
> 2. `./bench/z3_parity/run_parity.sh` — 0 disagreements required.
> 3. Re-screen the 509-file sample with the landed binary:
>    `python3 precompile/ac13904/benchmark/bv_gap/rescreen.py <binary>
>    /tmp/out.jsonl` (max 4 concurrent, cores pinned; the z3 column is
>    banked in `gap_cells.jsonl`). Baseline after the u64-wrap fix:
>    **266/509 solved, 0 disagreements vs z3** (z3: 281). Every
>    treatment claim needs the matched-null discipline of
>    `docs/BENCHMARKING.md` — a rewriting pass that only wins by
>    trajectory luck will not survive review.
> 4. Regression tests next to the code, per AGENTS.md.

## Operational cautions (all bit someone this week)

- **Never trust a verdict without the binary's md5 in the same shell
  block.** A shared `target/release/nixie` changed md5 three times under
  one session (other agents rebuild concurrently); verdicts were
  attributed to the wrong source. Build benchmarks in an isolated
  `CARGO_TARGET_DIR` and freeze the artifact under
  `precompile/<sha>/` before measuring.
- **Shell cwd drifts between command blocks** — always `cd` explicitly
  or use absolute paths; several phantom "flips" were two different
  binaries (main checkout vs worktree).
- Worktrees: `git worktree add <dir> <sha>` (main is checked out in the
  primary). **Symlink the corpora in** or 14 corpus-backed tests fail:
  `ln -s /media/data/proj/nixie/{smt-lib,satcomp2024,satcomp2025,satlib} .`
  Remove the worktree when done; other agents may still touch a live
  one (a HEAD moved mid-session once).
- z3 on PATH is 4.16.0 (the parity suite pins 4.15.4; the banked z3
  cells are 4.16.0 — fine, they're the comparison target, not parity).
- Disk is tight (~97%, ~53 G free). Release CLI builds are ~2–3 min.

## Where everything is

- Current state of the campaign + root-caused false-sat history:
  `docs/handovers/2026-09-09-bv-false-sat.md` (read fully — it contains
  the cluster map, the resolution, and the measurement incident).
- Banked cells + re-screen runner:
  `precompile/ac13904/benchmark/bv_gap/` (`gap_cells.jsonl` = pre-fix
  nixie + z3; `fixed_cells.jsonl` = post-fix nixie; `rescreen.py`).
- Frozen binary: `precompile/ac13904/nixie` (md5 64e6c14…).
- Blast-vs-search tooling (env-gated, landed): `NIXIE_DUMP_CNF`,
  `NIXIE_DUMP_TERMS`, `NIXIE_DUMP_CNF_AT_SAT` — use them before blaming
  the SAT core; the split takes minutes and saves hours.
- Known adjacent soundness bug, **not yet fixed**: the parser accepts
  ill-typed terms (BV1 as `ite` condition; `=` between different-width
  operands). Three sightings. Fix independently, it's cheap.
- Tier-B leads and everything else: the 2026-09-09 handover, §Follow-up.
