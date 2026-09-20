# Handoff: after the attribution session — the false-`sat` found by the new SHAPES is closed, the gap re-baselined, what remains (2026-09-19)

**Read `AGENTS.md` first.** This succeeds
`docs/handovers/2026-09-19-wide-lp-post-landing.md` (executed this
session). The session's full record, with the probe evidence and the
per-item analysis, is
`docs/studies/2026-09-19-gap-attribution-fi1.md` — where they disagree,
the study wins. Landed as `7ab21fb5` (binary
`precompile/7ab21fb5/nixie`, plus a `nixie-debug` for the sweep).

## What this session changed

1. **A live false `sat`, closed at the root** — the B&B leaf's
   feasibility `check()` re-optimizes onto a different vertex than the
   integrality scan read; acceptance on feasibility alone published
   fractional-vertex models (the settled-atom gate arm cannot catch its
   own feed). Found by the new boundary SHAPES on their first fresh-seed
   run; the leaf (and the dive's base case) now re-scan integrality at
   the re-solved vertex. Reproducer pinned never-`sat` in
   `arith_wide_literal_regressions.rs`.
2. **The residual gap re-attributed** (the item-67 recipe, ~75
   `NIXIE_GAP_PROBE` tags, `gap_survey.py` now captures decline stderr
   per member — re-attribution is one command now): 47 members = 27
   sticky resource-exhaustion (7 `find_wide_pivot_col` NOCOL storms, 20
   B&B depth divergence), 9 parse-gate, 5 blocking-nongenuine, 3 BV
   minting, 3 big-const uncertified, **MBQI zero**. One machine: search
   capacity over div/mod-structured LIA at wide constants.
3. **fi1 decoded** (still honest `unknown`, z3 `sat` at `xi=5, yi=2^62`):
   the free `/7` div-slack's zero-split walks an unbounded ray — up-
   branches refute, down-branches descend one level forever — and the
   cuts cannot see the mod-7 lattice (item 55's honest unmarking of
   rescaled rows). The study's §B lists the three candidate levers in
   promise order.
4. **`eval_linear` exact** (the last unchecked narrow accumulation in
   the evaluator's periphery), **boundary-literal SHAPES landed** in
   both fuzz generators (the fixed-seed survey re-baselines: **150
   members, 140 wall-literal** — the div/mod+beyond-width frontier;
   documented breakpoint, not a regression).

## What's next, in value order

1. **The wall-frontier capacity campaign** — the re-baselined survey's
   140 wall-literal members are one class: div/mod nesting under
   beyond-width witnesses. The levers (all heuristic-class: matched
   null, ≥10 seeds, no wall-clock): NOCOL repair eligibility, the B&B
   ray-walk branch signature (fi1's §B), real divisibility lemmas from
   the div/mod axiom rows (intern the mod-slack's `[0,d)` window at
   intern time).
2. **The bound-shadowing journal** — the design is sharpened to landing
   spec in the study's §F: the trail's full-clone undos are already
   pop-exact under LIFO; the journal's job is keep-the-tighter-live
   without losing the displaced bound's reason set. Do NOT land a
   decline without it.
3. ~~The model-blocking retry-succeeds fixture~~ — **closed** as the
   white-box option (`153b1e1c`): the loop's mechanics are pinned by
   driving `block_refuted_model_and_rebase` directly (block excludes an
   assignment, rebase leaves a solvable state, retry certifies the other
   model, counter pops scoped); the *reachability* of a refuted-first
   candidate stays fuzz-covered (no small deterministic goal exists on
   this tree).  The handoff's item 8 (exact-value spelling) closed with
   it: `get-value` echoes of exact rationals re-parse (the `RealConst`
   printer arm's `1/n` math spelling was readable by nothing).
4. ~~The wide-constant parity refutation~~ — **DONE the same day**
   (`33cb9418`, merged to main as `37ab63b1`): the Hermite solve widened
   to the full `i64` input domain (`MAG_BOUND_SOLVE`, checked Euclid
   updates); the reproducer answers the exact `unsat`, the fixed-seed
   survey drops **150 → 104** (the 46 closed are the UNSAT-side parity
   class, 31 → 3), timeouts 12 → 7.  The residual 104 is now purely the
   **SAT-side beyond-width witness frontier** (101 wall-literal members)
   — model construction, not refutation.  That is the campaign's next
   target, alongside the parallel session's S3 interval-refutation work
   (their item 87).

## Tree-health validation record (2026-09-20, at `b49b9242`)

After the heavy multi-owner churn (slack-CSR watches, the arith
items 93–96, the printer/simplify/parser landings of this arc), the
full battery re-ran clean on every surface: mixed ×3 + wide ×2 + quant
×2 fresh differential seeds (zero verdict disagreements, zero refuted
models), the debug-panic sweep over the parity corpus (zero panics),
and a 400-file stratified SMT-LIB verdict screen vs z3 across 8
arithmetic families — **399 decisive-verdict pairs, 0 disagreements**.
The wrong-verdict ledger stays empty.

## Open-items closure ledger (2026-09-20, final)

| item | verdict |
|------|---------|
| `eval_linear` exactness | **CLOSED** (`7ab21fb5`) |
| Boundary SHAPES + ill-sortedness | **CLOSED** (`7ab21fb5`) |
| The B&B leaf re-scan (false `sat`) | **CLOSED** (`7ab21fb5`); the parity twin closed by the Hermite widening (`33cb9418`) |
| fi1 | **CLOSED by the arith owner** (item 95 + the widening; `sat` in 48 ms, z3-validated) |
| Model-blocking reachability fixture | **CLOSED as fuzz-covered** — 12 shapes measured all-preempted; the white-box mechanics fixture landed (`153b1e1c`); no deterministic shape exists on this tree |
| Bound-shadowing journal | **CLOSED as design-spec'd** — the trail's full-clone undos are pop-exact under LIFO (proven in study §F); the guarded writers + `NIXIE_BOUND_TRIPWIRE` stand; the journal's landing spec is recorded for whoever next touches `set_*_value` |
| `get-value` Real-entry sort residual | **CLOSED** (`9bd34785`) — equality-extraction now consults the variable's sort |
| Unrecognized-command silence | **CLOSED** (`8e0fa573`) |
| nec-smt / `solve_eqs` pre-pass | **HANDED OFF with complete diagnosis** — the memo proved the residual cost is the case splits; the entry points (guard-equality elimination before the walk, or split ordering) are in the perf-gap study's addenda; see `2026-09-20-smt-perf-arc-executed.md` |
| ndir2 re-measurement | **STILL GATED** — the gate BASELINE re-pinned three times during this arc (`1710e125` → `aa219f89` → the flip); re-measure only on a stable baseline |
| Item 71's channel question, J5, the ray | **THE ARITH OWNER'S** (their item-96 handoff) |

The CSR `scan_split` underflow (a landed panic on `pete_5s`, release
included, from the slack-CSR flip) was found and unblock-repaired in the
same landing (`9bd34785`, the `fa0d59c9` precedent class) — with both
worlds verified `unsat` and the both-present invariant debug-asserted.

## Process notes from this landing

* Two fresh-seed differential runs (six seeds total) around the merge;
  the FIRST found the false `sat`, the second validated the fix — the
  SHAPES paid for themselves before their landing commit existed.
* The full debug suite's DWARF is ~97 GB on a full workspace;
  `CARGO_PROFILE_DEV_DEBUG=0` keeps debug assertions at a fraction of
  the size — the linker bus-errors under disk-full are silent failures
  otherwise.
* The perf gate resolves `precompile/` relative to the CWD: symlink the
  primary's `precompile` into a worktree before running it there.
* `gap_survey.py`'s stderr capture + `NIXIE_GAP_PROBE=1` on any binary
  reproduces the attribution table in one run — keep the tags' output
  stable if touching decline sites.
* **The precompile cache incident (2026-09-19, late)**: a worktree's
  `precompile` convenience SYMLINK was swept up by `git add -A` (the
  dir-only `/precompile/` ignore pattern does not match a symlink) and
  the landing replaced the primary's real cache directory with a broken
  self-symlink — most cached binaries were lost.  Repaired: `.gitignore`
  now ignores both forms; the gate BASELINE `1710e125` was rebuilt into
  the cache (throwaway worktree, deleted after) and verified by a PASS;
  the tip binary `e7fbd8fb` is cached.  Older entries are gone — rebuild
  on demand per the AGENTS.md convention, and never symlink `precompile`
  into a worktree (bind the gate's `GATE_BASELINE` or copy instead).
