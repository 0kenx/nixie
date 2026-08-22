# Mid-search inprocessing bundle: bisected with instruction counts, no default flip (2026-08-22)

Follow-up to the timeout-residue plan (item 3: mid-search vivification
cadence) and to the standing "inprocessing stays off" verdict, which until
now rested on load-contaminated wall-clock screens.

## Setup

Reference: cadical runs `vivify` **inside the inprobe block**
(`probe.cpp`: decompose → ternary → probe → gates → backbone → sweep →
**vivify** → transred → factor), i.e. bundled with probing, not as a
standalone schedule. OxiZ's `vivify_clauses` + `transred_round` +
`subsume_round` + ELS-round + pure-literal live inside `inprocess()`,
gated on `enable_inprocessing` (off in every preset; fires every 4000
conflicts when on).

Component-bisect screen: temporary env gates (`OXIZ_IP_NO_{SUBSUME,
VIVIFY,TRANSRED,ELSROUND,PURELIT}`) in a throwaway worktree.
Instructions-to-verdict, PMU `cpu_core/instructions`, CPU-pinned,
process-group-safe harness. Caps are walls; `TO` cells mean ">=".

## Results

Residue files (base = preset default, BVE+ELS pre-search on):

| file | base | full bundle | no_transred | no_subsume | vt_only |
|---|---|---|---|---|---|
| circuit64 | TO | **S 1117G** | TO | TO | TO |
| rbsat | S 519G | S 1106G | **S 114G** | S 445G | S 443G |
| crypto1 | TO | TO | TO | — | — |
| worker550 | TO | TO | TO | — | — |

no_transred vs base on previously-damaged files:

| file | base | no_transred | ratio |
|---|---|---|---|
| qwh50 | 184G | 600G | 0.31x |
| stable300 | 87G | 361G | 0.24x |
| constraints17 | 68G | 164G | 0.41x |
| summle4044 | 72G | 127G | 0.56x |
| 6s167 | 51G | **22G** | **2.34x** |
| mrpp | 48G | 53G | 0.90x |

## Findings

1. **circuit64 needs the whole bundle**: removing any single component
   re-times-it-out. The only residue file inprocessing rescues is rescued
   by the full interaction, not by vivify alone.
2. **transred is a 10x villain on binary-heavy instances**: rbsat
   1106G → 114G by turning transred OFF mid-search (and 4.5x better than
   the preset default's 519G). Mechanism (hypothesis, fits the worker550
   diagnosis): transred retires original binary clauses → fewer BIG edges
   → binary propagation falls back to the watcher machinery on exactly the
   instances where the BIG path is the fast path. This *refutes* the
   recorded "transred amortizer" hypothesis with data.
3. **No bundle variant is a default candidate**: full wins circuit64 but
   collapses qwh (6x, prior data) and rbsat (2x); no_transred wins
   rbsat/6s167 but wrecks qwh/stable/constraints (2.4-4x); no_subsume and
   vivify+transred-only lose circuit64. Our subsume round already carries
   the cadical `subsumelimited` propagation-scaled budget — the damage is
   not a missing cap.
4. What cadical has that we do not is *adaptive effort scheduling* across
   the whole inprobe family (tier-fractioned vivify budgets, per-instance
   effort normalization) plus probing interleaved *inside* the same block;
   component parity does not reproduce it.

## Verdict

`enable_inprocessing` stays off in every preset — now confirmed with
deterministic counts rather than load-tainted walls. The screen gates are
reverted (throwaway worktree deleted).

**Recorded follow-up (the one shape that could capture the wins)**: an
*inprocessing arm in the budget-chained portfolio* (the `SEEDS`/
`ARM_CONFLICTS` mechanism from `2026-08-seed-portfolio-restarts.md`):
default arm first, then a `INPROCESS=1`-style arm without transred. That
would capture circuit64 (default TOs, arm solves 1117G), rbsat (519G →
114G via the arm), and 6s167 (51G → 22G) at bounded budgets while the
default path keeps qwh/stable untouched — the same trade the seed
portfolio already makes: pay a budget slice for a different search shape
instead of perturbing the default.
