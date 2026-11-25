# Incremental unrolling for the TLA BMC loop – verdict-identical, budget-neutral (negative result on the suspected cause)

**Date:** 2026-11-25
**Issue:** #25 ("Undecided BMC queries: diagnose, then incremental unrolling")
**Landed as:** the single-solver `push`/`pop` rewrite of `Bmc::check`.

## The hypothesis, and what happened to it

The issue suspected that the ~12 "solver undecided" corpus specifications
were paying for a **fresh `Solver` per depth** – everything learned at depth
`j` discarded at `j+1` – and predicted that one persistent solver
(`Init`/`Trans_k` asserted once, `~Inv_j` under `push`/`pop`) would decide
≥5 of them at an unchanged conflict budget.

**The hypothesis is false.** Measured on the whole corpus and on the
undecided set, at two budgets:

| run | binaries | result |
|---|---|---|
| corpus, depth 4, 20 000 conflicts | fresh-solver (parent) vs incremental | **byte-identical** per-spec lists (319 lines, same md5): 107 checked, 14 undecided, same specs in every bucket |
| the 12 undecided specs, 200 000 conflicts | fresh-solver vs incremental | **identical verdicts**: `Barriers`, `TokenRing`, `SyncTerminationDetection` become `no-violation` on both; the other 9 stay undecided on both |

So the undecided bucket is **not re-derivation-bound**: those specifications
exhaust the per-query budget at a depth whose formula the search cannot
finish, and carrying learned clauses across depths does not rescue them.
The binding constraint is elsewhere (set-theory blowup over symbolic state
sets – the #20 frames work – and per-depth formula size, not repeated
learning loss). Anyone returning to this bucket should start there, not
here.

## What the rewrite is still worth

It landed, with verdict identity established, because:

1. **The architecture is the one the remaining issues need.** Deadlock
   checking (#26) asks a per-step "no successor exists" query next to the
   invariant query; simulation (#28) asserts one disjunct per step. Both
   are push/pop queries against a persistent unrolling – the fresh-solver
   path would re-assert the whole prefix per probe.
2. **Facts and queries are separated correctly.** Assumptions, `Init`, the
   transitions, `.cfg` constraints and definitional side constraints are
   asserted **outside** the push (facts about the specification); only the
   negated invariant and the blocked-trace clauses sit inside (facts about
   the query). Encoding depth `j` can mint new definitional facts – a
   `CHOOSE x : x \notin S` registers its non-membership when first encoded
   – and those are drained *before* the query is asked; one depth late was
   observable as a wrong answer in the fresh-value-idiom tests, which is
   how the ordering got pinned.
3. **The unlimited-budget case improves.** With no conflict limit (the
   library default, and what in-crate tests exercise), the queue-growth
   test went from an undecided query to a **confirmed, replayed violation
   at step 3**: the model builder had budget to finish, and the trace
   decoded. Budget-capped corpus runs see no such effect, per the table.

## Why no matched-null campaign

The change provably does not alter any verdict at either measured budget
(the corpus comparison is exact, not statistical), and the conflict budget
– the deterministic cost unit here – is applied per query in both designs,
so the accounting is unchanged. Wall-clock was deliberately not compared:
both 200k runs overlapped unrelated builds, and a contaminated number is
worse than none. If a future change makes the incremental path's cost
visible, that change re-measures under `docs/BENCHMARKING.md` (matched
null, ≥10 seeds) – this study is the baseline it starts from.

## Reproducing

```bash
# corpus A/B (byte-identical lists)
NIXIE_TLA_LIB=../temp/communitymodules/modules NIXIE_BMC_CONFLICTS=20000 \
  NIXIE_BMC_LIST=1 cargo run --release -p nixie-tla-check --example bmccheck -- \
  $(find ../temp/tlaplus-examples ../temp/apalache -name '*.tla' | sort)
```
