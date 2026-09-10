# Attribute the remaining propagation branch cost

## Registration

The contiguous binary engine removes 23.14% of whole-process instructions
against qualified production, but its one cost screen improves wall by only
2.35%. Its cycle profile puts 71.19% in propagation and 8.291% at deleted-header
tests/branches. Those are sampled instruction locations, not branch-miss or
load-source attribution. Do not assume that removing a hot branch removes its
sampled cycles. Earlier batching, lookahead, compact metadata and packed-truth
experiments already price several unsuccessful ways of changing this loop.

Use exactly ONE new solver diagnostic on the cached contiguous-engine perf
binary, source 710011283b14c1a8c613ac70161b5fb00a8964b2, SHA-256
ea7701b739f7031005135996277e902050d070384809e719f05d841a4d8f9abb.
This is a new event attribution, not another cycle profile or wall observation.
Sample user Atom BR_MISP_RETIRED.ALL_BRANCHES (event 0xc5), precise_ip=2,
period 200003, with user ANY LBR flags, CPU IDs, period and running-time reads.
Non-solver hardware preflight is permitted; stop without a solver invocation
if the requested event/precision/read configuration is unsupported.

Use j3037 SHA-256
7672cb34e4b32cf83292630f1155b7e564bdcf4b2eedd60f7f25cf59b4b5bcc7,
CPU 15, seed 0, MAXC=10000000, PRINT_MODEL=1, NIXIE_SWEEP=0,
NIXIE_DEFINITIONS=0; clear other study overrides. Preserve the portable
Rust 1.96.0 / LLVM 22.1.2 binary. Warm executable/input; anonymous tmpfs
output, 128-page recording ring and emergency cap 300 seconds. Audit constrained
competing threads, retain start/completion immediately and store the result
once under precompile/7100112/benchmark. No retries, new controls, reference
runs, solver changes or cost claims from this diagnostic's elapsed time.

Require exact stdout identity with the retained qualified cost, at least
1000 samples, CPU 15 only, zero loss/throttle and >=99.9% PMU coverage.
Audit precise-IP flags and branch-stack flags explicitly. Decode the exact
ELF/mapping and report sampled-IP and branch-history attribution separately.
Do not treat taken-branch history as an unbiased sample of all branches,
sum overlapping histories as independent events, infer per-site miss rates
without execution denominators, or convert event shares into removable wall.
Keep ambiguous IP/history associations unassigned. An unchecked UNSAT is
unknown/unverified in the canonical record.

Map propagation sites to binary truth/loop exits, long blocker exits,
header liveness/null guards, other-watch truth, tail truth/loop exits,
destination append/growth and queue/list boundaries. Use current disassembly,
not matching addresses from other builds. Compare these event locations with
the retained cycle-site groups, preserving the different sampling semantics.
Inspect local Kissat proplit.h and the previous negative mechanisms before
proposing a change. A follow-on implementation needs a separately recorded
soundness argument, removed consumer, replacement costs and measurement gate;
this audit alone cannot qualify production source or a new policy.

Commit the findings and reproducible offline analysis on main. Preserve raw
and canonical result-store evidence and the existing binary cache; remove
owned disposable artifacts. No production solver source is modified here.

## Result: tail classification and loop exits, not header misprediction

The single invocation produced record **73f875a5c9bd11b0** with byte-identical
stdout: 330,565 conflicts, 323,390,316 propagations and 695,639,361 ticks.
All **10,315** samples have the precise-IP flag, user mode and CPU 15. PMU
coverage is 100%, with zero loss or throttle; constrained sleepers retain
their runtime and identity. Whole output remains unchecked UNSAT, recorded
as unknown/unverified. The sampled prefix contains 2,063,042,052 branch
misses and 195,672,345,249 instructions. These are diagnostic prefix counts,
not a replacement for the prior cost cell. No new timing result is claimed.

The complete engine accounts for **8,340 / 10,315 (80.85%)** of precise
branch-miss sample IPs. Its sampled IPs resolve to branch instructions in
the exact cached binary. The following nonoverlapping groups include all
three generated long-scan bodies, including the rare deleted-prefix entry.

| Branch group | Samples | Share of all branch-miss samples |
| --- | ---: | ---: |
| Tail false versus undefined | 2,054 | **19.91%** |
| Long blocker truth | 1,886 | **18.28%** |
| Long-list loop end | 1,069 | **10.36%** |
| Binary-loop end | 726 | **7.04%** |
| Binary truth/conflict | 630 | **6.11%** |
| Tail positive test | 563 | **5.46%** |
| Tail length bound | 451 | **4.37%** |
| Empty long list | 430 | **4.17%** |
| Empty binary span | 379 | **3.67%** |
| Other watched literal truth | 137 | **1.33%** |
| Header null/deleted guards | **0** | **0 observed** |
| Destination capacity | **1** | **0.010%** |

Two samples are at long unit/conflict selection; twelve engine samples lie
outside the displayed categories. This is event attribution, not per-site
miss rates or exclusive stall costs. Zero observations do not prove zero
misses. In particular, the older 8.291% cycle-site share around deleted-header
tests cannot be called an 8.291% branch-misprediction opportunity. The current
measurement does not identify the underlying load latency at those sites.

Of the samples, **5,618 (54.46%)** have IP exactly equal to the newest
M-flagged LBR source. The other **4,697** IP/history associations stay
unassigned. Taken-branch history need not contain a missed not-taken branch;
its absence does not invalidate an exact sampled IP. No overlapping branch
histories are counted as additional independent samples. External-library
IPs are retained separately; no executable IP is unresolved. See the
[address/group report](assets/2026-09-10-propagation-branch-attribution.json),
[interactive event distribution](assets/2026-09-10-propagation-branch-attribution.svg)
and [offline decoder](assets/2026-09-10-propagation-branch-attribution.py).
The visualization is a function/IP distribution, explicitly not a cycle
flamegraph or a reconstructed call stack.

## Consequence for the next implementation

The strongest local target is the **two-stage tail classifier**: 25.37% of
all observed branch misses occur at its positive and false/undefined tests.
The current loop checks `value > 0`, then `value == 0`, for every inspected
tail literal. A false literal passes through both tests. Local Kissat
`src/proplit.h` instead searches for the first value >=0, then handles the
result outside that loop. Nixie must retain its own true-literal parking
semantics, first-undefined choice, eager watched-pair normalization and
stored order; copying Kissat's true-literal move would change search.

A follow-on should isolate the false-prefix scan from classification of the
single selected literal. This removes a repeated classifier, whereas the
earlier header pipeline added state without removing a visit and packed
truth added mask/RMW work. The tail still needs a truth branch and a length
bound; the positive/undefined distinction still exists at its result. The
25.37% event share is **not** a predicted reduction in misses or wall, and
short false prefixes limit removed instruction work. Exact assembly and a
whole-solve screen must price the changed control flow. List-end branches
are also substantial, but this does not yet justify sentinel storage or
merging binary and long lists: both need separate correctness/cost arguments.

The decoder passed five synthetic cases: precise source association, target
association kept separate, absent precision rejected, wrong CPU rejected,
and unrelated history kept unassigned. Exact grouping recomputes the saved
report. Both event/precision preflights used only a short Python workload;
the registered solver diagnostic ran once. Raw data, runner, metadata,
disassembly and canonical record remain under
`precompile/7100112/benchmark/propagation-branch-attribution/` and its sibling
`runs/propagation-branch-attribution/`. Production source was not modified;
workspace solver qualification is not claimed or needed for this diagnostic.
