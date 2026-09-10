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
