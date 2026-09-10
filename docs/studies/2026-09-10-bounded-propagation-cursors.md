# Bounded traversal cursors inside a propagation session

## Registration

Continue closing Nixie's wall/cycle gap against Kissat. The archived session
and assignment leaf (ebaef56) removed per-list setup and truth-owner loads,
but retained an arena-plus-tail base and indexed traversal coordinates. Its
tail index overwrote the arena register, requiring restores on tail exits.
This experiment changes traversal representation, retaining that session,
the assignment leaf and the complete callback/observer fallback.

Split the two watched literals from the clause tail and walk disjoint tail
slots directly. Replace indexed watch compaction with bounded read/write/end
cursors; compute the kept count only at the outer list boundary. Exclusive
slice ownership must exclude reallocation and aliased element references.
Each consumed entry may be kept once or removed; write never overtakes read.
Preserve the unvisited suffix on conflict, including overlap and empty lists.
Keep small unsafe operations inside the cursor primitive, with no custom
Send/Sync or persistent raw pointers. Retain a no-removal prefix and at most
one transition to compacting suffix, so call depth is independent of input.

Kissat proplit.h and CaDiCaL propagate.cpp are the local cursor/end traversal
references. Do not import their saved clause-search positions or different
replacement/normalization policies. Preserve exact Nixie clause order, eager
normalization, blocker updates, true-tail parking, first undefined watch move,
unit/reason order, conflicts, budgets, scheduling ticks and work ledger.
This is an implementation screen, not a heuristic change or a seed search.

Before cost, inspect portable Rust 1.96.0 / LLVM 22.1.2 perf assembly using the
frozen lock 3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439.
Require cursor/end traversal and direct truth/arena bases on blocker and
nonassigning tail paths: no repeated owner dereferences, saved derived-tail
base load per miss, or arena restore after ordinary true-tail exits. Calls
may preserve bases on units or destination growth; record those costs.
Record text/frame sizes without treating size as speed. Permit one specific
source-directed repair if the intended representation fails to lower; stop
at preflight if it still fails. Do not sweep encodings or inline annotations.

Run default/all-feature SAT tests, doctests, strict SAT Clippy and formatting
before cost. Extend the scalar oracle across tail truth patterns and both
compaction phases. Test cursor empty/end/overlap/early-conflict cases,
assignment queue publication and borrowed arena identity with strict-
provenance Miri; retain native Rayon owner-transfer and callback checks.
Full workspace verification and installed-Z3 4.16.0 parity remain mandatory
before production promotion. Z3 is a soundness gate, never the perf target.

Use default Nixie sweeping ON explicitly (NIXIE_SWEEP=1), definitions OFF,
CaDiCaL preset, seed 0, MAXC=10000000, PRINT_MODEL=1 and cleared other study
overrides. Reuse production fd01d0b's constraints cell 14d6f38d3c5c5cb9
(53147102832 instructions, 45156742562 cycles, 10.01 s). Run candidate
constraints first, requiring at least 5% lower instructions and qualified
wall/cycles. Only if it passes, run production/candidate crn and candidate/
production j3037, reusing any compatible cells; require no input regression
above 3% and at least 5% three-input wall improvement. Finally allow one noL
candidate against sweep-ON 36990e8006fa9aac, with the same 3% regression cap.
At most six new cost cells; no repeated cells or reference reruns. Reuse
Kissat 4.0.4 with the user's disabled-pass options as target context. Never
join sweep-OFF Nixie cells into this default-mode comparison.

Use the retained CPU15 Atom setup, portable release, warmed input/binary,
anonymous tmpfs output, GNU time 1.10, grouped user instructions/cycles/
branches/misses, 300-second cap and no owned builds during timing. Require
at least 99.9% PMU coverage, zero major faults, at most 5% off CPU and audited
idle guards. Instructions are the primary execution counter; scheduling
ticks establish workload equivalence and remain untouched. Cached-control
age and shared-host interference limit wall attribution. Store every start,
completion, exact output/model comparison and canonical record once.

A cost rejection permits one CPU15 cycle/LBR diagnostic on the rejecting
input, period 10472903, requiring at least 1000 resolved samples, 99.9% PMU
coverage, zero lost/throttled records and less than 1% unresolved weight.
Its time is not a replacement cost cell. No measured repair or second
profile. Archive any rejection with its source, generated code and causal
limits on main; clean the owned worktree and build artifacts afterward.
