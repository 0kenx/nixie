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

## Initial code generation and one preflight repair

The bounded entry-token API scalarizes: no cursor-owner load remains in the
watch loops. Prefix/suffix bodies are 620/577 bytes with 72/56 local stack
bytes, plus six saved registers each. The suffix loads its three cursor
coordinates once at entry; prefix passes it an aggregate only at the first
hole. The tail iterator lowers to a moving slot pointer and remaining byte
bound, two coordinates instead of base/length/index. It retains the same
truth tests and selected-literal order.

Both truth and arena bases now remain live on blocker, first-watch and
true-tail paths. Prefix uses rcx/r14; suffix uses rdx/r9. The old suffix
per-tail-entry derived-base stack load and ordinary true-tail arena restore
are absent. Prefix still restores a destination-directory argument at
0x64242 and recomputes arena+16 at 0x6424a after true tails. The suffix
restores its derived base after a watch move, and assignment/growth calls
still preserve state. Those remaining costs must be measured, not hidden
behind the representation improvement.

Use the single preflight repair on a newly exposed finish-path defect:
LLVM emits memmove at 0x6509c after every completed suffix even though its
remaining length is zero. Add an explicit read==end return before suffix
copying. This is a specific failed empty-copy elimination, not a source
encoding sweep or a measured repair. Preserve overlapping memmove for actual
unvisited conflict tails and rerun the affected Miri/code-generation gates.
No cost invocation has occurred.

## Pre-cost amendment: withdraw the optional empty-copy change

The explicit empty-copy exit grows the suffix to 584 bytes and does remove
the zero-length memmove. It also changes register allocation: 0x64f67 now
loads arena+16 from `[rsp+0x30]` on every miss reaching the tail. The original
577-byte suffix held this derived base in r13. The main arena and truth
bases remain direct in both versions, but the optional change violates the
registered derived-base requirement. It is not eligible for the cost screen.

Withdraw that optional repair and freeze the **original cursor implementation**,
which already passed the required traversal shape. Retain its zero-length
memmove as a cost to price. This explicitly amends the earlier instruction
to stop after a failed repair: the failed repair is discarded before timing,
and the already eligible initial implementation receives the single cost
screen. Both source forms and their assembly are archived. No cost has run,
no thresholds or instance order change, and neither timing both variants nor
a further code-generation repair is permitted. Repeat affected final-source
qualification, including the wider observer-layout Miri tests, before cost.

An initial all-feature test build also found that the new fixture constructed
Watcher directly without its observer-only identity field. Use the existing
Watcher::new constructor; this changes test setup only. Native all-feature
qualification then passes 1,054 tests, and the guarded-copy source passes
eight focused Miri checks. These passes are labelled by source form rather
than silently transferred to the selected unguarded-copy implementation.
