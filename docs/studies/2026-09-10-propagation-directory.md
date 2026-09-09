# One owning propagation directory per literal

## Registration

Continue the Kissat wall-cost task after the
[raw-header rejection](2026-09-10-raw-header-pipeline.md). The next target
removes separate metadata directories instead of adding lookahead state.
This is a representation change with exact search-state equivalence, not
a heuristic comparison. Local Kissat `src/proplit.h` combines binary and
long entries in one stream; Nixie must retain its binary-before-long order,
stable long-watch filtering, eager pair normalization and immediate moves.

Put one literal's long-watch Vec, binary overflow Vec, primary start/live
length and phantom tick count in one owned, cache-line-aligned 64-byte row
on this host. Keep the binary primary edge pool contiguous and retain the
existing Vec allocation/growth rules. `WatchLists` owns the rows and primary
pool; crate-private binary methods replace the separate solver graph field.
Public watch APIs remain available. No shared pointer, global state, custom
Send/Sync assertion or new unsafe block is needed for this first version.

Retain separate logical watch, binary and phantom extents. Watch rollback
must restore only watchers/phantoms and preserve binary edges; binary
clear/rebuild/compaction must preserve watchers/phantoms. A full solver
rebuild must discard old watch buffers but retain reusable binary storage.
Explicit primary starts must preserve physical slack after individual
retirement, and count/extent/fill overflow must fail before corrupting any
neighbor. Directory growth, clone, scope transitions, HBR, observer fields,
LRAT and exact tick charges must retain their original semantics.

Before measurement: default and all-feature SAT tests, strict SAT Clippy,
format, independent Vec-model directory tests, channel-isolation tests,
packed rollback/growth/compaction tests and native Rayon owner-move tests.
Inspect generated code for a single directory base, direct row addressing
and ordinary inlined destination append. Record scanner/driver code size
and stack use. Repair correctness or a missed intended code transformation
before timing; do not benchmark a known-broken representation.

Use ordinary portable release/perf, the retained lockfile and Rust 1.96.0 /
LLVM 22.1.2. Main's SAT source still matches qualified fd01d0b; later changes
are outside the DIMACS solving path. Reuse its j3037 cost record
`0ec1f4bfcfe8f5f9` and Kissat 4.0.4 record `45a3c8f2e3057841`. Use the same
once-only harness/configuration as those records: CPU 15, seed 0, CaDiCaL
preset, disabled sweep/definitions, MAXC=10000000, printed models, warmed
binary/input, anonymous tmpfs output and whole-process user instructions /
cycles. Clear unrelated overrides. No own build overlaps measurement.
Require byte-identical complete Nixie stdout, >=99.9% PMU coverage and
<=5% off-CPU for usable wall. Quality failure is inconclusive and retained,
not permission to retry. Record exact source/binary identities in benchstore.

Start with **one candidate j3037 cost cell**. Advance to one paired si2
confirmation only with >=5% fewer complete instructions and no usable wall
regression, or >=10% lower usable wall and cycles with at most 1% extra
instructions. Independently check si2's SAT model; require identical Nixie
output, no more than 3% si2 instruction/wall regression, and >=5% two-input
wall improvement. These are bounded engineering screens, not population
estimates or a new Kissat-suite geomean. Unchecked UNSAT stays unverified in
the store. Full workspace build/nextest/doc-test/Clippy/fmt/docs and fresh
installed-Z3 4.16.0 parity are required before production landing.

A failed cost screen gets one LBR diagnostic with the retained quality
checks. Allow at most one cost-directed measured repair if code and profile
identify removable introduced overhead; record its design before timing.
No layout/width/seed sweep or timing retry. Include growth/rebuild/rollback,
larger destination-directory stride and memory overhead in the diagnosis.
A rejected mechanism is archived with its source and finding on main;
do not infer a win by adding older compact-buffer/lookahead percentages.

## Unified Vec directory result

Prototype `b8ad94676fa91dfe73c4ee40b804e838f9f7c0ca` implements one 64-byte
row with ordinary Vec owners. The driver uses the same directory base for
primary start/live, overflow length, watch transfer and phantom count.
Prefix/suffix bodies shrink from 938/1120 to 914/1106 bytes, with local stack
88/88 -> 72/72 bytes. The driver shrinks 3781 -> 3345 bytes and local stack
248 -> 184 bytes. Ordinary destination append remains inlined; growth stays
cold. The assembly reference is cached a64b285, whose hot source matches
qualified fd01d0b; a64b285 itself is not the qualified cost control.

| j3037, seed 0 | Qualified fd01d0b | Unified directory |
|---|---:|---:|
| Whole-process user instructions | 254596496994 | 252295643327 |
| Whole-process user cycles | 164287697694 | 172818143306 |
| Wall | 36.13 s | 37.94 s |
| Off CPU | 0.332% | 0.343% |
| Conflicts | 330565 | 330565 |
| Propagations | 323390316 | 323390316 |

Full stdout is byte-identical. Instructions fall only **0.904%**, while wall
rises **5.010%** and cycles **5.192%**. This fails both advancement paths;
no si2 cell runs. Both PMU counters have 100% coverage, with no major faults
and 266 involuntary switches. Foreign builds remained active, so even the
passing off-CPU gate does not isolate their cache/frequency effects from the
source change. The instruction reduction alone is below the declared bar.
Cost record `0f6af0d08b424fea` keeps unchecked UNSAT unverified/Unknown.

The [flamegraph](assets/2026-09-10-propagation-directory.svg), diagnostic
`fae6d9c787402405`, passes with 16095 samples, no loss/throttle, 100% PMU
coverage, two kernel-labelled samples and 0.0124% unresolved self weight.
Prefix/suffix self shares are 23.03%/25.29%; the driver is 23.43%.
Directory setup is still hot: `0x4ac9a`, the overflow-length load following
the live-count load from the same row, has 5.28% self weight. Destination
capacity checks `0x63342` and `0x63775` have 3.83% and 1.25%; append's second
store `0x631dd` has 3.03%. Samples can skid across dependent loads/stores;
these shares do not prove cache misses or quantify removable instructions.
Other persistent costs include binary value access (around `0x4ad6d`),
blocker checks and clause-header loads. Profile counters cover a sampled
prefix, not a second complete-cost cell. Output matches after removing only
the registered terminal memory line.

The representation reduces keyed directories but increases a destination's
header stride **24 -> 64 bytes**. Total metadata rises from 60 bytes per
literal across the old arrays to 64 bytes in one aligned row. The primary
pool and individual watch/overflow allocations remain separate; co-location
cannot remove their dependent accesses. Terminal geometry is unchanged:
3441696/7684864 arena live/capacity bytes, 1914480 reference bytes,
821424/2316608 watch bytes and 511456/573776 BIG bytes, with 27 compactions.
Peak RSS is 35892 KiB; this is not evidence of a whole-process memory win.
Rebuild is only 0.19% self weight in this diagnostic, so cold rebuild savings
cannot plausibly explain a large total gain on this input.

Preflight passes **781** default SAT tests and **1045** all-feature SAT tests
(one existing skip), strict SAT Clippy and format. Tests compare mixed
operations against independent Vec lists, preserve channel extents through
rollback/growth/reset/compaction, protect physical span boundaries and
builder overflow, and move prebuilt solver/oracle pairs into Rayon. No new
unsafe block was added. The source/binary identities, verified source bundle,
assembly, logs and raw measurements are retained in `precompile/b8ad946/`.
No full workspace qualification or production source landing is claimed.

### One combination repair, registered before implementation

The new larger directory stride is concrete introduced overhead at the
profile's hot lookup/append sites. Combine this unified directory with the
previously audited 16-byte `CompactVec` owner from
[compact adjacency](2026-09-10-compact-adjacency.md). Two compact owners plus
explicit start/live and phantom count give a **48-byte row** with native
alignment, reducing the unified row by 25% and old aggregate metadata by 20%.
Keep the field order and primary pool; remove forced 64-byte alignment.
Rows may straddle cache lines. This is one ownership representation with a
derived size, not a layout/width sweep.

Retain that wrapper's cold checked growth, exact Vec allocation ownership,
initialized slice borrows, deep clone and type-bounded Send/Sync contract.
Retain this experiment's binary driver: do not also import the older
borrowed-binary loop or change traversal. The public watch mutable-buffer
type becomes `WatchBuffer`, with initialized slice access; callers requiring
`&mut Vec<Watcher>` need adaptation. The interaction being tested is compact
ownership reducing the larger unified destination stride and watch transfer,
not the sum of two old speedup percentages.

Before timing, run default/all-feature SAT and exact-state tests, strict
SAT Clippy/fmt, fresh strict-provenance Miri for the five non-Rayon buffer
cases and directory operations excluding native Rayon, and native Rayon
owner/solver checks. Inspect a 48-byte row, 16-byte owner transfer, inlined
ordinary append and cold growth in both scanners. Require no extra metadata
indirection, driver local stack <=184 bytes and scanner local stack <=88
bytes (the qualified control). Failure ends the repair before timing.

If these pass, spend at most **one** repaired j3037 cost cell against the
retained qualified control, with the original advancement gate. No second
profile, replacement cost cell or further repair follows. A passing repair
may use the originally registered si2 confirmation and full qualification;
a failing one closes this experiment. No compact/unified production code
is promoted solely for smaller metadata or a passing ownership test.

## Compact combination result: rejected

Repair `78894d04c924778f6109e84cb22385d01c60646f` passes all preflight gates.
The row is 48 bytes, both owners are 16 bytes, and indexing uses one base
plus `literal * 48`. The prefix/suffix bodies are 909/1079 bytes with 72/56
bytes of local stack; the driver is 3331 bytes with 184 bytes of local
stack. Ordinary append remains inlined, with checked growth out of line.
Watch transfer now moves a pointer and two u32 counts. There is no new
metadata pointer chain. The binary driver and watch filtering algorithms
are unchanged from the first prototype.

| j3037 repair, seed 0 | Result | Repair / qualified control |
|---|---:|---:|
| Whole-process user instructions | 250851301161 | 0.985290 |
| Whole-process user cycles | 167718521410 | 1.020883 |
| Wall | 36.86 s | 1.020205 |
| Conflicts | 330565 | 1.000000 |
| Propagations | 323390316 | 1.000000 |

Complete stdout is byte-identical to both the qualified control and first
prototype. Instructions fall **1.471%**, while wall rises **2.020%** and
cycles **2.088%** against control. Relative to the 64-byte prototype, the
repair uses 0.57% fewer instructions and 2.85% less wall. Neither comparison
establishes the required improvement over qualified production. The repair
fails both advancement paths. No si2 cell or second profile runs.

Cost record **`bc753cbcec20ffa2`** has 100% coverage, 0.353% off CPU,
36.66 s user / 0.07 s system, zero major faults and 253 involuntary switches.
Peak RSS is 34560 KiB. Foreign builds were active again; the passing quality
gate does not make these different-window wall deltas solely source effects.
Against retained requested-mode Kissat this single input remains **2.043x
wall**, **2.072x instructions**, and **1.838x cycles/conflict**. These are
context from existing cells, not a new suite geomean or a paired Kissat run.
Unchecked UNSAT remains unverified/Unknown in the canonical store.

Default SAT tests pass **788**; all-feature SAT nextest passes **1052**, one
existing skip. Strict SAT Clippy and format pass. Fresh Miri 0.1.0
(485ec3fbcc, nightly 2026-06-11), seed 42 with strict provenance, passes the
five compact-owner cases and all eight non-Rayon directory cases. The latter
includes mixed operations against independent Vecs after every step, plus
rollback and binary compaction/overflow guards. Native Rayon buffer and
prebuilt solver/oracle tests pass in the SAT suites. This does not claim
strict-Miri coverage of Rayon itself; its previously documented Crossbeam
limitations are unchanged. The reused wrapper confines unsafe operations
to allocation ownership, initialized slices and capacity-checked append,
with Send/Sync bounded by the entry type.

Source bundle/patch, both binaries, compiler/lock hashes, assembly preflight,
Miri/test/build logs and the complete raw cell are retained under
`precompile/78894d0/`. Both prototype bundles were verified against main's
reachable `42c78bd8` prerequisite. The study consumed exactly **three new
performance invocations**: two candidate cost cells and the first candidate's
LBR diagnostic. The qualified control and Kissat cells were reused throughout.
No source is promoted; full workspace qualification and SMT parity are not
claimed for rejected prototypes.

## Cost conclusion and next scope

This combination tests the interaction requested by the user: compact owners
reduce the unified directory's introduced stride and owner-transfer footprint.
It still saves only **11.58 whole-process instructions per processed trail
literal**, from 787.27 to 775.69. Those are amortized process totals, not
isolated propagation instructions. Smaller ownership metadata does not
remove a binary edge visit, blocker lookup, clause-header/literal dependency,
watch destination append or assignment. The assembly still performs those
consumers, and the first profile locates substantial cost there. There is
no second profile establishing which one explains the repair's wall delta.

Close this ordinary/compact unified-directory experiment. Do not repeat it
with another alignment, field order, owner width or growth factor, and do
not add its percentages to the old compact-adjacency result. New representation
work needs a way to remove an actual consumer or amortize it across useful
work, rather than another metadata-only size reduction.

The larger algorithmic route remains the recorded
[propagation-work audit](2026-09-09-propagation-work-audit.md): reduce the
amount of formula/replay work presented to propagation. Its circuit result
rules out scheduled inprocessing and those exit resets as a sufficient
explanation, and the [explicit relation-solving mode](2026-09-09-direct-relation-solve.md)
already gives a substantial measured structural reduction on that input.
The missing cheap gate/definition preparation before elimination is another
existing source-audit target; local Kissat `gates.c` tries equivalence, AND
and ITE recognition before its embedded definition solver, while Nixie's
`elim_try_variable` goes directly to the optional embedded path after its occurrence
cutoff. This is not a new discovery, a default-enablement claim, or an
invitation to flip thresholds. A follow-up must price exact recognition,
proof/model reconstruction and changes in propagation volume with the
appropriate matched controls. These targets remain open; this negative
layout experiment does not close the Kissat gap.
