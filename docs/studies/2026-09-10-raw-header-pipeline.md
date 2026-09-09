# Deferred classification of lookahead headers

## Registration

Continue toward lower Nixie wall/cycles per conflict against mode-matched
Kissat. The [previous experiment](2026-09-10-miss-header-lookahead.md)
loaded the next header early but also branched on its deletion flag before
current literal work. Repairing hit dispatch reduced instructions without
rescuing wall. This experiment tests that specific remaining dependency,
not a different lookahead distance or another parameter sweep.

Use the consecutive-miss loop with one private, unclassified header word.
Its first eight initialized bytes contain length, LBD, flags and usage;
identity at offset eight is not needed. Decode length/flags at consumption,
with native-endian layout handled explicitly. Use `ClauseRef::NULL` as the
pending-slot sentinel, avoiding a separate Option discriminant. Check null
before any header read, deletion before any literal view. Pending metadata
belongs to the same exclusive arena scan that forms the literal slice;
no caller can supply a cached length or access the arena concurrently.

The fixed-trail boundary, eager normalization, watch order, reasons, ticks
and all search schedules remain unchanged. Duplicate references may change
literals but never a prepared header. Discard preparation on every return
and prefix-to-suffix transfer. No global state, volatile reads, architecture
prefetch intrinsic, unsafe Send/Sync assertion, or shared raw pointer.

Before timing: default and all-feature SAT tests, scalar-oracle exact-state
checks, strict SAT Clippy/format, focused strict-provenance Miri, native
Rayon owner-move checks and assembly inspection. Add regressions for raw
header decoding and deferred deleted/null classification. The assembly must
load next metadata before current literals, consume it without reloading,
and have **no next-header-content-dependent branch before current work**.
The ordinary hit loop must have no pending-state dispatch; local stack must
not exceed the previous repair's 104/120 bytes (prefix/suffix). If the
compiler fails this preflight, repair the representation before measuring,
or stop at an assembly-backed negative result.

Reuse qualified fd01d0b j3037 control `0ec1f4bfcfe8f5f9` and Kissat 4.0.4
reference `45a3c8f2e3057841`; main's SAT source matches that control, with
only unrelated arithmetic-builder changes in the compiled core dependency.
Reuse the previous once-only harness and configuration: CPU 15, seed 0,
CaDiCaL preset, disabled sweep/definitions, warmed binary/input, anonymous
tmpfs output, whole-process user cycles/instructions. Require identical
complete stdout, >=99.9% PMU coverage and <=5% off-CPU for usable wall.
Record all cells once in benchstore, with actual source/binary identities;
no own build overlaps measurements. Quality failure is inconclusive, not
permission to retry. No fresh control or Kissat j3037 run.

Advance to one paired si2 confirmation only with either >=5% fewer complete
instructions and no usable wall regression, or >=10% lower cycles **and**
wall with at most 2% extra instructions. The latter permits a small cost
for useful memory overlap, declared before seeing this candidate's data.
Both paths need an independently checked SAT model on si2 and full
workspace build/tests/docs/Clippy/format plus Z3 4.16.0 differential parity
before production landing. These are bounded engineering screens, not a
new suite geomean or a heuristic improvement claim.

A failed cost screen gets one LBR diagnostic with the previous quality
gates. At most one measured repair is allowed, only if code and profile
identify removable introduced overhead. No width/distance/seed search or
replacement profile. Stop and archive if that repair misses the gate.

## Raw-header result

Candidate `3029772537555151c1de6024bb4e1c608e88ae9a` passes the assembly
preflight. Prefix/suffix bodies are 1289/1477 bytes, with 104/120 bytes of
local stack and six saved registers. The suffix loads next metadata at
`0x63adb` and current literals at `0x63b21`; the prefix does so at
`0x640ac` and `0x640e7`. Neither path tests the next header's contents before
current work. Consumption uses the saved word, without rereading the header.
The prefix ordinary-hit loop has no pending dispatch or reference load.
This establishes the intended code transformation, not effective memory
overlap or a speedup.

| j3037, seed 0 | Qualified control | Raw-header candidate |
|---|---:|---:|
| Whole-process user instructions | 254596496994 | 272085784765 |
| Whole-process user cycles | 164287697694 | 280667245517 |
| Wall | 36.13 s | 68.38 s, quality failed |
| Off CPU | 0.332% | 9.418% |
| Conflicts | 330565 | 330565 |
| Propagations | 323390316 | 323390316 |

The complete stdout is byte-identical. Instructions are **1.06869** of
control, failing both advancement paths; both PMU counters have 100%
coverage. An unrelated checkout's build overlapped the run. With 3391
involuntary switches and 61.45 s user/0.49 s system time, the candidate fails
the registered <=5% off-CPU wall gate. Wall/cycle differences must not be
attributed to this source change. Do not replace the failed wall cell with
another invocation or with a profile duration. Canonical cost record:
`f2cb161b3c22054d`. Its printed UNSAT remains unverified/Unknown in the store
because no original-CNF proof was checked.

The [flamegraph](assets/2026-09-10-raw-header-pipeline.svg), record
`b9e2965649dc85dd`, passes the diagnostic gates: 21398 samples, 100% coverage,
zero loss/throttle, six kernel-labelled samples and 0.0280% unresolved
self weight. Scanner self share is 52.61%, propagation driver 21.05%.
Attribution concentrates at the blocker read (7.99%), current-header test
(5.55%), and stores immediately following next-header loads (5.93% suffix,
2.04% prefix). These stores depend on the preceding arena loads; sample
skid prevents reading their percentages as removable stack-store costs.
The profile's counters cover only its sampled prefix and are not a second
cost measurement. Its full output matches after removing the registered
terminal memory line; arena/watch/BIG geometry is unchanged.

Default SAT tests pass **784**; all-feature SAT nextest passes **1048**, one
existing skip. Strict SAT Clippy and workspace format pass. Five focused
arena tests pass strict-provenance Miri (nightly 2026-06-11), including raw
native-endian decoding, deleted/null consumption, duplicate references,
layout changes between scans and owning thread moves. Native Rayon tests
move prebuilt solver/oracle pairs. Both ordinary portable binaries use Rust
1.96.0 / LLVM 22.1.2 and the same lockfile as control. Source/binary identities,
preflight logs, assembly and raw measurements are in `precompile/3029772/`.

### One code-directed repair, before further measurement

The loop rereads the following watcher after having already read it to
prepare its header. In the prefix, the repeated range test/reference load
appears at `0x64133..0x6414e`; the looked-ahead hit also reads its watcher
again in the suffix. The existing fixed-trail and stable-compaction
invariants guarantee that current work cannot modify this unread entry.
Carry that exact copied watcher to the next visit instead. This removes
duplicate input state from the pipeline without changing its distance,
header representation, literal access or mutation order. Do not fabricate
a replacement blocker or identity, including observer fields.

Inspect assembly before spending the one repair cost cell: repeated watcher
loads must disappear, neither phase may increase its stack footprint, and
all original raw-header ordering gates must still hold. If these fail,
record the assembly result and stop without another solver invocation.
Passing assembly still needs exact-state SAT tests and the original cost
gate. No additional profile is authorized for this repair.

## Watcher reuse repair: stopped at assembly

Repair `27e73cbbe37e78d02246fa64e00e5293fd61d058` carries the exact watcher
copy read by preparation. It removes the second reference read and the
looked-ahead hit's second watcher read. The ordinary prefix hit loop remains
free of pending dispatch; next-header loads still precede current literals
without testing the next header's contents. However, prefix local stack
grows **104 -> 120 bytes**, failing the declared preflight. Suffix stack
stays 120. Bodies change from 1289/1477 to 1315/1449 bytes: almost no combined
text reduction. No release cost cell or second profile was run.

The source saves a read but extends the copied watcher's lifetime across
current-clause work. In the generated prefix the prepared reference is
spilled at `0x6416e` and recovered at `0x64104`, alongside current reference,
raw header, next-hit state and both cursor positions. Null/deleted control
flow also retains extra state moves. This is a register-pressure trade,
not elimination of the pipeline's bookkeeping. It gives no basis for
claiming that the saved read is a net improvement. SAT default/all-feature
tests, strict SAT Clippy and format pass again; the arena API and unsafe
blocks are unchanged from the five passing Miri cases above.

The failed assembly gate ends this repair. Do not keep changing defaults,
inlining, pending encodings or distances to obtain another timing cell.
The raw-header version removed the previously identified early liveness
branch and still added 6.87% complete instructions. The repair then traded
a repeated read for more live state. Together these results close this
one-entry software-lookahead approach under the current scan boundary;
they do not prove a hardware latency model or rule out every possible
memory-overlap algorithm.

## Underlying cost to address next

The retained qualified j3037 control and Kissat reference contain **1.478x
processed trail literals**, **1.153x conflicts**, and **2.103x whole-process
instructions** for Nixie. Instructions amortized per processed literal are
therefore 1.423x Kissat's. These are accounting ratios with different phase
coverage, not isolated propagation-kernel measurements. They reinforce the
[earlier work-volume audit](2026-09-09-connected-residual-payloads.md#the-wall-gap-also-contains-more-work-per-conflict):
similar conflict counts do not mean comparable propagation work. Current
single-input evidence must not be presented as a new suite geomean.

A concrete representation target outside this rejected pipeline is the
**per-literal propagation directory**. Source and the current diagnostic
show the driver reading separate binary span/live/overflow arrays, taking
a long-watch Vec, and reading a separate phantom tick count. Address
`0x4afbf` maps to binary-span setup, `0x4b014` to overflow metadata and
`0x4b1fc` to watch-list ownership transfer. The driver's 21.05% self share
also includes real binary traversal and assignment; it is not all removable
directory overhead. For example, `0x4b0dc` maps to binary literal-value
access, not directory setup.

The previous [compact adjacency experiment](2026-09-10-compact-adjacency.md)
fused binary metadata but retained separate binary and long-watch
directories. A distinct design would co-locate one literal's binary
start/live extent, overflow owner, long-watch owner and phantom count,
and lend their disjoint views to propagation together. With ordinary Vec
owners this is approximately one 64-byte row on this host, rather than
several unrelated keyed loads. Preserve binary-before-long order, immediate
watch moves, exact phantom accounting, primary-span physical boundaries,
growth, rebuilds and scope snapshots. Do not intermix the edge streams or
copy Kissat's differing watch-order semantics.

This is an **unimplemented source-audit direction**, not an accepted speedup
or a registered performance run. Its preflight must price larger destination
directory strides and cold rebuilds, and establish fewer metadata reloads
in generated code. Combining it with compact ownership would need an actual
interaction: compact rows reducing the state/traffic of a unified lookup,
not adding the old negative experiments' percentages. The reference
`kissat/src/proplit.h` instead scans binary and long entries in one watch
stream; it is useful for the ownership/load audit, but directly copying that
ordering would change Nixie's trajectory and require heuristic controls.

## Closure and artifacts

Exactly **two performance invocations** ran: one candidate cost cell and
one LBR diagnostic. The repair used zero performance invocations. No fresh
Kissat/control cell, si2 confirmation, seed sweep, timing retry or full
workspace qualification was added. **No production solver change is
landed, and no reduction of the Kissat wall gap is established.** Full
workspace and Z3 qualification are reserved for a candidate passing the
advancement gate; these SAT preflights do not substitute for them.

`precompile/3029772/` preserves release/perf binaries, exact source patch
and bundle, lockfile, identity manifest, tests/Miri/codegen logs, once-only
measurement harnesses, raw results and profile/address analysis.
`precompile/27e73cb/` preserves the untimed repair's perf binary, source
patch/bundle and preflight evidence. Both bundles require the reachable
registration `ce1c01c04b86bcde7b7cda772b998baac3f3389e`. Experimental
worktree, branch and temporary files are removed after archival.
