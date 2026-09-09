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
