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
instructions and no usable wall regression, or >=10% lower cycles **and**+wall with at most 2% extra instructions. The latter permits a small cost
for useful memory overlap, declared before seeing this candidate's data.
Both paths need an independently checked SAT model on si2 and full
workspace build/tests/docs/Clippy/format plus Z3 4.16.0 differential parity
before production landing. These are bounded engineering screens, not a
new suite geomean or a heuristic improvement claim.

A failed cost screen gets one LBR diagnostic with the previous quality
gates. At most one measured repair is allowed, only if code and profile
identify removable introduced overhead. No width/distance/seed search or
replacement profile. Stop and archive if that repair misses the gate.
