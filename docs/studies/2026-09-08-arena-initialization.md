# Arena initialization prerequisite for conflict-cost work

Inspection of first-UIP clause bookkeeping found a memory-safety defect in
`ClauseArena` at `6333f83`. This repair is a correctness prerequisite, not a
claimed performance improvement. No benchmark cells were run for the repair.

## Defects and repair

The backing storage is `Vec<u64>`, with a padding-free 12-byte header, four-byte
literals, and eight-byte slot alignment. An even number of literals leaves
four trailing bytes. Allocation wrote only the header and literals before
increasing the vector length, exposing a partially initialized integer.
Compaction independently did the same when creating its 16-byte tombstone.
The derived arena clone can read these entire integer elements.

Rust requires every newly exposed vector element to be initialized before
[`Vec::set_len`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.set_len).
An uninitialized integer is an invalid value under the
[Rust validity rules](https://doc.rust-lang.org/reference/behavior-considered-undefined.html).
Both writing sites now clear the final aligned word before writing their
payload and exposing it. This needs one word store, including for odd-sized
clauses where the following payload write covers the whole word.

The same allocation audit found unchecked size arithmetic and a debug-only
reference-width assertion followed by a release-mode null fallback. The
allocation now validates length, rounded size, offset and full extent before
reservation or mutation. It reserves address space for compaction's permanent
tombstone and respects both the u32 reference width and Rust's allocation
extent bound. Exhaustion raises an explicit panic; it cannot silently become
a missing clause. Kissat's `src/arena.c::kissat_allocate_clause` likewise treats
exhaustion of its representable arena as a fatal resource error.

Compaction now validates live ordering/nonoverlap and representable destination
sizes before relocation, reserves before changing refs, and rejects invalid
refs instead of silently deleting them. Its extent read uses subtraction and
division to avoid overflowing when validating a corrupt length. Copy bounds
remain checked in release builds. Reference construction rejects misalignment
and offsets without room for a header.

## Invariants examined separately

- Both vector-length extension sites: allocation and compaction tombstone.
- Header layout: its fields cover all 12 bytes; a compile-time size assertion
  protects this premise. `Lit` is transparent over u32 and needs four-byte
  alignment; the existing u64 buffer and eight-byte strides provide it.
- Growth and cloning: reservation only exposes capacity; complete slot writes
  precede the vector length change. Cloning reads initialized elements.
- Shrink: lowering the header length leaves old literal bytes initialized.
  Compaction destinations already contain initialized bytes, including their
  padding; only the new tombstone can expose previously spare capacity.
- Relocation: live slots preserve order and move downward. Database refs are
  rewritten synchronously, and existing tests check watcher relocation and
  deleted IDs reaching the tombstone. The repair changes no clause content,
  learning rule, watch selection, tick accounting or search schedule.
- Failure behavior: unsupported extents and invalid compaction inputs raise
  errors; the focused tests check that preflight failures leave refs/storage
  unchanged. This is not a claim that arbitrary corrupted solver state can be
  recovered or that a wrong SAT/UNSAT verdict was observed before this fix.

## Verification

Two regressions were first run against the old implementation. Both failed,
showing the unwritten padding still contained four `0xa5` bytes. The tests
initialize spare capacity to that pattern first, so inspecting the old result
in these regressions does not itself read uninitialized memory.

Six new tests cover allocation padding, empty-arena tombstone padding, numeric
extent boundaries without multi-GiB allocation, exhaustion before mutation,
invalid/duplicate compaction refs, and growth/shrink/repeated compaction/clone
with explicit literal and metadata comparisons. All 30 arena tests pass.

The all-feature workspace build, clippy with warnings denied, formatting,
documentation with warnings denied, **10,718 nextest tests** (12 skipped), and
**111 doc tests** (29 ignored) pass. Fresh Z3 **4.16.0** differential parity
reports **169 Correct, 0 Disagree, 1 Inconclusive**: `array_unique.smt2` is
Nixie UNSAT / Z3 Unknown, not counted as a match. This is the available Z3
version, not the historical 4.15.4 snapshot comparator. Miri was unavailable;
no Miri result is claimed. Logs, source/lockfile fingerprints, parity records
and release binaries are cached under this commit's `precompile` entry.

The next performance candidate combines repeated learned-clause metadata
updates during conflict analysis. It must preserve usage saturation, exact
activity arithmetic, tier transitions, LRAT order, clause literals and search
counters. Its cost screen will use committed sources and a small fixed panel.
