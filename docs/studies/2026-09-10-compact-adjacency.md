# Compact owning adjacency buffers and fused binary metadata

## Design and safety contract

The user explicitly permits small, focused unsafe blocks compatible with
Rayon. This experiment changes representation, preserving propagation and
inprocessing order, reasons, tick accounting and all search choices.

Replace the three-word per-list `Vec` header with an owning pointer and
checked u32 length/capacity for non-zero-sized Copy entries: 16 bytes instead
of 24 on a 64-bit host. Allocation/deallocation remains Vec's responsibility;
small unsafe blocks transfer ownership, expose initialized slices and append
within established capacity. Growth never truncates a count. Allocation
failure restores the old owner before reporting failure. No pointer escapes
the owning buffer or survives a safe mutable borrow. Clone is deep.

Fuse each literal's binary span start/live length with its compact overflow
buffer in one 24-byte record, replacing three separate arrays totaling 32
bytes per literal. The start is explicit, so reading code-1's span end and
special-casing literal zero disappear. Long-watch headers also shrink to
16 bytes. Keep the CSR edge pool and each growable list independently owned;
avoid flat-pool relocation/defragmentation and delayed-move costs that failed
previous studies. This first representation retains separate long-watch and
binary directories; it does not claim complete adjacency unification.

The wrapper is Send only for Send entries, Sync only for Sync entries. All
mutation requires exclusive access, with no global mutable cache or shared
allocator metadata. Test moving prebuilt solvers into a Rayon pool, parallel
independent solves, deep copies, empty buffers, alignment, growth, bounds,
retain/panic and ownership transfers. Test ordinary and observer watch widths.
Use the existing exact-state and independent LRAT oracle tests, plus a safe
Vec-based container oracle. Consult local Kissat vector/propagation and
CaDiCaL watch semantics; no C/C++ dependency is introduced.

## Bounded engineering screen

Before execution, inspect generated code for compact header moves and fused
binary metadata loads. Commit/cache exact source, compiler, lock and binary
identities. Portable release/perf, CPU 15, CaDiCaL preset, seed 0,
MAXC=10000000, PRINT_MODEL=1, NIXIE_SWEEP=0, NIXIE_DEFINITIONS=0;
clear all other study overrides. Full-process user instructions/cycles,
GNU-time wall, warm input/binary, anonymous tmpfs output, <=10% off-CPU,
>=99.9% counter coverage. No own build overlaps measurement.

At most five new solver invocations: one fresh compatible qualified Nixie
j3037 control if absent from the store; one candidate j3037 cell; one
candidate j3037 LBR profile to diagnose the result; then, only if j3037 wall
improves at least 10% and instructions at least 5%, one candidate si2 cell
and one compatible qualified si2 control if absent. Reuse requested-mode
Kissat records and any compatible controls; never retime a recorded cell.
Require exact complete Nixie output and check every SAT model. Report raw
UNSAT without an original-CNF proof as unverified/unknown in canonical data.

The profile requires zero lost/throttled samples, >=1,000 samples, >=99.9%
coverage/user samples and <=0.1% unresolved self. Retain a negative's cost
diagnosis; no parameter sweep follows. This is a bounded same-trajectory
engineering screen, not a multi-seed heuristic or population claim.

Advance only if both anchors retain exact output, the two-input wall
geomean improves at least 5%, and si2 regresses no more than 3%. Before any
production source landing, complete all workspace build/test/doctest/Clippy/
fmt/doc checks and installed-Z3 4.16.0 parity as a correctness gate. Keep
the target Kissat wall. Archive rejected code and commit its finding.
