# Whole watch copies, borrowed live views and subsumption scratch

The [direct compact-watch result](2026-09-09-direct-watch-identity.md)
reduced the observed two-input wall cost, but leaves original circuit and
si2 at 1.44× and 1.66× mode-matched Kissat. Its qualified original-circuit
profile attributes 49.51% of self cycles to the two watch phases. Generated
code copies eight-byte entries as two words and repeats live-header
validation when returning a unit/conflict reason. Instruction-pointer
samples near these operations are cost clues, not removable-cycle estimates.

## Combined implementation hypothesis

Store the complete reference/blocker pair in a private u64 representation.
This adds no tags and narrows neither 32-bit value. The reference constructor
stays inside the memory module; observer builds retain their separate stable
ID and 12-byte layout. The expected benefit is a single unchanged-entry copy;
price extraction, bit updates, register pressure and destination insertion
as well. In particular the no-removal prefix must still read only a blocker
on its hit path.

Borrow the live header together with its disjoint mutable literal slice.
The existing arena-origin/relocation contract establishes the live slot;
exclusive borrowing keeps it valid through scan completion. Copy the stable
reason ID out before returning to assignment/HBR, which may grow the arena.
This should remove repeated validation at reason exits without loading an
identity on every hit. It does not remove the deleted check or change eager
literal normalization, watch order, ghost retention, ticks or assignments.

The semantic references are the archived scalar oracle and local Kissat
`src/proplit.h`, `src/watch.h`, and CaDiCaL `src/watch.hpp`: retain a live
clause through the payload operation and encode watch words without changing
the propagation policy. This experiment keeps Nixie's own parking and
normalization order.

Before solver measurement, check both feature layouts, full-width encodings,
relocation/snapshot behavior and the existing exact-state kernel oracle.
Inspect both generated phase bodies. If the intended copy and validation
changes do not materialize, repair the implementation or record that failure
without a solver screen. This is an engineering representation combination;
no search heuristic or policy choice changes, and no interaction coefficient
is inferred from older single-component results.

## Registration: at most three new solver invocations

Use the same Rust 1.96.0, LLVM 22.1.2, pinned Cargo.lock SHA-256
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`,
portable release/perf profiles and offline locked build as the retained
control. No native flags, PGO or RUSTFLAGS override. Identify the immutable
prototype source and binary hashes before execution; a prototype is not a
qualified production landing.

All cells use CPU 15 (atom), original inputs, seed 0, MAXC=10000000,
CaDiCaL preset, `NIXIE_SWEEP=0`, printed model and a 300-second emergency
cap. Clear other study environment variables. Verify no competing pinned
userspace job before starting. Use complete-target GNU-time elapsed with
anonymous tmpfs output, warm input/binary reads and <=10% off-CPU fraction.
Wall is the user's primary engineering target; never make it a policy input.
Every start/completion and result goes into the result store once, including
failed cells; never retime an inconvenient control or candidate.

1. Candidate original-circuit wall. Reuse compact-control record
   `a64df562525fa2df` (7.98 s; source `02cc03c`, identical production source
   to qualified `d1290db`) and Kissat `dffd0cb6beb45f5f` (5.55 s). Require
   a checked model and byte-identical complete Nixie output.
2. If timing quality and output identity pass, one candidate original-circuit
   LBR profile, whether the wall result wins or fails. Use fixed cycle period
   10472903, user-only grouped atom cycles/instructions, sample reads/running
   time, explicit CPU samples, 128 pages and LBR. Require zero loss/throttle,
   >=99.9% scheduling coverage, >=1000 samples and <=0.1% unresolved self
   attribution. Print terminal memory only and remove that diagnostic line
   when comparing to the wall output. Failed profiles stay failed. Use its
   flamegraph and code to price a negative/neutral mechanism before deciding
   on a specific repair or an opportunity limit.
3. Only if circuit candidate/control wall <=0.95 and both previous quality
   gates pass, candidate original-si2 wall. Reuse compact-control record
   `68494a8004e0cdca` (2.02 s) and Kissat `c3bb0064cbaa9d2d` (1.22 s).
   Require checked model, exact Nixie output and timing quality.

Advancement requires the two-input geometric mean candidate/control wall
<=0.95 and si2 ratio <=1.03. Report each ratio, candidate/Kissat wall,
wall/conflict and solved-at-cap. Retained controls come from earlier time
windows: the off-CPU gate cannot remove frequency/cache/shared-resource
noise. This is a bounded engineering screen, not a population speedup.
A positive source landing also requires the repository's full correctness
checks; reference parity is a correctness gate only, not the performance
target. A negative result lands its cost diagnosis and explicit next action
in documentation, without promoting the unqualified prototype source.

## Pre-measurement repair and combined scope

No solver performance invocation has run. Ordinary SAT tests passed 1002
cases and observer tests passed 1028 (one skipped in each layout). These
include exact-state propagation/inprocessing checks, complete models and
independent LRAT checking.

The literal-u64 prototype `4799685` fails a generated-code obligation.
Its suffix and prefix shrink from 1120/938 to 937/786 bytes and reason exits
become single header-ID loads. Suffix unchanged copies and destination
insertion become single eight-byte operations. However the prefix now loads
and shifts a complete entry on every blocker hit and combines/stores both
words on blocker refreshes. This adds work to the no-copy phase. Do not
benchmark that representation merely because the overall text is smaller.
Its binaries and assembly are retained under `precompile/4799685/`.

Repair it with typed reference/blocker words and a fixed-size safe slice
copy only for unchanged entries in the compaction suffix. Retain direct
blocker field access elsewhere and the borrowed live view. Inspect the new
assembly before proceeding; no packing-related unsafe access is needed.

The audit also found an actual defect in the old subsumption scratch reuse
(`03b869d`, still present at `d1290db`): normal rounds take `schedule`,
`occs` and `mark` out of the solver, then drop them. Only the no-candidate
return stores them back. Thus the advertised normal-round capacity reuse
never happens. Restore all three buffers after normal and budget exits.
The next invocation clears schedule/occurrence contents before consulting
them; every marked candidate is unmarked before reaching an exit. Test
warm buffers against a cold-buffer control across complete, zero-budget,
limited-budget and repeated rounds, including spilled occurrence lists and
proof/state identity. This prices a concrete lifecycle repair, not the
previous unrelated analysis-scratch experiment.

Include that repair in the same upcoming candidate, before its first wall
cell. The existing three-invocation limit, retained controls, quality gates,
5% combined wall advancement gate and exact-output requirements stand.
Report performance for the combined implementation only. Keeping buffers
live may increase later peak memory and clone cost; retain peak RSS and
inspect allocation/drop work in the candidate profile. No individual or
superadditive speedup is inferred. Source qualification must cover the
scratch cleanup invariant as well as the watch representations.
