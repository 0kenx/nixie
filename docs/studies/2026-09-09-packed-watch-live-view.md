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

## Result: combination fails the wall gate

The repaired candidate is source `2ad799671e0aa62e8c23380a678408f78a5fafdc`.
It includes the independently landed `ac13904` correction; its SAT-side
addition is an inactive terminal CNF-dump environment check. Study variables
were cleared, and complete output is identical to the retained control.
Release SHA-256 is
`56e98fff9cc427567dd8f9f49c53cee639546e77b5fd63ff09f25e57f90ee092`;
perf SHA-256 is
`767223c009b20c4224e9a123aaf38fbaa8721eee73ca804b6735cdfbf6a85fb6`.

The final representation uses ordinary typed fields again: no u64 shifts,
bit masks or packing-specific unsafe code. The suffix's unchanged-entry
copy is one eight-byte load/store. Its blocker is read first, so this still
reloads the entry on a hit. The prefix only reads or updates the blocker
word. Destination insertions and changed suffix entries retain two word
stores. Reason exits read the stable header ID directly. Suffix/prefix text
is 954/772 bytes versus 1120/938 in the retained control.

| Original circuit | Wall s | Conflicts | Wall/conflict µs | Peak RSS KiB |
|---|---:|---:|---:|---:|
| compact-watch control, retained | 7.98 | 162529 | 49.10 | 33228 |
| combined candidate | 9.58 | 162529 | 58.94 | 35476 |
| mode-matched Kissat, retained | 5.55 | 277061 | 20.03 | not recorded |

Candidate/control wall is **1.20050** and candidate/Kissat is **1.72613**.
The model checks, complete Nixie output matches, and both Nixie arms solve
at cap. Candidate user/system time is 9.47/0.06 s, off-CPU fraction 0.52%,
37 involuntary switches and zero major faults. The circuit advancement gate
fails, so **si2 was not run**. Exactly **two new solver invocations** ran:
the wall cell and the prescribed diagnostic profile. No control was rerun.

This is a failed engineering screen, not an established causal 20% source
regression: the control and reference come from earlier time windows.
The off-CPU gate does not control clock, cache or shared-resource effects.
Neither a smaller binary nor fewer sampled-prefix instructions overrides
the failed wall criterion. The combined source is not promoted to main.

## Candidate flamegraph and cost diagnosis

The [interactive flamegraph](assets/packed-watch-live-view.svg) contains
3968 cycle samples on CPU 15, zero loss/throttle/unthrottle records and 100%
group scheduling coverage. There are 3966 user-mode samples and two samples
with kernel-mode/unknown self attribution (0.0504%, inside the registered
0.1% limit). LBR supplies 1916 caller stacks; incomplete chains are labeled.
The SVG was parsed as XML.

The sample-read prefix totals are **41.556 G cycles / 58.076 G instructions**,
versus retained diagnostics of 36.320 G / 59.887 G: +14.42% cycles and
-3.02% instructions. These are sampled-prefix diagnostics, not complete
solve counter ratios. The profile's enclosing elapsed time is diagnostic,
not a second primary wall observation.

| Self region | Candidate cycle share | Candidate instruction attribution share |
|---|---:|---:|
| compaction suffix | 31.83% | 26.68% |
| no-removal prefix | 18.85% | 16.44% |
| subsumption | 18.98% | 22.27% |
| search body | 4.86% | 4.21% |
| outer propagation | 3.73% | 3.27% |

The prefix's instruction attribution drops by about 8.7%, while suffix and
subsumption instruction attribution stay near the retained observations.
Cycle attribution rises across these and largely unchanged search/conflict
routines. This does not isolate a new local instruction sequence as the
cause of the wall increase. The retained-buffer layout can alter allocation
and cache behavior; host effects are also unresolved. Neither is established
by this noncontemporaneous comparison.

The suffix's deleted-flag branch receives 21.30% of its cycle attribution;
the destination blocker store receives 8.08%. In the prefix, the deleted
branch receives 19.65% and the blocker-value access 16.18%. These samples
include instruction skid and are not branch-miss probabilities. Removing
validation at rare reason exits leaves the main dependent loads and watch
movement in place. Another change to just copy width is not justified by
this profile.

The scratch defect is real: the regression failed because a normal round
returned zero schedule capacity. With the repair, warm and cold-buffer
controls match clause/trail/watch state and proof transcripts across full,
zero-budget, limited-budget and repeated rounds. Allocations survive and
marks are zero at every exit; occurrence contents are cleared before reuse.
The final default and observer preflights each passed ten focused tests.
Full production qualification was not run after the wall gate failed.
Retaining capacity did not remove the remaining subsumption lookup/membership
work. Peak RSS rose by 2248 KiB in this observation, while terminal arena,
watch, BIG, reference sizes and 13 compactions match the previous profile.
There is no `Solver::clone` path; inspection did not establish a hot clone
cost from this repair. Memory retention and allocator effects remain real
cost terms to price in a follow-up.

## Next algorithmic combination: immutable connected-clause payloads

The candidate's subsumption entry-lookup region (`0xab522..0xab58b`)
receives **36.39% of subsumption self-cycle attribution**, or **6.91% of the
whole profile**. The literal-membership region receives 32.14% / 6.10%.
The entry path resolves an occurrence's clause ID through `refs`, validates
the arena extent, reads the header and checks the cold-activity identity
range even though subsumption only needs live literals. This remains inlined
machine code; it is not a conjectured out-of-line accessor overhead.
These percentages are upper opportunity indicators, not removable savings.

A stronger candidate is to materialize connected subsumer literals **once
per round**, in compact round-owned storage, with their stable clause IDs
for proof/promotion. Occurrence lists then address those immutable payloads.
This can share the repaired persistent scratch allocation and replace the
repeated ID/ref/header validation chain; it does not change the signed-mark
membership algorithm or connection policy. Price the extra copying, index
width, bounds checks, clearing and retained memory before benchmarking it.
Do not simply add old percentage gains from the watch and scratch changes.

The initial lifetime audit supports this direction but is not yet a complete
implementation proof:

- The size-sorted schedule contains each live clause ID once. A clause is
  connected only after its own deletion/strengthening decision.
- A later subsumption outcome retires the current candidate. The connected
  subsumer can be promoted to original; promotion changes metadata, not its
  literal payload or stable ID.
- Strengthening mutates only the current candidate, reorders its watches and
  resets the propagation head. `remove_literal_opts` does not propagate or
  collect the arena during this round. The connected copy must be made
  **after** this mutation, including a ternary-to-binary transition.
- Proof strengthening rewrites the current candidate's proof ID. A cached
  subsumer must keep its stable database ID and resolve the current proof ID
  when emitting; caching a proof ID has a different lifetime contract.
- `retire_clause` purges the current candidate's edges/reasons and sets its
  deleted flag. It does not retire earlier connected clauses. Binary-graph
  checks still need their existing liveness/order behavior.
- No cached membership may become evidence in the next round. Clear its
  contents before any later use, including after scope changes or compaction.
  Idle cached IDs must never be dereferenced. Persistent capacity is not
  persistent evidence.

The local CaDiCaL `subsume.cpp` schedule/one-watch loop supplies the semantic
reference: process a candidate, then connect it for later candidates.
A future implementation must enforce the immutability contract, compare
complete states/proofs against the existing index and cover promotion,
strengthening, budget exits, repeated rounds and scopes. No additional
performance cells are registered or run here.

## Retained evidence

Canonical records are wall `298eeff494ef5279` and profile
`e81f4bb87fc15f60`. Runners, immediate start/completion files, complete output,
model validation, source/binary hashes, CPU-affinity evidence, raw LBR data,
folded stacks, phase/subsumption IP attribution and disassembly are under
`precompile/2ad7996/benchmark/packed-watch-live-view*`. The prototype patch is
retained there against main base `057f028`; the rejected u64 preflight's
binaries/assembly are under `precompile/4799685/`. The production baseline
remains the already-qualified compact-watch implementation. Owned temporary
worktrees and scratch files are removed after recording this verdict.
