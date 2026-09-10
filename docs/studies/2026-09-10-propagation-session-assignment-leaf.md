# Propagation session with a narrow scan and assignment leaf

## Registration

Continue closing the wall/cycles gap against Kissat. Combine the archived
long-list kernel's narrow scan with the earlier complete engine's lifetime
contract. The rejected per-list version repeatedly reserved queue capacity,
constructed views and checked callback gates; its suffix also reloaded arena
and value bases. The wider sweep exposed constraints as a required regression
case. Reducing retired instructions alone did not reduce elapsed time.

Create one exclusive fixed-domain trail/arena/watch-directory session per
ordinary propagation call. Separate mutable truth bytes from assignment-only
queue/metadata state. Keep long-list scanning non-inlined, with a small
non-inlined assignment leaf so metadata and queue-update state need not stay
live through watch/tail scans. Pass fixed truth/arena storage directly to the
scan, preventing owner-field reloads after unit assignment. Preserve the
no-removal prefix and single transition to compacting suffix. Keep the BIG
representation and binary-before-long order. Do not change scheduling ticks,
clause order, assignments, conflict selection, budgets or search heuristics.

Reserve at most the existing trail length plus the variable-domain bound
before borrowing; the old prefix may contain duplicate entries. Only currently
undefined variables can append during the session, and no backtrack, domain
growth, arena relocation or callback is possible through it. Publish only
initialized queue elements and the current propagation head on all returns
and unwind. Keep borrowed live clause identity disjoint from its mutable
payload. No custom Send/Sync, global pointer or input-dependent recursion.
LRAT, HBR, reason counters and active observers retain the complete old path;
select that path once per propagation call. DRAT output remains unchanged.

Reference audit: Kissat inlineassign.h and propsearch.c keep undefined-only
assignment and a local propagation cursor; CaDiCaL propagate.cpp updates the
conflict-free prefix differently on conflict and fixpoint. Nixie's existing
head requeue and budget-abort behavior remain authoritative. The prior fixed
queue and borrowed-reason safety tests are reusable, not evidence that this
new composition is correct without retesting.

Before any cost invocation, run default/all-feature SAT tests, the exhaustive
scalar-state oracle, callback/observer checks, focused strict-provenance Miri
on the queue and disjoint arena borrow, native Rayon owner moves, strict SAT
Clippy and formatting. Inspect portable Rust 1.96.0 / LLVM 22.1.2 perf assembly:
reservation and callback gates must be outside the list loop; assignments must
not grow the queue or revalidate their reason; arena/value owner bases must
not be reloaded per blocker/miss/tail visit. Record stack/text size rather than
using an arbitrary frame-byte ceiling as a speed oracle. One source-directed
preflight repair may address a specific missed transformation. A remaining
miss ends at preflight without cost, rather than an annotation sweep.

Use Nixie's **default sweeping enabled** (explicit NIXIE_SWEEP=1), CaDiCaL
preset, NIXIE_DEFINITIONS=0, seed 0, MAXC=10000000 and PRINT_MODEL=1. Clear
other study overrides. Keep the retained lock/compiler, portable release,
CPU 15 Atom, warm input/binary, anonymous tmpfs output, GNU time 1.10 and
grouped user instructions/cycles/branches/misses. Whole-process instructions
are the primary engineering counter; unchanged scheduling/work counters
establish workload equivalence, not machine cost. Retain the 300-second cap,
>=99.9% PMU coverage, zero major faults, <=5% off CPU and audited idle guards.
No owned build may overlap timing. Shared load/older controls remain limits.

First price constraints against the cached sweep-enabled production control
14d6f38d3c5c5cb9 (53147102832 instructions, 45156742562 cycles, 10.01 s).
Require >=5% lower instructions, usable wall and cycles. Only then run fresh
production/candidate crn and candidate/production j3037 pairs, reusing any
compatible existing cell. Each must preserve complete stdout and regress
neither instructions nor qualified wall/cycles by more than 3%, with >=5%
three-input wall improvement. Finally permit one noL candidate against the
sweep-enabled 36990e8006fa9aac control (389171744416 instructions,
231268638827 cycles, 50.99 s), with the same <=3% regression limit. Maximum
six new cost cells, spent conditionally; no repeated cells, seed search or
reference reruns. Use retained Kissat 4.0.4 with the user's disabled-pass
options for target context. Never join sweep-disabled Nixie cells into the
default-mode comparison. This is an exact-trajectory engineering screen;
no matched null is required for an unchanged search path.

A cost rejection permits one cycle/LBR diagnostic on the rejecting input,
period 10472903, requiring CPU 15, >=99.9% coverage, >=1000 resolved samples,
zero loss/throttle and <1% unresolved self weight. Its elapsed time is not a
replacement cost cell. Diagnose the actual introduced cost and possible
underlying improvement; no measured repair or second profile follows this
experiment. Preserve rejected source/findings on main and reusable results in
precompile. Production promotion requires the full workspace verification
gates and fresh installed-Z3 parity, with Z3 used only for soundness. Clean
owned worktrees/branches/scratch when finished.

## Initial preflight and the one code-generation repair

The first portable perf binary has a 68-byte assignment leaf and scan phases
of 664/833 bytes, each with 56 local stack bytes plus six saved registers.
Truth-byte reads now use the live r8 base throughout blocker/first/tail tests;
the previous per-probe value-owner reload is gone. Assignment does not grow
the queue or revalidate the reason. However, the arena base is restored after
tail exits (0x64204/0x64307 and 0x64ff2), with a saved arena-plus-tail-offset
base loaded at 0x650a5. The mutable output cursor remains live throughout the
suffix although it is written only at the final exit. Fixed coordinates
removed owner indirection but did not eliminate the register-pressure cost.

Use the one preflight repair to remove that unnecessary live cursor pointer.
Each phase returns a kept-count/conflict result by value; the suffix receives
the first hole index, from which its initial read/write positions follow.
There are no unit yields, so neither intermediate cursor publication nor an
externally mutable cursor is needed. Keep exactly one prefix-to-suffix
transition, stable compaction, counters and conflict suffix semantics. This
is a control-state representation change, not an inline-annotation sweep.
Re-run the affected correctness/codegen gates before any cost invocation.

The initial all-feature library suite passed 812 tests; six focused Miri
tests passed, including both binary spans and exact long-visit ledgers.
The initial default suite reached a missing external-corpus link, and the
all-feature integration build exhausted the data filesystem. These are
environment failures, not solver verdict failures. Link the primary checkout's
existing corpora and move only this experiment's target directory to the root
filesystem, retaining its path through a symlink. The ignored Cargo.lock was
also copied from the frozen benchmark cache before all qualification builds;
the initial auto-generated-lock compile check is not qualified evidence.

The first source form of the cursor repair still lowers the returned
`{ usize, Option<ClauseId> }` through a hidden output pointer: its three
scalar components defeat the intended two-scalar return. That pointer is
again live in the suffix, and the arena restores remain. Complete the same
control-state repair using the arena's already reserved `ClauseId::NULL`
for the no-conflict result, yielding `{ usize, ClauseId }`; decode it back
to Option at the driver boundary. Live arena identities cannot be NULL
(allocation checks ID exhaustion), so this adds no ambiguous result. This
is an additional compile of the planned cursor removal, explicitly recorded
before timing, not evidence that the first source form removed the pointer.

## Verdict: stop at code generation

**Reject this source at preflight. Zero cost cells and zero profiles ran.**
The scalar-pair return now uses rax/edx, so the cursor-removal repair works.
The composition also removes per-list callback/reservation checks and the
previous per-tail-probe truth-owner load. It nevertheless retains the
arena-base spills that the registered gate required it to remove. Smaller
code and fewer owner indirections do not establish a wall improvement; no
new Nixie/Kissat ratio follows from this experiment.

| Portable perf body | Initial bytes | Final bytes | Final local stack bytes |
| --- | ---: | ---: | ---: |
| Assignment leaf | 68 | 68 | 0 |
| No-removal prefix | 664 | 569 | 40 |
| Compacting suffix | 833 | 785 | 56 |
| Outer propagate, including fallback | 5,181 | 5,098 | 280 |

Each scan phase additionally saves six registers (48 bytes), and suffix
execution retains the prefix and outer frames. These are static assembly
sizes, not dynamic traffic measurements or independent speed predictions.
The final perf executable SHA-256 is
`d76fe044ac49f8bada48b4fe5332a87314ce5fb57628c5d1a2dcf75dbddce5f6`.
Rust is 1.96.0 / LLVM 22.1.2 with the registered lock. No release cost binary
was built after the code-generation rejection.

### The remaining dependency is in traversal state

In the final suffix, the blocker, first-watch and every tail truth load use
the live rcx base. Header access at 0x64fb6 uses the live r9 arena base.
However, entering a tail search loads the saved arena-plus-20 base from
`[rsp+0x28]` at **0x65011**. The tail index then overwrites r9 at 0x6501d.
After a true-tail exit, **0x6513b** restores the arena from `[rsp+0x70]`;
watch moves and units restore it at 0x6507b and 0x6511d. The prefix similarly
restores its arena/derived bases at **0x641a7/0x641ac** after a true tail.
These are stack restores of fixed coordinates, not reads through a mutable
arena owner. They still leave the hot dependency targeted by preflight.
There is no arena reload on every blocker hit or every tail probe; the
failure is specifically on misses reaching the tail and their exits.

The assignment leaf has no allocation, reason lookup or callback. Its 68
bytes are not its whole caller cost: prefix units preserve watch/truth/false-
literal state around the call at 0x6427e, then restore bases. Suffix units do
the equivalent at 0x650f6. The source boundary hides assignment metadata but
does not remove the traversal state that must survive it. Likewise, watch
destination growth remains a separate permitted allocation on watch moves.

The suffix retains a watch-array base, length, kept index, current read index
and next read index. Its clause-tail traversal adds a base, length and index.
This is a concrete place to reduce simultaneously live coordinates rather
than rearrange function boundaries again. A further candidate should split
the two watched literals from the tail, then walk the tail with a bounded
cursor/end pair and update the selected slot directly. A disjoint mutable
tail iterator may express this safely without an extra integer index or new
unsafe code. A fixed-slice compaction cursor can similarly carry read/write
positions and an end pointer; recover the final kept count only at exit.

The local references support this traversal shape: Kissat `proplit.h` uses
p/q/end watch cursors and r/end_lits for tails; CaDiCaL `propagate.cpp` uses
i/j/eow and k/end. Their saved search positions and different normalization/
replacement policies are separate algorithms and must not be imported into
an exact-trajectory implementation screen. Preserve Nixie's eager watched-
pair normalization, first eligible tail literal, true parking, move order,
unit/conflict behavior and untouched conflict suffix. If pointer compaction
needs unsafe, isolate its initialized-range/ordering proof in the borrowed
view and test empty/end/overlap cases with strict-provenance Miri. No raw
cursor may survive the session or transfer between Rayon owners.

That representation change is **unimplemented and unmeasured** here. Its
potential benefit is fewer live coordinates and fewer indexed compaction
checks, not a promised fraction of the Kissat gap. It must price any new
dispatch or call-state preservation. Do not repeat this exact session/leaf
combination, sweep inline annotations, or count reduced text as a win. A
flamegraph was not authorized for a preflight rejection and would not change
this static finding; prior profiles are not relabelled as this candidate's.

## Verification and limits

The final source passes **812 all-feature SAT library tests**, including
the 1,296-case scalar-state oracle, and **nine default kernel tests**. Those
checks cover callback exclusions, owner moves through Rayon, model/LRAT
checks, backtracking, budgets and preservation of conflict tails. Strict SAT
all-feature/all-target Clippy and workspace formatting pass. Final-source
strict-provenance Miri passes the two work-ledger tests and the default
unit/conflict-tail test (three final-source checks, seed 42).

Earlier source forms additionally passed 1,018 default SAT nextest tests
(one existing skip) and six focused Miri tests covering queue publication on
unwind, duplicate old trail entries, fixed storage, borrowed clause identity
through mutation/relocation, resumption and both binary spans. The queue and
arena primitives did not change in the return-state repair. These earlier
passes are not relabelled as a full final-source integration run. An initial
final-source test filter matched zero tests; the corrected `kernel_tests`
filter ran the nine tests above. The failed disk/corpus setup runs remain in
the cache as described above.

Full workspace qualification, SAT doctests and fresh installed-Z3 parity were
not completed for this rejected prototype. No solver source is promoted to
main. Preserve the final source patch, exact assembly, perf binary, lockfile
and qualification logs; commit this finding and reconstructible source to
main, then remove the owned experimental checkout, branch and build storage.
Future measurements retain default Nixie sweep ON and the user's requested
Kissat options; this rejection does not weaken the baseline-mode correction.

## Reconstructible archive

Archived source is `ebaef56db3f160a812772654f112e06258b0ee53`, based on
registration `f87a05575082efa5b634350cc8d668c8d82a5189`. The
[source patch](assets/2026-09-10-propagation-session-assignment-leaf.patch)
reconstructs tree `ab4c8e873bb21203413397d86391ef7aa8adcde3` in a
temporary Git index without modifying any checkout. The
[code-generation listing](assets/2026-09-10-propagation-session-assignment-leaf-codegen.txt)
contains both final scan phases, the assignment leaf and the full outer
propagation body. The [audit](assets/2026-09-10-propagation-session-assignment-leaf-audit.json)
records hashes, individual qualification results and incomplete gates.

`precompile/ebaef56/` retains the verified source bundle, original patch,
matching perf executable, frozen lockfile, initial/repaired/final assembly
and raw preflight logs. The source bundle requires reachable registration
f87a0557. This is an experimental archive, not a qualified production binary.
The solver patch is landed only as a study asset; production source stays
unchanged and the experimental branch is removed after archival.
