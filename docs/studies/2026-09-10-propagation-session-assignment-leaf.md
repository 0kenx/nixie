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
