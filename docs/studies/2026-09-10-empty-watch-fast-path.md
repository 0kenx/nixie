# Empty long-watch propagation

## Registration

The closed complete engine saved instructions without establishing a wall
gain. Before another representation rewrite, remove unnecessary ownership
transfers on a trigger with no long watchers. The production driver currently
takes and restores its vector even when empty. Its scanner wrapper is inline
and already guards the actual scan call: this is **not** a claim that an empty
trigger calls the out-of-line watcher kernel. Earlier arena-locality and
single-exit tail-scan studies already argue against repeating those changes.

Move the existing tick calculation before vector extraction, then continue
for an empty list when the ordinary kernel is selected. Preserve binary-first
propagation, binary-conflict requeue, bounded-step behavior, phantom binary
ticks, saturating counters, and final conflict-free-prefix publication. Active
observers and the legacy test oracle keep their original empty-list path.
No unsafe code, watch selection, search policy, or new per-entry operation.
Kissat `src/proplit.h` and CaDiCaL `src/propagate.cpp` likewise charge the
trigger before scanning; an empty long list cannot skip binary implications.

Preflight: compare full solver state with the existing legacy oracle for empty
lists, reserved empty vectors, binary chains/conflicts, phantom-only lists,
stable/focused tick saturation, budgets, backtracking, and LRAT. Run the SAT
suite with ordinary and all features, strict SAT Clippy and formatting. Inspect
generated code before measurement: the empty path must bypass vector clearing,
restoration and drop handling, with no second list lookup on the nonempty path.
If this fails, stop without running a solver cost cell.

Budget: at most two new cost invocations, j3037 then (only after passing)
summle, using cached production controls instead of retiming them. Portable
release Rust 1.96.0 / LLVM 22.1.2 and retained lockfile
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`.
CPU 15 Atom, seed 0, MAXC=10000000, PRINT_MODEL=1, NIXIE_SWEEP=0,
NIXIE_DEFINITIONS=0; other study overrides cleared. Whole-process user
instructions are primary; grouped user cycles, wall, faults, switches and
off-CPU fraction are secondary. Warm input/binary, anonymous tmpfs output,
GNU time 1.10, emergency 300 s. No own build/test overlaps measurement.
Store every start and completion once; no repeat on a bad timing.

Reuse production j3037 record `0ec1f4bfcfe8f5f9` and summle record
`02d916e9af5fe4da`, both `fd01d0b`. Require identical complete stdout,
>=99.9% PMU coverage, zero major faults and <=5% off CPU. A screen advances
only with <=0.95 instructions and <=0.95 wall versus its retained control;
different measurement windows limit any causal wall claim. Validate any SAT
model independently. Unproved UNSAT is recorded unknown/unverified.
Reuse requested-mode Kissat context; no new reference runs. A negative uses
retained profiles and current assembly to account for remaining/introduced
costs; no extra profile or source tuning is licensed by this screen.

Source promotion additionally requires the full workspace build, nextest,
doctest, Clippy, fmt, documentation and installed Z3 4.16.0 parity gates.
Otherwise archive the source and commit the finding, with no solver change.
