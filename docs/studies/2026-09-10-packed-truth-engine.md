# Packed truth values in the complete propagation engine

## Registration

The elimination-product census leaves learned-clause traffic as the larger
target. Ordinary propagation already elides arena extent validation; deleting
those checks again is not an implementation opportunity. The current watcher
also already carries a direct arena reference. Keep both facts explicit.

Test a different representation: two truth bits per variable instead of two
signed bytes. Bit `Lit::code()` records whether that literal is true. Both
bits clear means undefined; assignment clears the pair and sets exactly one
bit. Both bits set is forbidden. A variable's pair never crosses a u64 word.
Use the packed table as the sole hot truth representation, including ordinary
and diagnostic paths, growth, reassignment, chronological backtracking and
scope resets. Preserve the existing cold VarInfo record and every result.
General value queries retain all three states. Hot true-only queries test one
bit directly; do not compute a ternary value just to test positivity.

Combine this with the archived complete borrowed-reason engine from d8e7805.
Its 19.93% j3037 instruction reduction did not establish a wall improvement;
the held-out wall screen failed. Here its fixed borrow keeps the packed table
available through an entire propagation pass. Price the combined source only.
The specific hypothesis is smaller truth-table footprint under arena/watch
traffic, with fewer calls and ownership transfers offsetting added decoding.
No claimed additive or superadditive gain, and no unchanged-engine retiming.
The dependent lookup still exists: footprint reduction is not its removal.

Reference semantics: local Kissat proplit.h/inlineassign.h and Nixie's scalar
oracle assign a literal and its negation consistently, test blockers before
deleted headers, and preserve binary-before-long propagation. Keep Nixie's
normalization, parking, ordering, reasons, conflict prefix, phantom ticks and
all budgets unchanged. This is a representation experiment, not a heuristic
or a new choice requiring randomized trajectory controls.

Preflight before any cost invocation: independently compare packed values
against signed-byte truth across word boundaries, all states/polarities,
growth, clear/reassign and boundary indices; exact scalar engine comparisons,
models and independent LRAT checks; default/all-feature SAT tests, doctests,
strict SAT Clippy and formatting. Run strict-provenance Miri on the packed
table and fixed propagation view, plus native Rayon owner movement. Any
unchecked operations must be local to domain-checked fixed borrows, with no
unsafe Send/Sync or shared global state. Inspect portable generated code:
true-only blocker paths use one word load and a bit test, with no ternary
conversion, allocation or second value table; no extra per-entry traversal.
Record all code/stack growth. At most one source-directed preflight repair;
no width, encoding, threshold or annotation search after seeing cost results.

Budget: at most THREE new solver invocations. First, candidate j3037 cost;
second, one candidate j3037 LBR diagnostic after a completed identity-matching
cost, whether the cost is positive or negative; third, candidate crn only if
j3037 has <=0.95 production instructions and <=0.95 usable wall. Confirmation
requires <=1.03 instructions/wall on crn and <=0.95 two-input wall geomean.
No measured repair follows. If code preflight fails, stop without cost runs.

Use retained Rust 1.96.0 / LLVM 22.1.2 and Cargo.lock SHA-256
3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439,
portable release/perf, no native flags or PGO. CPU 15 Atom, seed 0,
MAXC=10000000, PRINT_MODEL=1, NIXIE_SWEEP=0, NIXIE_DEFINITIONS=0; clear
all other study overrides. Reuse fd01d0b j3037 control 0ec1f4bfcfe8f5f9,
crn from borrowed-engine-heldout, and requested-mode Kissat 4.0.4 context
45a3c8f2e3057841. No new controls or references. Archive immutable source,
binary/input hashes, start/completion, raw outputs and canonical cells once.
Never repeat a failed/used cell or infer timing from diagnostic duration.

Whole-process user instructions are primary, user cycles and wall secondary.
Use grouped explicit atom events, GNU time, warmed input/binary and anonymous
tmpfs output, with a 300-second emergency cap; no own builds during timing.
Require exact complete stdout, >=99.9% PMU coverage, zero major faults and
<=5% off CPU. Constrained sleeping threads covering CPU15 must retain their
identity and runtime; wait for active constrained foreign jobs, never stop
or move them. Different windows and shared frequency/cache load remain limits
even when those checks pass. SAT needs an original-CNF model check; unproved
UNSAT remains unknown/unverified in the canonical store.

The one LBR diagnostic uses period 10472903, 128 pages, user atom cycles and
instructions, sampled CPU/running-time reads, zero loss/throttle, >=99.9%
coverage and >=1000 samples with <=0.1% unresolved self weight. Its purpose is
to locate decode/update versus retained propagation cost, not retime the cell.
Full workspace build/nextest/doctests/Clippy/fmt/docs and installed Z3 4.16.0
parity precede any production landing. Otherwise archive the prototype, land
the finding on main and remove owned temporary artifacts.

## Initial preflight and the single repair

Initial prototype 6dfb2f56 passes 1,024 default SAT tests and 1,049 all-feature
tests (one ignored each); the latter preceded two additional boundary tests.
Strict SAT Clippy and doctests pass. Strict-provenance Miri passes the packed
word-boundary test and three fixed-queue tests. Ordinary test suites include
native Rayon ownership moves. No solver cost invocation has run.

The portable perf engine is 3,908 bytes with 248 local stack bytes, versus
3,098/216 in the archived byte-valued complete engine. True-only blocker tests
already use a word load and BT. At 0x64594..0x645ab, however, a binary query
performs both bit tests, SETB/SBB and a signed comparison to reconstruct a
ternary value before checking its positive exit. At 0x645b7..0x645d0, a new
propagation computes and clears the entire pair even though its unsafe
contract already requires both bits to be zero.

Use the one preflight repair to express the complete engine's state tests
directly: test the literal's bit, then its opposite only when needed, and set
only the known-empty assignment bit. This keeps the exact true/undefined/false
branch order and preserves every unrelated bit in the word. General Trail
assignment still clears the pair because it permits reassignment. Recheck
the affected unsafe queue path with Miri, exact-state tests and generated code
before measurement. No encoding/word-width change or gate relaxation.

On the 14,400-variable input domain the hot truth table is 3,600 bytes instead
of 28,800 bytes. That footprint change is exact; any cycle saving is unknown.
Word read/modify/write also couples independent variables sharing a word and
may introduce store dependencies. Bit indexing, these writes, code/stack
growth and general ternary queries all belong in the cost of this candidate.
