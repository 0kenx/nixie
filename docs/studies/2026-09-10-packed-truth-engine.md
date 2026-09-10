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

## Final preflight and safety

The single repair produces candidate `f1d9c7440ac978f3835ee02621c66a53a5135f40`,
tree `79896c4a1901f7d8e6c6b04fc000f7f718d5aa43`, based on `552eeded`.
The complete engine shrinks to **3,450 bytes**, still larger than the archived
byte engine's 3,098 bytes. It retains **248 local stack bytes**, versus 216.
Six saved registers are additional in both cases. Blocker queries use a word
load and BT; complete-engine state queries no longer reconstruct signed
ternary values, and undefined assignment no longer clears the pair.

There is remaining generated work: the primary binary loop reloads the same
word at `0x64588` and `0x645ad`; tail scans do likewise at `0x648c0/0x648d6`
and `0x64b93/0x64ba8`. Binary and other-watch true tests also prepare an
assignment mask before knowing whether they will assign. Long paths carry
the original word/mask across the tail scan, increasing live values and
spills. These costs were retained in the measured source, not edited after
seeing the result.

Final qualification passes **1,051 all-feature SAT tests**, **1,024 default
SAT tests** (one existing skip each), **two doctests** (one ignored), strict
SAT all-feature/all-target Clippy and workspace formatting. The suites cover
exact scalar/full-engine state, original-CNF models, independently checked
LRAT cases, compaction/growth/requeue and native Rayon owner movement.
Strict-provenance Miri, seed 42 on nightly 2026-06-11, passes the new packed
word-boundary borrow test and all three fixed-queue tests. The latter are
rerun after the OR-only assignment repair.

The representation audit covers more than the fast loop. Every literal pair
is contained in one initialized u64; growth preserves old pairs and zeroes
new/padding bits. General assignment clears both bits before setting one,
so reassignment retains the old API semantics. Clear/backtrack/reset clear
the entire pair, including chronological backtracking that retains a lower
level assignment out of trail order. The independent signed-byte oracle
checks all states and polarities across word boundaries, growth and
reassignment. Safe queries preserve out-of-domain behavior; unsafe hot
queries require a checked literal domain.

The fixed propagation borrow excludes growth and unassignment. Its unsafe
append requires an undefined variable, so OR sets one bit without changing
any neighbor; it cannot retain a stale opposite bit. No word reference
escapes a query. The inherited arena identity/payload borrows remain
disjoint, and the queue publishes only initialized entries on return or
unwind. No global state or unsafe Send/Sync is introduced. These checks
support the archived prototype; they do not replace the full workspace and
Z3 gate required for a production change.

## Cost screen: rejected

One candidate j3037 cost invocation produces record **`e9668ba31fb529ea`**.
The complete stdout is byte-identical to qualified production: **330,565
conflicts**, **323,390,316 propagations** and **695,639,361 ticks**. Its SHA-256
is `a904b7f02cd4dc6ac5abd11a0754072e9f32af0ab18409dc293edf1242c1cb9b`.
The reported UNSAT remains **unknown/unverified** in the canonical store;
this cost invocation did not independently check an original-input proof.

| Arm | Whole-process user instructions | User cycles | Wall |
| --- | ---: | ---: | ---: |
| Qualified production `fd01d0b`, reused | 254,596,496,994 | 164,287,697,694 | 36.13 s |
| Packed complete engine `f1d9c74` | 245,376,048,341 | 223,187,907,601 | 49.29 s |
| Candidate / production | **0.96378** | **1.35852** | **1.36424** |
| Requested-mode Kissat 4.0.4, reused context | 121,059,163,625 | 79,144,759,362 | 18.04 s |

The **3.62% instruction reduction fails the 5% screen**, and measured wall is
**36.42% higher**, also failing. The conditional crn invocation does not run.
No new control, Kissat invocation, replacement cell or measured repair runs.
Kissat has 286,784 conflicts and 218,808,022 propagations; its row provides
target context, not identical-work attribution or a suite geomean.

All four PMU events have 100% coverage. Candidate user/system time is
48.75/0.32 s, off CPU **0.446%**, major faults zero, peak RSS 35,596 KiB;
there are 82 involuntary and 229 voluntary switches. Constrained sleeping
threads retain identity and runtime. All owned compilation ended before
timing. These satisfy the registered timing checks. The retained control
comes from a different window, however: unpinned foreign work, frequency and
shared cache effects remain attribution limits. Passing those checks does
not prove the source alone caused the observed 36.42% wall increase.

For context, the archived byte-valued complete engine executed
203,854,720,117 instructions on the same trajectory. Its wall failed quality
and cannot be used as timing evidence. The packed combination gives back
most of that earlier instruction reduction; no separate packed-table
ablation was run, and no additive interaction estimate is established.

## Required flamegraph and cost review

The single diagnostic produces record **`2bee68451ea612ec`** and the
[interactive flamegraph](assets/2026-09-10-packed-truth-engine.svg).
All **22,055 samples** are on CPU 15, with 100% read coverage, zero lost or
throttled records and **0.03174% unresolved self weight**. The output matches
the cost run after removing exactly one terminal memory-statistics line.
The diagnostic's elapsed time and sampled-prefix counters are not a second
cost result. Grouped counter-read deltas, rather than the slightly different
sum of programmed periods, weight the offline attribution.

The complete engine receives **72.46% of sampled self cycles**. Search,
subsumption, shrinking/minimization and backtracking receive 4.36%, 2.97%,
2.84% and 2.62%. The scalar watch fallback receives 1.64%. The
[address report](assets/2026-09-10-packed-truth-engine-addresses.json)
records every selected IP and the top 50 engine addresses:

| Instruction-site group | Whole-process sampled self-cycle share |
| --- | ---: |
| Deleted-header tests and following branches, all three bodies | 16.396% |
| Prefix blocker load, indexing, bit test and exit | 8.311% |
| Suffix blocker load, indexing, bit test and exit | 0.843% |
| Binary overflow pointer load and following spill | 4.512% |
| Binary truth-query region, including early mask/reason setup | 4.403% |
| Tail truth-query regions and loop increments | 3.174% |
| Five repeated word-load sites, a subset of the preceding query groups | 0.136% |
| Packed OR/word-store sites, binary and long paths together | 0.100% |

These are **sampled IP groups, not removable-time estimates**. In particular,
the hottest prefix blocker IP is the register move immediately after the
blocker load (`0x647fe`, 7.228%), and the hottest overall IP is the branch
after the suffix deleted-byte test (`0x64af2`, 10.016%). Skid and execution
dependencies prevent attributing that weight to the register move or branch
alone. LBR uses USER/CALL_STACK/NO_FLAGS/NO_CYCLES, so it supplies no
branch-misprediction or store-forwarding diagnosis. Low self weight at the
packed stores does not disprove effects on subsequent dependent loads.

The source and profile together narrow the failure:

- **Smaller footprint did not remove a consumer.** Watcher-to-blocker-to-truth
  access remains dependent, and a blocker miss still reads the arena header
  and watched literals. The 8x truth-table shrink is not an 8x reduction of
  propagation traffic. Header, blocker and overflow sites remain prominent.
- **The representation adds work throughout the solver.** Word indexing,
  bit testing and read/modify/write replace direct byte access; general
  truth queries still need three-state decoding. The complete engine also
  carries more live values and spills. Both the whole-process instruction
  screen and assembly include these costs.
- **An obvious local repair is insufficient evidence for another run.**
  An ephemeral word snapshot could avoid repeated opposite-bit reloads,
  but would not eliminate first loads, bit indexing or update dependencies.
  The sampled reload sites have no demonstrated large cost. The already
  used preflight repair removed ternary construction and redundant clearing;
  the subsequent combined candidate still failed both gates.
- **The combination was actually priced.** The borrowed engine's reduced
  calls/validation and the packed table's smaller footprint did not jointly
  clear the wall screen. Combining individually plausible changes is a
  hypothesis, not permission to add their presumed savings. This result
  does not establish a useful positive interaction.

Do not retry this source unchanged or start a word-width/encoding/annotation
sweep from it. The next substantial representation or algorithm proposal
must explain which repeated consumer or dependent access it removes, price
its replacement and invalidation work, and distinguish that saving from
merely shrinking a table. This result supplies no measured large repair,
and does not close the performance gap to Kissat.

## Archive and disposition

The experiment used **two new solver invocations: one cost, one diagnostic**.
The [source patch](assets/2026-09-10-packed-truth-engine.patch) includes the
complete combined engine and its regressions. Applying it to `552eeded` in
a temporary Git index reconstructs the exact candidate tree above. Its
SHA-256 is `8d24815b504f44794b86cc84de468d6a8ba665869206d8e73bfa7a0f36b01d17`.
The production SAT implementation is unchanged.

`precompile/f1d9c74/` retains release/perf binaries, compiler/lock/build
identities, preflight logs and assembly, verified source bundle/patch,
canonical records, raw cost/profile outputs, runners and offline address
analysis. Release SHA-256 is
`1228398b5e9dae8b4c63fb2b89a0d74a6b6b04af1b03d7fbc98e6ff12aa17f7f`;
perf SHA-256 is
`946004fe074cccad8c708eecd2d1d4fca7f6dde8319d4de99539be54d3805fd5`.
The source bundle also retains the initial preflight prototype `6dfb2f56`;
that prototype had no solver cost invocation. Its cache is preserved.

The result, source and flamegraph land on main. Owned experimental worktree,
branch, corpus symlinks and disposable bytecode are removed after archival;
the binary/result caches and foreign work remain. No `/tmp` artifacts were
created. Full workspace build/nextest/docs and installed Z3 4.16.0 parity
were not run because the candidate is rejected, with no solving change
promoted. They remain prerequisites for any future production landing.
