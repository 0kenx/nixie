# Delayed watch moves inside the complete-list propagation engine

## Registration

Continue closing the wall/cycle gap against Kissat from promoted `ade512da`.
Its release binary is byte-identical to the measured `f5e75a7` prototype
(SHA-256 `69c731e4351f91ae1680df81abf527c11afb096065b800e7854f8c8e5d1cd70a`).
The existing noL profile places 55.31% of sampled cycles in watch scans.
Destination appends still keep a vector directory live and can allocate
inside those scans. Sampled instruction locations do not measure removable
stall time.

The earlier delayed-move prototype flushed on every unit yield and paid a
capacity check and length update per queued move. Combine delayed moves with
the promoted complete-list session: reserve scratch space before entering a
list, append through a bounded cursor, and flush once when the list finishes
or conflicts. The local reference is Kissat `src/proplit.h`'s delayed stack
and FIFO flush. Preserve Nixie's eager normalization, true-tail parking,
first undefined replacement, assignments, reasons and scheduling counters.

Keep a reusable buffer of uninitialized move slots with WatchLists. Its
capacity is physical scratch, never logical solver state: clones start empty,
snapshots do not retain entries, and no raw cursor survives a list. Reserve
at least one slot per input watcher. The scan visits each watcher once and
queues at most one move per visit, so appending cannot reallocate or overrun.
Only the initialized prefix may be read during flushing. Report the scratch
capacity in terminal memory diagnostics.

A replacement is undefined when selected, while the currently watched
literal is false; its destination cannot be the active list. Internal
assignment reads neither destination lists nor the scratch records. Flush
all moves in FIFO order before processing the next trail literal or returning
a conflict, preserving destination-list order and the unvisited conflict
tail. Existing LRAT/HBR/observer paths retain their complete fallback.
These arguments apply equally when the SAT engine runs inside CDCL(T).

Inspect portable Rust 1.96.0 / LLVM 22.1.2 perf assembly before measurement,
using frozen lock SHA-256
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`.
Check that destination indexing/growth and scratch capacity checks leave
the scan. Price the extra 12-byte records (16 bytes with observer identity),
flush work, reserve checks, return-value storage and any new register spills.
Do not equate a smaller scan with a full-run improvement or sweep inline
annotations. Default/all-feature SAT tests, doctests, strict SAT Clippy,
formatting and focused strict-provenance Miri precede cost. Extend the exact
scalar oracle with move bursts followed by units and conflicts, repeated
destinations, buffer reuse, clone/snapshot/relocation and Rayon ownership.

At most **three new cost cells**, in order noL, crn, j3037, plus **one noL
cycle/LBR diagnostic**. Reuse controls `248bb59f9b9d9308`,
`625816f9fef3d493`, `ac690061cdf2abbe` from the byte-identical promoted binary;
do not substitute old sweep-OFF or pre-promotion controls. Reuse the existing
requested Kissat 4.0.4 reference cells; no new reference runs or cost repeats.

Use CPU15 Atom, seed 0, CaDiCaL preset, NIXIE_SWEEP=1,
NIXIE_DEFINITIONS=0, MAXC=10000000, PRINT_MODEL=1, cleared study overrides,
portable release, warmed input/binary and anonymous tmpfs output. GNU time
1.10 covers the complete target. Group user cycles/instructions/branches/
misses, with a 300-second cap, >=99.9% PMU coverage, zero major faults,
<=5% off CPU and audited constrained threads. No owned build runs during
cost. Hardware instructions cover the extra memory operations; unchanged
semantic counters alone do not price the new queue. Verify exact complete
stdout and independently check SAT models; unchecked UNSAT remains unknown
in the result store. Save each start/completion and canonical record once.

The diagnostic uses period 10472903, explicit CPU samples, grouped user
cycles/instructions and LBR. Require >=1000 resolved samples, >=99.9% PMU
coverage, zero lost/throttled records and <1% unresolved self weight; no
additional user-mode-IP threshold. Its elapsed time is not a replacement
cost cell. Retain a flamegraph separating scan, buffer and flush work.

Report per-input and aggregate instructions/cycles/wall, completion counts,
memory and the limitations of cached controls. The original study's 3%
per-input wall veto is not reinstated. Apply the repository's productive-step
and enablement rules: a demonstrated component improvement can be useful
with neutral end-to-end results, subject to structural soundness, complete
fallbacks and fresh differential qualification. Clear added cost without
a compensating improvement is a negative finding to archive and diagnose.
Full workspace build/tests/doctests/Clippy/fmt/docs and installed Z3 4.16.0
parity remain required before promoting solver code. This is an execution
change under exact trajectories, not a heuristic or seed-selection study.

## Code-generation preflight

The initial three-pointer move writer did remove destination indexing and
allocation from both scan phases, but introduced writer-owner updates on
moves and a watch-cursor owner store on every kept suffix entry. This is not
free separation: the initial prefix/suffix were 547/530 bytes, with 40-byte
local frames, but the owner traffic remained inside the hot loop.

The bound is needed only for debug assertions; the fixed visit bound proves
release appends safe. Making that member debug-only lets the two live writer
coordinates pass as scalar arguments. This removes writer-owner updates,
but alone produces a 616-byte suffix that still publishes/reloads watch
coordinates. Its LLVM argument is an indirect 24-byte cursor; the raw
coordinate accesses have not all become local SSA state.

Consume the incoming watch cursor into a fresh local cursor before traversing
it. This is a safe fieldwise move, with no new pointer operations or aliasing
assumptions. Generated code now loads the three watch coordinates once at
entry and keeps them in registers: no per-watch cursor-owner traffic remains.
The selected prefix/suffix are 585/555 bytes with 40-byte local frames. The
assignment leaf remains 68 bytes. The 164-byte separate flush owns vector
directory indexing, bounds checks and growth; it is called only for a nonempty
move prefix. Both scan phases remain free of destination indexing/growth and
scratch capacity checks.

Residual costs are explicit: three 32-bit scratch stores per move, one spilled
move-pointer load/store per suffix move, reads and vector append during the
flush, the prepare/empty checks, and a 32-byte internal return using an output
pointer. Two static suffix exits still call memmove, including zero-length
normal completion. Removing those costs was not smuggled into this change.
The assembly repairs were selected before any cost cell; no runtime tuning or
inline-annotation sweep was performed.

The shared main history was rebased externally during preflight: registration
`569af036` is tree-identical to `689c82ee`, and promoted `ade512da` is represented
by `e396985b`. The frozen experimental base and cached controls retain their
original identities; no measurements are relabeled as another source commit.

## Selected-source qualification

After the code-generation repair, default SAT nextest passes 1,023 tests
(one existing skip); all-feature SAT nextest passes 1,056 (one existing skip).
SAT doctests pass two, with one ignored. Strict all-feature/all-target SAT
Clippy and workspace formatting pass. Three strict-provenance Miri checks
pass on the selected source: empty/partial/full scratch prefixes, move
bursts across internal units and conflict, and unit resumption with an
unvisited conflict tail. A mistyped intermediate Miri filter selected zero
tests and is not counted; the full resumption name was then run successfully.

Initial setup failures are retained in the preflight archive: insufficient
filesystem space when creating the first worktree/signing registration, a
test-only attempt to clone Solver (which has no Clone), and an unavailable
corpus symlink. After correcting that environment, the final native suites
above both pass in complete invocations. The selected code remains an
isolated prototype pending cost and full workspace/SMT qualification.

## Three-cell cost screen

Measured prototype `8514638b9ab212b8a15e92733be5a864d4a338b9`, release SHA-256
`c2df55f04abfc105d1842ef0b75e8358a22ab3ca6c473bcf62b1512effe60eff`.
All three complete solves have byte-identical stdout against the retained
control, including decisions, conflicts, propagations and scheduling ticks.
The noL model is independently checked against its original CNF. The two
unchecked UNSAT results remain `unknown` in the canonical store, with their
reported verdicts retained separately.

| Input | Instructions ratio | Cycles ratio | Control wall | Candidate wall | Peak RSS control/candidate KiB |
|---|---:|---:|---:|---:|---:|
| noL | 1.0317 | 0.9429 | 53.99s | 49.30s | 53,456 / 55,012 |
| crn | 1.0296 | 0.9998 | 1.44s | 1.43s | 14,412 / 14,740 |
| j3037 | 1.0475 | 0.8948 | 44.54s | 39.98s | 35,068 / 35,104 |

The paired three-input geomeans are **1.0362 instructions**, **0.9449 cycles**
and **0.9337 wall**. The primary instruction result is inside the repository's
neutrality band. The retained-control wall screen is 6.63% lower and cycles
5.51% lower; these describe this screen, not a demonstrated corpus-wide
speedup. Completion count is 3/3 in each arm. All new cost cells have 100%
PMU coverage, zero major faults, passing constrained-thread audits and under
1% off-CPU time. No cost cell or control was repeated.

Extra instructions are consistent with storing and rereading the move queue.
IPC improves on both long inputs, while crn cycles remain essentially flat.
The controls come from an earlier window; other host load, cache placement
and frequency still limit causal wall/cycle claims. The instruction increase
covers complete-process work, including parsing, search, inprocessing and
flushes. Unchanged semantic ticks are an exact-trajectory check, not evidence
that the added memory traffic is free.

Kissat remains the target. The retained requested-option reference walls are
16.69s (noL), 0.68s (crn), and 18.04s (j3037), leaving candidate ratios of
2.95x, 2.10x and 2.22x respectively. These are earlier-window context; j3037's
reference uses a different PMU group. This narrow panel does not replace the
standing corpus or claim that the overall Kissat gap has closed. Nixie's
screen retains sweep ON with definitions OFF; Kissat retains the user's
listed disabled options. No new reference invocation was added.

## Profile: charge the flush too

The single noL diagnostic is canonical cell `a98e2d2514fb9e98`, with 20,664
cycle samples, 20,647 resolved self samples, 100% sampled-read coverage, zero
lost/throttled records and 0.0823% unresolved self weight. Its full stdout,
after removing the terminal memory line, exactly matches the cost cell.
The elapsed profile run is diagnostic only and is not substituted for cost.

The [flamegraph](assets/2026-09-10-whole-list-delayed-moves.svg) labels prefix,
suffix, assignment and flush by their inspected address ranges. LBR chains
that do not reach `_start` are explicitly labeled truncated. The
[assembly](assets/2026-09-10-whole-list-delayed-moves.asm) and
[audit](assets/2026-09-10-whole-list-delayed-moves-audit.json) retain the
ranges, complete records, quality evidence and hashes.

| Component | Sampled cycle share | Sampled instruction share |
|---|---:|---:|
| Prefix | 9.345% | 8.554% |
| Suffix | 42.930% | 37.937% |
| Flush | 3.170% | 2.926% |
| Assignment leaf | 0.527% | 0.476% |

The combined scan-plus-flush sampled cost is 119.99 billion cycles versus
122.69 billion for the retained direct-append scans: approximately 2.2%
lower. Including the assignment leaf gives approximately 2.0% lower cycles
and 5.1% more sampled instructions. Thus the profile does **not** establish
an above-band component improvement. Moving work into a different symbol
cannot be counted as eliminating it. The prior profile's registered quality
assessment passes; its original copied helper had imposed an extra user-IP
threshold, documented and corrected in that prior study.

The terminal move allocation is only 10,368 bytes on noL. RSS differences
therefore cannot all be attributed to the queue. Prefix/suffix traversal
still accounts for 52.28% of sampled cycles. Extra flush traffic is a real
counterweight to reduced scan pressure; repeated scans and clause/compaction
memory accesses remain the next large costs. Retrying the old per-unit flush
would add boundaries without addressing them. Retrying the uncorrected
indirect-cursor variant would also restore the per-watch owner traffic that
this preflight removed.

The largest sampled scan locations are the suffix branch after reading the
clause garbage flag (8.41% of whole-process cycle weight), the tail-slot store
on a move (5.18%), and the blocker store while compacting a satisfied watch
(4.34%). These are attention markers, not removable-latency estimates: sample
skid and preceding dependent loads matter. The audit retains the top twenty
IPs with instructions. A future attempt to remove liveness or compaction work
must price its maintenance at deletion/rebuild boundaries too; simply adding
another header lookahead or relabeling these stores does not establish a gain.

## Enablement decision

Apply the repository's 2026-08-25 default-enablement rule, with fresh full
workspace and SMT qualification recorded below. The safety argument is the
fixed visit bound, exclusive scratch ownership, initialized-prefix read,
FIFO destination order and flush-before-next-literal/conflict boundary.
The exact-state oracle covers internal assignments, conflict tails,
backtracking, cloning, snapshots, growth, relocation, Rayon ownership,
proofs and complete observer/callback fallbacks. Screening shows no lost
completions or obvious wall regression on the three registered inputs.

This is an enablement decision under that structural rule. The instruction
result is neutral and the profile provides no above-band component claim;
there is no added 3% per-input wall veto. The paired cost records remain
attached to the measured prototype, while the landing applies only this
patch onto current main and receives its own fresh correctness
qualification. No shared history is rewritten and unrelated landed fixes
are preserved.

## Fresh landing qualification

The patch was applied onto main `69dd2291` in the isolated worktree,
preserving the intervening diagnostic fixes. All required commands pass:

| Check | Result |
|---|---|
| `cargo build --all-features` | Pass |
| `cargo nextest run --workspace --all-features` | 10,902 pass, 13 existing skips |
| `cargo test --workspace --all-features --doc` | 111 pass, 29 ignored |
| `cargo clippy --all-features --all-targets -- -D warnings` | Pass |
| `cargo fmt --all -- --check` | Pass |
| `cargo doc --no-deps --all-features` | Pass; workspace rustdoc flags enforce `-D warnings` |
| `./bench/z3_parity/run_parity.sh` | Z3 4.16.0; 174 decisive matches, 0 disagreements, 1 inconclusive |

The sole inconclusive case remains AUFLIA `array_unique.smt2`: Nixie UNSAT,
Z3 Unknown. It is not counted as a match. The [immutable parity record](assets/2026-09-10-whole-list-delayed-moves-parity.json)
retains every verdict and the actual comparator version. Decisive matches
and unresolved count are unchanged from the promoted control's full parity
qualification, with no disagreements or lost completions in this gate.

The final default `stats_solve` binary SHA-256 is
`1cecaf3a8a007d3ac99b66398ba7f44159d24efb9f296ebe56d266f9840eebd3`;
the CLI binary is
`3c265808cc7d3cc2f6bac143262f8d5a10a36076f4ebc704f76b1b509864a871`.
The landing binary differs from measured prototype `8514638`; its runtime
was not remeasured after applying the patch on current main. The recorded
6.63% lower wall is therefore explicitly a prototype screen, not a timing
claim for this new binary. Performance invocations remain exactly three
candidate cost cells and one diagnostic. The qualified default is enabled;
full logs, source and binaries are retained in the precompile cache.
