# Contiguous binary spans in the complete propagation engine

## Registration

The packed truth experiment failed its instruction and wall screens. Keep
the production signed-byte truth table. The next candidate removes a
storage channel from each binary scan: replace fixed CSR plus per-literal
overflow vectors with one contiguous span per literal in an owned edge pool.
When an append exhausts a span, allocate a larger segment at the pool end,
copy its live edges once, append, and retire the old segment. Ordinary
propagation reads one start/length and scans one slice, binary-before-long.

Combine this with the archived complete borrowed-reason engine `d8e7805`.
Its earlier instruction reduction did not qualify for production wall;
this is a changed implementation, not an unchanged-engine retiming. Previous
compact/unified directories retained two binary storage channels. The older
inline-binary watcher experiment interleaved binaries with long clauses.
Neither is this design: no binary tags or interleaving, and no per-edge
primary/overflow choice. Local Kissat `proplit.h` establishes binary value,
reason and conflict semantics; Nixie's existing ordered BIG is the exact
sequence oracle. No heuristic, tick, clause, reason or search-order change.

Keep exact-size two-pass construction for large binary inputs. Growth,
individual retirement, bulk compaction, graph reset/rebuild, scope rollback
and cloning must preserve every literal's sequence. A relocated segment may
be physically out of literal order, so compaction must not overwrite an
unread source span. Retain count/extent overflow and per-span fill checks.
Preserve the existing distinction between removing one matching built edge
and retaining all nonmatching overflow edges, including duplicate/sentinel
cases; cold origin metadata may remain without a second hot storage channel.
Use checked slices and owned Vec storage; add no raw-pointer adjacency
ownership wrapper. The complete engine's existing small unsafe trail/arena
borrows remain confined to their established contracts.

Price the entire representation: segment copying, pool slack/retired space,
growth, larger transient compaction memory, directory metadata and changed
consumers outside propagation. Do not silently preserve a second overflow
table, count a footprint reduction as removed work, or add historical
percentages. Use the existing memory diagnostic and full-process peak RSS;
retain generated-code and allocation evidence for every negative result.

Preflight: mixed-operation differential tests against independent Vec lists,
relocation followed by deletion/compaction, growth across empty and populated
domains, duplicates, builder overflow/overfill, reset/rebuild and deep clone.
Reuse full-engine/scalar exact-state, original-CNF model and independent LRAT
tests. Run default/all-feature SAT suites, doctests, strict SAT Clippy and
workspace formatting, focused strict-provenance Miri for the new span
operations and inherited fixed queue, and native Rayon owner movement.

Inspect portable perf assembly before cost: one binary slice loop, no
overflow-directory lookup or second binary loop, no span relocation inside
propagation, and unchanged signed-byte truth tests. Record code/stack sizes;
the engine must not exceed the byte engine's 3,098 bytes or 216 local stack
bytes. Permit one source-directed preflight repair, then stop if that fails.
No measured repair, capacity/growth-factor sweep or additional encoding.

At most THREE new solver invocations: candidate j3037 cost; one j3037 LBR
diagnostic after a completed output-identical cost, win or fail; candidate
crn only if j3037 instructions and usable wall are both <=0.95 qualified
production. Confirmation requires <=1.03 instructions/wall on crn and
<=0.95 two-input wall geomean. Require j3037 peak RSS <=1.10 the retained
production peak. These are small rejection screens, not a suite estimate.
No new control/reference, existing-cell repeat or diagnostic-as-cost reuse.

Reuse production fd01d0b j3037 record `0ec1f4bfcfe8f5f9`, crn
`0840cab28aa276cb`, and requested-mode Kissat 4.0.4 context
`45a3c8f2e3057841`. CPU 15 Atom, seed 0, MAXC=10000000, PRINT_MODEL=1,
NIXIE_SWEEP=0, NIXIE_DEFINITIONS=0; clear unrelated overrides. Retain Rust
1.96.0 / LLVM 22.1.2 and Cargo.lock SHA-256
3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439,
portable release/perf, no PGO/native flags. Whole-process user instructions
are primary, wall/cycles secondary; exact stdout, >=99.9% PMU coverage,
zero major faults, <=5% off CPU and unchanged constrained sleeper runtime.
Warm binary/input, anonymous tmpfs output, GNU time 1.10, emergency cap
300 s and no own compilation during cost. Shared host/cache/frequency and
the older control remain attribution limits even after these checks pass.

LBR: period 10472903, 128 pages, grouped user atom cycles/instructions,
sample CPU/running-time reads, zero loss/throttle, >=1,000 samples and
<=0.1% unresolved self. Save source/binary/input identities and every raw,
canonical and diagnostic record once in the precompile result store. An
unchecked UNSAT remains unknown/unverified; check SAT models against the
original CNF. Before any production promotion, complete all workspace
build/nextest/doctest/Clippy/fmt/docs and installed Z3 4.16.0 parity gates.
Otherwise archive source and cost diagnosis on main, then remove owned
worktree/branch/disposable artifacts while retaining the caches.

## Implementation and preflight

Candidate `710011283b14c1a8c613ac70161b5fb00a8964b2` implements a 16-byte
literal directory row (`start`, `len`, `capacity`, `built`) and one Vec edge
pool. The previous directories totalled 32 bytes per literal. `built` is
cold origin metadata, retaining the old duplicate-ID removal semantics;
propagation reads only start/length. There is no second edge channel.
Exact-size count/layout/fill construction remains. Appends double exhausted
span capacity (minimum four), copying live edges to the pool end. The pool
uses initialized entries and checked slices throughout; no adjacency unsafe
block, custom allocator or unsafe Send/Sync implementation is added.

Individual removal compacts only its span. Bulk deletion writes a separate
destination pool because physical span order can differ from literal order;
it also reclaims abandoned segments. Growth never reclaims other spans, so
the scalar HBR path's saved indices remain valid across another trigger's
append and pool reallocation. The complete engine holds an immutable graph
borrow for the whole fixpoint, excluding graph mutation altogether. General
graph consumers, including SCC analysis, read the same single sequence.

The independent Vec oracle checks reverse-key relocation, individual and
bulk deletion, bounds/disjointness, empty/populated growth, deep clone,
reset/rebuild, and preservation of saved indices after other-trigger growth.
A separate duplicate/sentinel regression verifies both old origin-removal
rules after physical merging and compaction. Existing overflow/overfill tests
still reject count/extent failure before modifying neighboring data. The
inherited complete-engine tests preserve scalar state, reasons, budgets,
conflict tails, original-CNF models, independent LRAT checks and native Rayon
owner movement. Scope tests run in the SAT suites.

Preflight passes **1,050 all-feature SAT tests**, **1,023 default SAT tests**
(one existing skip each), **two doctests** (one ignored), strict SAT
all-feature/all-target Clippy and workspace formatting. Three existing test
collections become `to_vec()` because BIG now returns a slice; both affected
oracle tests are rerun after that lint adaptation. Strict-provenance Miri,
seed 42 on nightly 2026-06-11, passes **three new span tests** and **three
fixed-queue tests**. Initial compile diagnostics were a module visibility
adjustment and an all-feature test's ambiguous `sum()` type; both were fixed
before successful qualification. No performance cell ran during bring-up.

The portable perf engine is **2,769 bytes** with **184 local stack bytes**,
versus the archived byte engine's **3,098/216**. Both additionally save six
registers. At `0x638a2/0x638a5` it reads one directory row's start/length;
`0x638f0..0x6395d` is its only binary loop. `0x638fe` directly compares a
signed value byte, and the reason load at `0x63905` follows the satisfied
exit. No overflow-directory lookup or second binary loop remains. Ordinary
span growth cannot occur in this immutable graph borrow. The initial code
passes the assembly gate: **no preflight repair was used**.

## Cost result: instruction reduction, wall below the gate

The one j3037 cost invocation produces **`fe075d2cf545b689`**. Full stdout
is byte-identical to qualified production, including **330,565 conflicts**,
**323,390,316 propagations** and **695,639,361 ticks**. Output SHA-256 is
`a904b7f02cd4dc6ac5abd11a0754072e9f32af0ab18409dc293edf1242c1cb9b`.
The reported UNSAT remains **unknown/unverified** in the canonical store;
this invocation did not independently check an original-input proof.

| Arm | Whole-process user instructions | User cycles | Wall | Peak RSS |
| --- | ---: | ---: | ---: | ---: |
| Qualified production fd01d0b, reused | 254,596,496,994 | 164,287,697,694 | 36.13 s | 34,236 KiB |
| Contiguous binary engine 7100112 | 195,675,300,186 | 159,868,361,922 | 35.28 s | 35,000 KiB |
| Candidate / production | **0.76857** | **0.97310** | **0.97647** | **1.02232** |
| Requested-mode Kissat 4.0.4, reused context | 121,059,163,625 | 79,144,759,362 | 18.04 s | not compared here |

Instructions fall **23.14%**, but observed wall improves only **2.35%**,
below the registered 5% advancement gate. Cycles fall 2.69%; peak RSS rises
2.23%, within its 10% limit. **No crn candidate cell runs, and no production
promotion follows.** This is not a measured regression or an established
population-neutral result: the single screen simply fails the wall bar.
Requested-mode Kissat has a different trajectory (286,784 conflicts and
218,808,022 propagations); candidate/Kissat wall is still **1.956x** on this
input. No new Kissat run or suite geomean is claimed.

The cost passes its registered quality checks: all four PMU events have
100% coverage, major faults are zero, off CPU is **0.794%**, user/system time
is 34.93/0.07 s, with 612 involuntary and 12 voluntary switches. Constrained
sleepers retain identity and runtime. All owned builds/tests had ended.
Before execution, host load was 46.39/28.71/26.27 on the 20-core machine;
the one-second CPU15 observation had 36.4% nonidle time and substantial
I/O wait. Passing the target's off-CPU test does not remove unpinned foreign
load, cache or frequency effects. The older control and this small wall
difference do not isolate a source-only speedup.

Against the archived byte-valued complete engine's instruction count, this
candidate removes another **8,179,419,931 instructions (4.01%)**, or 25.29
amortized whole-process instructions per propagated literal. That comparison
is instruction context only: the old byte engine's j3037 wall failed quality.
The present 23.14% production reduction belongs to the **combined** engine,
not to the new adjacency representation alone.

## Required profile and remaining cost

The one diagnostic produces **`acf2c30643da66db`** and the
[interactive flamegraph](assets/2026-09-10-contiguous-binary-spans.svg).
All **14,449 samples** are on CPU 15, with 100% read coverage, no lost or
throttled records, and **0.02768% unresolved self weight**. Its full output
matches cost after removing exactly one terminal memory-statistics line.
Diagnostic elapsed time and sampled-prefix counters are not another cost
observation and cannot substitute for the 35.28-second cost result.

The complete engine receives **71.19% of sampled self cycles**; search,
shrinking/minimization, subsumption and backtracking receive 4.58%, 3.41%,
2.98% and 2.31%. The scalar watch fallback receives 1.03%. The
[offline address report](assets/2026-09-10-contiguous-binary-spans-addresses.json)
reconciles sample counts and grouped counter-read deltas with the raw audit.

| Instruction-site group | Whole-process sampled self-cycle share |
| --- | ---: |
| Single binary directory and extent-check region | 4.692% |
| Binary edge/value reads and exits | 6.679% |
| Prefix blocker read/value test/exit | 4.955% |
| Suffix blocker read/value test/exit | 0.547% |
| Deleted-header tests and following branches | 8.291% |
| Destination length/capacity/growth-branch regions, including intervening reloads | 4.914% |
| Destination edge stores and length updates | 4.582% |
| Tail literal/value loop regions | 5.841% |

The hottest IP is the branch following a prefix deleted-header test
(`0x63a92`, 4.139%). The single binary length load (`0x638a5`) receives
4.063%, and the suffix destination capacity check (`0x63d60`) 3.336%.
These are sampled IP weights, subject to skid and dependencies, **not
exclusive causes or removable-time estimates**. LBR carries
USER/CALL_STACK/NO_FLAGS/NO_CYCLES; this capture cannot diagnose individual
branch mispredictions or load sources. The cost counted 2,032,301,753 branch
misses, but the reused production control did not record a comparable
branch-miss counter; there is no measured before/after miss reduction.

The memory diagnostic reports unchanged live arena, reference, watch and
binary-edge bytes and 27 arena compactions. Binary edge allocation capacity
rises from **573,776 to 851,296 bytes**, with **511,456 live bytes**: another
277,520 allocated bytes and a 48.37% capacity increase. This prices retired
segments and spare room; it is not the whole BIG footprint. Logical
directory size halves from 32 to 16 bytes per literal, while the diagnostic
does not report allocated directory capacity. Whole-process peak RSS, above,
is the independent memory gate.

All memset sites together receive 1.606% self weight, and memmove 0.270%.
Most memset weight is under deletion/restart handling; only 0.021% is
attributed through the graph/watch rebuild caller. That rebuild receives
0.208% self weight; binary edge removal receives 0.014%. Inlining and caller
truncation limit attribution, and these routines perform other work too.
Do not label all zeroing/copying as new span-maintenance cost. The profile
does not identify a dominant introduced rebuild/copy cost that explains
away the failed wall gate or licenses another capacity-tuning experiment.

## Disposition and algorithm implications

This combination removes the intended overflow consumer and reduces both
the code and live stack, but most measured cost remains in ordinary
propagation. A single binary span still requires directory-to-edge-to-value
access and value-dependent exits. Long-watch blocker/header/literal checks,
stable compaction and destination appends are unchanged. Removing setup and
bookkeeping instructions did not proportionally shorten this execution.

The larger pool is a concrete cost to improve in a different design, but
reverting to separate overflow storage would restore the eliminated lookup
and loop. Frequent repacking would add copying and is forbidden inside the
scalar path's saved-index lifetime. A growth-factor or row-width sweep would
not remove another edge/value consumer. The recorded
[compact adjacency](2026-09-10-compact-adjacency.md) and
[unified directory](2026-09-10-propagation-directory.md) results already
price related metadata-only trades. Do not add their percentages to this
result or retry this candidate unchanged.

The profile also does not justify a generic cache-locality explanation.
The older [throughput campaign](2026-09-07-throughput-campaign.md) found
slow dependent accesses even on L1 hits on other anchors. Those historical
measurements are not current j3037 load-source evidence, but they rule out
assuming that any hot arena IP is an LLC miss fixed by reordering. The next
substantial proposal needs evidence that it removes a repeated value/branch
consumer or propagation obligation, with replacement and invalidation costs
included. Smaller metadata or fewer instructions alone remain insufficient
for the user's Kissat wall target.

Exactly **two performance invocations** were used: one cost and one profile.
No assembly repair, measured repair, held-out cell, reference rerun or broad panel
followed. Production remains unchanged. The
[source patch](assets/2026-09-10-contiguous-binary-spans.patch) reconstructs
tree `8e8f5e774aaff324039789a6c287506c732c673f` from reachable registration
`e44cf486f3bc5eb57ebebdecb72bb37dc8dced9a`, verified using a temporary Git
index. Patch SHA-256 is
`7cd9eeebb6fdb8c6d5b4ab59d7d5928a3df7126bafdbc4c21ff382fc59bbbaf6`.

`precompile/7100112/` retains the source bundle/patch, release/perf binaries,
lock/compiler identities, preflight and Miri logs, assembly, canonical/raw
results, runners and offline address analysis. Release SHA-256 is
`c8451d8015a80b6e539cb773443beb4a7ed6e9f0bdcb6a9395148709fc369866`;
perf SHA-256 is
`ea7701b739f7031005135996277e902050d070384809e719f05d841a4d8f9abb`.
The result and archive land on main; the owned worktree, branch, corpus
symlinks and disposable bytecode are then removed. No `/tmp` artifact was
created. Full workspace build/nextest/docs and fresh installed-Z3 parity
were not run because no solver implementation is being promoted.
