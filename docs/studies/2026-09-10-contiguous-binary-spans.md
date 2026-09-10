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
