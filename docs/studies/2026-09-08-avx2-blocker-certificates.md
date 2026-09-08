# AVX2 blocker-certificate generation: rejected cost screen

The scalar window-certificate prototype was rejected: constructing masks and
maintaining its scan cursor cost more than the avoided blocker checks. This
tests a different implementation of mask generation, using AVX2 gathers on
the available Intel Core Ultra 7 265K. It is not a window-width search or a
claim that the prior scalar prototype worked.

## Mechanism and safety contract

Keep its fixed sixteen-watcher window and exact positive-only certificate
semantics. Generate two eight-lane masks by gathering blocker values and
testing each low byte for +1. Read blocker codes through ordinary Rust field
access, without assuming the layout of Watcher. Retain certified positive
runs in original order; every non-certified watcher still executes the
original scalar check, since earlier propagation may have changed it.
Certificates never survive list exit, conflicts or backtracking. Preserve
arena normalization, compaction, conflict tails, observer events and ticks.
Kissat `src/proplit.h` is the reference for the blocker-before-payload rule.

The gather reads four bytes starting at each literal's value byte. Keep the
value vector's logical length unchanged and explicitly initialize at least
three spare bytes after every creation/growth path. No uninitialized or
out-of-allocation read is permitted. Audit both assignment entry points,
resize, clear and backtrack. Signed gather offsets require every code to fit
i32; use the original scalar kernel for larger variable domains. Dispatch
once per propagation call after runtime AVX2 detection, with a scalar fallback
on unsupported architectures. Debug checks and exhaustive mask tests cover
the lane, index, padding and positive-only contracts.

The ordinary scalar kernel remains a test oracle. Compare actual clause
payload and metadata, trail/watch state, models and LRAT transcripts in
paired solves. Exercise certified runs across units, moves, deletion,
compaction, stale zero-to-true/false changes, conflict tails, partial windows
and backtracking. Independently check small models and UNSAT proofs.

## At most four new cells

Pin a clean committed control based on main `c7f3d93` and its direct-descendant
candidate. Build both with the same ordinary release flags/compiler/lockfile;
no global native-CPU or AVX2 build flags. The runtime-dispatched candidate is
the artifact being measured. Archive both binaries and exact build metadata.

Run circuit scalar then candidate, seed 0, MAXC=40000, CPU 10, CaDiCaL preset,
`NIXIE_SWEEP=0`, model output enabled and other study overrides cleared.
Stop unless cycles/conflict falls by at least **5%**, whole-process user
instructions do not increase, and complete stdout is byte-identical.
Only after passing run j3037 candidate then scalar with the same settings.
Final advancement requires geometric-mean cycles/conflict <= **0.95**,
geometric-mean instructions <= **1.00**, neither input's cycle ratio > **1.03**,
and all identity/correctness gates. No inline, width or dispatch tuning after
the first cost cell. Hardware events require one active PMU and >=99.9%
event scheduling coverage; report branches/misses, verdicts, conflicts and
secondary wall time. Record/reuse every cell once, with a 300-second emergency
timeout that cannot justify a repeat.

This is an early rejection screen, not a broad performance claim. Budget
Unknown is an unsolved prefix, not a certified verdict. A passing candidate
still needs full workspace build/nextest/doctests/clippy/fmt/docs and fresh
Z3 parity before production landing. A failed candidate is archived, removed
from the checkout, and recorded here on main. The overall Kissat gap remains
the objective.

## Implementation and pre-cost checks

The control is registration commit **`1036b62`**, binary SHA-256
`447b505b21b4fa6594d8d3710429243108c6c8ef92fd008db1fbd21799658579`.
The final candidate is **`a26c660`**, binary SHA-256
`73e217cbdf60cd44abacd0832c372914f96b72edde1ad980d5ed46966e010de7`.
It contains only this experiment atop the control, through the initial
unmeasured implementation `c7d956b` and a checked-window correction. Both
measured binaries use Rust 1.96.0 / LLVM 22.1.2 and identical lockfile/release
settings, with no RUSTFLAGS or target override.

Before any cost cell, disassembly confirmed that both gathers inline into
the AVX2 propagation wrapper. It also exposed unnecessary per-index address
calculations/spills while extracting blockers. Converting the sixteen-element
slice to a checked array reference made those accesses fixed offsets from
one base. The final disassembly retains two `vpgatherdd` instructions per
full window, with no gather-helper call. The window width, dispatch rule,
certificate semantics and registered metrics were not tuned after measurement.

The unsafe boundaries were checked against the official Rust
[gather intrinsic](https://doc.rust-lang.org/core/arch/x86_64/fn._mm256_i32gather_epi32.html)
and [spare-capacity API](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.spare_capacity_mut).
The implementation initializes three spare bytes while preserving the Vec's
logical length; it never exposes padding as additional literals. Both normal
and explicit-level assignment growth paths reinitialize padding, as do
construction and resize. The private kernel has an explicit unsafe ISA/domain
contract so new callers cannot silently bypass the checked dispatcher.

## Result: instruction reduction, cycle regression in the screen

Exactly **two new cells** ran. Both circuit invocations reached 40,000
conflicts and returned budget Unknown. Complete stdout, including every
printed search counter, is byte-identical; solved-at-cap is **0/1 in both
arms**, and no final SAT/UNSAT certificate is claimed for this prefix.

| metric | scalar | AVX2 | treatment / scalar |
|---|---:|---:|---:|
| user instructions | 12,073,440,631 | 11,667,484,251 | **0.966376** |
| user cycles | 5,661,041,810 | 6,347,023,213 | **1.121176** |
| cycles / conflict | 141,526.05 | 158,675.58 | **1.121176** |
| branches | 2,674,212,713 | 2,602,635,913 | 0.973234 |
| branch misses | 61,642,572 | 66,414,505 | 1.077413 |
| secondary wall time (s) | 1.7233 | 1.4771 | 0.857151 |

The 3.36% instruction reduction is inside the neutrality band. The measured
12.12% increase in cycles/conflict fails the advancement gate, and branch
misses increase 7.74%. The runner therefore stopped before either j3037
cell. These observations reject this prototype; they are not a multi-seed
estimate of AVX2 performance generally.

Wall time moves in the opposite direction from measured cycles. It is
secondary context only and does not override the registered cycle gate.

Vector generation removes some retired instructions, but that saving does
not make the complete certificate loop cheaper in cycles on this host. The
screen includes the gathers, mask handling, dispatch, padding maintenance,
changed code layout and scalar fallback paths; it does not isolate any one
as the cause of the cycle increase. Do not tune this sixteen-entry gather
design on these results or reinterpret its instruction reduction as closing
the throughput gap. A successor needs a different cost mechanism, not another
mask-width sweep.

Both records used one active `cpu_atom` PMU with 100% scheduling coverage.
Canonical IDs are **8263c2fb39751e7f** (scalar) and **149e0d10a0fad080**
(AVX2). Schema, record identity and canonical path checks passed. The raw
outputs/perf records and runner are preserved under each arm's
`precompile/<sha>/benchmark/` directories.

## Correctness coverage and disposition

All **761 all-feature SAT library tests** and **736 ordinary-feature SAT
library tests** passed, as did all-target SAT clippy, formatting and the
committed release build. New tests cover 13,122 scalar/gather mask comparisons
over all 3^8 assignment patterns, both literal polarities and the final value
byte; every vector-growth path, initialized spare bytes and unchanged public
literal bounds; the signed gather domain cutoff; and positive runs across
units, moves, deletion, compaction, stale zero-to-true/false changes, conflicts,
partial windows and backtracking.

Twenty-four truth-table-classified formulas, including guaranteed SAT and
UNSAT cases, run with scalar and dispatched propagation, each with proof
recording off and on. Clause literal order and metadata bits, trail, watches,
binary graph, stats, ticks and models agree. SAT models and UNSAT LRAT proofs
are checked independently, and complete watch-group, region and clause-traffic
observer reports agree when those features are enabled.

The prototype is **archived, not landed**. Its source bundle includes both
implementation commits and is rooted at the registered control:
`precompile/a26c660/benchmark/avx2-blocker-certificates/source.bundle`.
Build/test logs and before/after code-generation excerpts accompany it. No
full-workspace, SMT parity, Miri or sanitizer qualification is claimed for the
rejected code.
Main receives this negative result only; the temporary checkout and branch
are removed. The original per-conflict gap remains open.
