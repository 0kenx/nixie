# Elimination resolution: clear marks after a satisfied first parent

The per-conflict throughput audit found a correctness defect in the scratch
state that any first-parent reuse optimization would depend on. The internal
resolution helper can leave marks behind when a satisfied first parent ends
its scan early. A subsequent call can then fabricate a unit or omit a required
resolvent. This repair restores cleanup before further work on that state.
It is not a measured speedup; no new performance cells were run.

## Reproducer and root cause

With the root fact `t = true`, resolve `(p OR a OR t)` against
`(NOT p OR c)`. The first-parent scan marks `a` and its complement before
discovering `t`. It correctly retires the satisfied parent, but jumps past
the assignment of `marked_n`. That variable still has its initial value zero,
so the shared cleanup loop clears nothing.

Now resolve `(q OR b)` against `(NOT q OR a)`. The stale positive mark says
`a` already belongs to the new first parent; the helper drops it and returns
the unjustified unit `b` instead of `(b OR a)`. The assignment
`t=a=q=true, p=b=false` satisfies all four parents while falsifying that unit.
If the second pair uses `NOT a`, its stale negative mark instead labels the
non-tautological pair tautological and omits its required resolvent.

Both direct-helper regression tests fail on the unmodified source and pass
after the repair. This establishes the helper defect and its invalid
consequence, **not an end-to-end public solver wrong-verdict reproducer**.
The normal round filters initially satisfied clauses and eagerly retires
clauses satisfied by new units; those outer protections limit reachability.
The helper nevertheless explicitly handles satisfied parents and must honor
its own cleanup contract on that path.

`git blame` identifies `7e644a7a`, the
[resolvent-marking vector removal](2026-09-01-elim-resmarked-removal.md), as
the change that introduced `marked_n = 0` plus the later capture. The older
separate bookkeeping vector retained partial prefixes. CaDiCaL's reference
`src/elim.cpp::resolve_clauses` explicitly calls `unmark(c)` on the satisfied
first-parent exit as well as after the second-parent scan.

## Repair and independent layer audit

Stop only the first-parent loop when it finds satisfaction. Capture its
actual marked prefix before leaving the marking phase. Make `marked_n` an
immutable, definitely assigned local: an absent first parent assigns zero;
every completed or partially completed first-parent scan assigns its actual
prefix length. All effects still execute after unmarking. No new allocation,
mark array, unsafe code or search policy is introduced.

| layer examined | evidence and boundary |
|---|---|
| literal and assignment encoding | marks use opposite signed bytes for a literal and its complement; the exhaustive test covers both polarities and all three assignment states |
| first-parent exits | missing/deleted parents mark nothing; satisfied prefixes of lengths 0–3 now clear fully; later resolution tests check both stale-sign failure modes |
| second-parent exits | missing/deleted, satisfied, tautological and ordinary exits all occur after the prefix length is captured; the second scan only appends literals and never writes marks |
| other consumers of the shared mark array | backward subsumption uses its own explicit marked-literal list and clears it on early and normal exits; unit assignment and shrinking do not write resolution marks |
| deferred clause effects | retire/shrink runs after cleanup; tests check surviving clauses and any derived unit/resolvent against every original-parent model |
| caller and round lifetime | pair-loop snapshots remain required because shrinking mutates occurrence lists; per-round scratch is rebuilt by `Eliminator::new`; this repair does not reuse it across pairs or rounds |
| scope and theory integration | the existing base-scope, root-level, assumptions and frozen-theory-variable gates remain the entry conditions; workspace regressions and fresh SMT parity qualify the shared path |
| proofs and model reconstruction | the repair changes neither proof emission nor reconstruction; the caller must receive the full valid resolvent before it can emit/add it and eventually retire a pivot |

The audit does not infer global solver correctness from one passing
reproducer. In particular, no public-input reachability or performance
frequency is claimed for this defensive exit.

## Verification

Four focused tests pass, including **19,683** combinations of two parent
clauses and partial root assignments over three non-pivot variables. An
independent truth-table oracle enumerates all sixteen total assignments,
requiring every model of the original parents/root facts to satisfy any
returned consequence, eagerly derived unit and surviving transformed clause.
It also forbids a fabricated empty-clause result and checks that all marks
are zero after every invocation. Separate tests cover absent/deleted parents
and the two-call contamination regression.

The complete qualification passed on the repair atop `66166ed`, using
Rust 1.96.0 / LLVM 22.1.2 and the existing lockfiles:

| check | result |
|---|---|
| `cargo build --all-features` | passed |
| `cargo nextest run --workspace --all-features` | **10,732 passed**, 12 existing skips |
| workspace all-feature doctests | **111 passed**, 29 ignored |
| all-feature, all-target clippy with `-D warnings` | passed |
| `cargo fmt --all -- --check` | passed |
| all-feature documentation with warnings denied | passed |
| release `diff_equiv 100000` | **zero disagreements, zero invalid models**; 66,993 SAT models checked against original CNFs |
| fresh `run_parity.sh`, available Z3 **4.16.0** | **169 agreements, zero disagreements, one inconclusive** out of 170 |

The inconclusive parity case is `array_unique.smt2`: Nixie reports UNSAT,
Z3 reports Unknown. It is not counted as agreement. The reference version
differs from the historical 4.15.4 snapshot and is recorded explicitly.
Full logs, failing-before/passing-after regressions, source hashes and the
fresh parity snapshot accompany the cached binaries under
`precompile/<landing-sha>/benchmark/elimination-mark-cleanup/`.

## Throughput follow-up

The next candidate is to prepare a first parent once across consecutive
tautological resolution pairs. Those pairs have no clause or assignment
effects, so they offer a bounded reuse interval. Any fallback to units,
retirement, strengthening or other effects must end that interval and clear
its marks first. Pair order, resolution accounting and proof behavior must
remain exact. Measure the eligible repeated preparation work before pricing
the implementation; the older resolution profile alone does not establish
a current end-to-end gain. This is an untested candidate, not a speedup claim.
