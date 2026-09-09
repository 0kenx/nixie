# Direct solving after exact relation factorization

The [propagation-work audit](2026-09-09-propagation-work-audit.md) leaves
95.31% of original-circuit propagation outside scheduled inprocessing and
finds no resolution-budget exhaustion. The original dense relation encoding
places all two-sided variables above Nixie's initial occurrence cutoff.
The [checked transformer](2026-09-08-relation-factorization.md) already
provides an exact smaller encoding; it currently requires a separate
transform/write/reparse/solve pipeline. Make that existing algorithm usable
in one explicit input-to-verdict invocation.

## Implementation contract

Add `NIXIE_RELATION_FACTOR=1` to `stats_solve`. This mode shares the explicit
transformer's strict source parser, uses `factor_relations` with its existing
limits and exhaustive certificate checks, then loads its ordered clauses
directly through the same Solver insertion and deferred-BIG protocol as the
DIMACS parser. No fresh variables, new projection policy or changed relation
recognizer. Retain the original input for post-solve SAT model validation;
refuse a purported SAT answer unless every original clause is satisfied by
the returned model. Limit exhaustion retains the original formula; malformed
input and certificate failures are errors before loading a partial result.

Normal example behavior and solver defaults stay unchanged. This mode does
not emit a complete original-CNF UNSAT certificate: callers needing proof
files keep the existing prefix/map pipeline. The existing mathematical
factorization/proof checks and full solver correctness gates remain required.
The new mode's printed structural summary must state whether it factored or
fell back, without adding wall-dependent policy.

Tests compare direct loading with serialized/reparsed factored clauses under
the same seed/configuration, including SAT and UNSAT, binary deferral, root
units, signs, duplicate clauses, no recognized group and exact limit fallback.
Share and retain the strict-parser rejection tests. Test original-model
validation independently, including missing/unassigned values and an invalid
model. No unsafe indexing or recursion is introduced.

## Registration: one full-path operational screen

Build an immutable candidate from main `f490068`, pinned Rust 1.96.0 / LLVM
22.1.2 and the cached lock SHA-256
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`.
Portable release settings, no RUSTFLAGS/native/PGO override. Cache the
binary and record its source/hash before execution.

Allow **one new solver invocation**: original circuit, CPU 15, seed 1,
MAXC=10000000, sweep disabled, printed model and the new mode enabled.
Clear other study variables. GNU time covers original parsing, exact
transformation/certificate construction, loading, solving and original-model
validation in one process. Warm input/binary, anonymous tmpfs stdout/stderr,
300-second emergency cap and no constrained competing userspace thread on
CPU 15. Record every start/completion once; no retry or new controls.

Require the known 700 groups / 44864 clauses / 224064 literals, a complete
SAT model checked independently on original and cached factored CNFs,
<=10% off CPU and equality of the existing deterministic search output with
the retained factored solve where source changes preserve that output. Any
unexpected trajectory difference needs explanation before qualification.
Compare full-path wall descriptively with retained ordinary Nixie 8.81 s
and requested mode-matched Kissat 1.88 s (both original input, seed 1).
A useful operational screen must solve within the cap and below that
retained ordinary Nixie time; it is not a population or causal speedup claim.
This screen uses no factorial or heuristic null, and does not qualify
factorization as an ordinary default. Passing licenses this explicit mode
only after all required source checks. A negative result must identify
where preparation/retention or remaining search consumes its opportunity;
use the existing profiles before registering more runs.

## Result: explicit whole-path mode passes its operational screen

Exactly one new performance invocation ran, on immutable source
`5261d303a98429e9941f43a1c621c2df0bbca2b9`. The portable release
`stats_solve` SHA-256 is
`ff4dedb52cd11bf1caded91646013bbce18d930e753989929c87081547d55f96`.
The registered compiler and lockfile match. Qualification later removed
two redundant model borrows in `7cb6974`; rebuilt release binaries for both
examples are byte-identical to the measured candidate. No retiming followed.

| Original circuit, CPU 15, seed 1 | Whole invocation wall | Conflicts | Propagations |
|---|---:|---:|---:|
| Retained ordinary Nixie `a64b285` | 8.81 s | 186114 | 19391470 |
| Direct relation mode `5261d30` | **3.61 s** | **91833** | **8369710** |
| Retained requested mode-matched Kissat 4.0.4 | 1.88 s | 167929 | 6684415 |

The new timer includes original parsing, exact transformation and certificate
construction/checking, direct loading, search, original-model validation,
printed output and process teardown. Its 3.55 s user + 0.03 s system time
give 0.831% off CPU; zero major faults, 29 involuntary switches and one
voluntary switch were recorded. Peak RSS is **58176 KiB**, versus retained
ordinary Nixie's 37512 KiB. Keeping the original CNF and constructing the
certificate has a real memory cost; direct loading does not remove it.

The structural result is exactly **700 groups, 44864 clauses and 224064
literals**, from 168064 original clauses. Complete stdout is byte-identical
to the retained offline-transform solve, SHA-256
`87eb5896119b2e0d389bd7495929722291351a3889509b1c549dab3c593814c4`.
Independent external checks accept the printed model on both the original
and retained factored CNFs; internal original-model validation also passes.
All printed search counters, including 315010 decisions, match the old solve.

Descriptively, full wall is 59.02% below retained ordinary Nixie and remains
1.92 times retained Kissat. These are different measurement windows, one
input and one seed. They do not establish a general speedup, a default
factorization policy or a factorial interaction with the newer watch and
subsumption implementations. The historical 3.44 s transform/solve pipeline
used another CPU and instrumentation; this study does not establish the
isolated speed benefit of removing its write/reparse boundary. It establishes
that the complete checked route is now usable in one invocation and meets
the registered operational wall threshold.

Per-conflict cost is still a material gap: whole wall amortized over conflicts
is **39.31 microseconds** here versus Kissat's **11.20 microseconds**. These
include preparation and different work per conflict, so they are not isolated
propagation-kernel timings. Fewer conflicts and less propagated work provide
much of this route's practical gain; they do not establish that the core's
per-conflict overhead is solved.

## Usage and validation boundaries

Build with `cargo build --release -p nixie-sat --example stats_solve`, then:

```bash
NIXIE_RELATION_FACTOR=1 NIXIE_SWEEP=0 SEED=1 MAXC=10000000 PRINT_MODEL=1 \
  target/release/examples/stats_solve input.cnf
```

The explicit mode always validates a SAT model against the original CNF,
including when `PRINT_MODEL` is absent. Its stderr summary reports group
and clause counts and `fallback=true` on transformation limit refusal.
Malformed source, invalid option values and transformation/certificate
errors exit with status 2 before printing a verdict. A resource limit loads
the untouched original formula. Parsing still retains the full input before
applying the existing transformation limits; those limits are not a bound
on input-parser memory. The mode adds no variables and requires no model
reconstruction beyond the solver's existing model handling.

The ordinary example route and library defaults remain unchanged. For an
exported proof over the original CNF, use the existing `relation_factor`
prefix/map pipeline: this direct mode does not compose/export a full UNSAT
certificate. The library's exact equivalence and resolution checks remain
in force before any transformed clause reaches the solver.

The new loader tests compare complete solver statistics and models against
serialized/reparsed output for SAT, UNSAT, original fallback, signed units,
duplicate binaries, tautologies and empty clauses. Malformed-input tests
verify that the solver remains empty. A separate model-validation test
rejects missing, undefined and false witnesses; partial assignments are
accepted only when every original clause already contains a true literal.
The shared strict parser is extracted without semantic changes from the
qualified standalone transformer. Both its retained tests and all four
new example tests pass under the ordinary build.

## Source qualification

Final source `7cb6974` passes the full required gate: all-features build;
**10824 workspace tests passed, 12 skipped**; **111 doc tests passed,
29 ignored**; both example test targets passed all six tests with all
features; strict Clippy, formatting and warning-free documentation passed.
The earlier qualification's redundant-borrow lint failure remains recorded,
alongside the final clean run. The two release example binaries are identical
across that cleanup, so the measured binary is the qualified executable.

The required correctness-only comparison used installed **Z3 4.16.0**:
**174 Correct, 0 Wrong, 1 Inconclusive**. `array_unique.smt2` is Nixie
UNSAT / comparator Unknown, explicitly not an agreement. The actual
platform result is retained with the final qualification logs. This is a
soundness gate, not the performance target; all wall comparisons above
remain against Kissat.

Only documentation changed on main during qualification. Its integration
does not alter the qualified source. The implementation, usage and measured
result land together; cached binaries and canonical records survive cleanup
of the temporary worktree, branch, build tree and scratch logs.

## Retained evidence

Canonical record **`8eca4094036dc24b`** lives under
`precompile/5261d30/benchmark/runs/direct-relation-solve/`. Adjacent
`direct-relation-solve/` retains the one-shot runner, thread affinity audit,
start/completion markers, full stdout/stderr and qualification logs. The
build identity and both example binaries are cached at `precompile/5261d30/`.
The retained original Nixie and Kissat records are `ee11cd60c342c2fb` and
`6295845397e7a242`; neither was executed again. The separate propagation
diagnostic earlier in this step is recorded in its own study and is not
an uninstrumented timing control.
