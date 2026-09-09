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
