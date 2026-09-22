# Closing the theory audit's completeness gaps

This follows [the audit](2026-09-22-theory-audit.md) and its
[soundness repairs](2026-09-22-theory-audit-fixes.md). It adds decision paths for
the cases those repairs deliberately left unresolved. These are standalone
theory APIs; this is not a claim of general SMT-LIB/CLI parity with Z3.

## Implemented coverage

| Audit finding | New behavior |
| --- | --- |
| F1–F2, combination | A rejected initial arithmetic arrangement triggers scoped exhaustive splitting of each shared pair into equality, less-than, and greater-than. Accepted witnesses expose exact shared values. Only exhaustive refutation yields `Unsat`; budget exhaustion yields `Unknown`. |
| F3, FP conversion | Symbolic cross-format conversion now normalizes, preserves guard/sticky bits, rounds once in all five modes, and handles subnormals, signed zero, infinity, NaN and directed overflow. The circuit supports exponent widths 2–30 and significand widths 2–256, including binary128. |
| F4, set models | Boolean membership constraints, cardinality bounds and negative subset witnesses are solved together with fresh elements. Models can be finite or cofinite, and are independently validated against the input constraints. |
| F5, set adapter | `assert_decoded` accepts a signed semantic constraint and its input literal. Explained conflicts return a sound, possibly nonminimal core. Contradictory polarities of the same opaque atom are recognized directly. |
| F11, array adapter | `register_equality_atom` supplies operand metadata so the Theory interface can assert either polarity of a registered equality. Registrations follow push/pop. |

### FP semantics and model extraction

The conversion follows Z3 `fpa2bv_converter.cpp::mk_to_fp_float` and its rounder.
Arithmetic is entirely bit-level and exact; there is no intermediate native
floating-point conversion. The exponent word is widened before normalization,
rebiasing and rounding. NaN conversion constrains the abstract NaN value,
without inventing a specific sign or payload.

Enabling wide symbolic conversion exposed a separate model extraction problem:
the previous equality-grouping path shifted into `u64` even for binary128.
`FpExactValue` and `get_value_exact` now preserve all bits with `BigUint`.
Model grouping uses the validated snapshot alone and canonicalizes NaNs.
The narrow accessor retains its explicit width limit.

### Arrangements and explanations

The interface split is a complete partition for shared arithmetic terms. Each
branch feeds equality/disequality to EUF and exact order to arithmetic. An
explicit heap stack controls traversal. Every branch scope is removed on
success, refutation, incompleteness or error. Shared witness values are copied
before restoring the component solvers, and are invalidated on mutation.

The search captures the original assertion reasons before adding branch
assumptions. A final refutation therefore cannot expose the synthetic reason
used for a temporary split. Separate tests protect alternative arrangements,
exhaustive refutation, explanations and subsequent incremental checks.

### Sets and independent shared primitives

The small-model construction follows the fresh-element/slack-element approach
in CVC5 `cardinality_extension.cpp::mkModelValueElementsFor`. It keeps all
named elements, enough witnesses for each lower cardinality, and one for each
negative subset. A default membership pattern represents the unnamed infinite
part of an Int/Real universe. Removing excess finite elements preserves upper
bounds and Boolean relations. Pointwise relation clauses preserve both
polarities, and a negative subset requires an existential counterexample.

Explicit cardinality terms require finite integer sizes in accepted models.
The search first forces their sets finite. If that restriction is refuted, it
rechecks the weaker encoding: only refutation of the weaker encoding proves
`Unsat`; unresolved infinite-cardinality semantics remain `Unknown`.
The model validator independently checks original membership expressions,
relations, cardinalities and domain restrictions. Public mutable domain access
is trailed and prevents fabrication of a literal explanation.

Two deeper defects were found while validating this path:

1. The shared SAT totalizer discarded literal polarity at its leaves. This
   broke at-least constraints, which use negated inputs, and could produce
   either wrong answer. It now uses iterative bounded unary addition with
   signed literal leaves, following Z3 `pb2bv_rewriter.cpp::bounded_addition`.
   Repeated occurrences retain their multiplicity. A primitive-level test
   checks all 14,336 combinations of polarity, assignment, threshold and bound
   direction, independently of set validation.
2. SAT `pop()` unconditionally cleared `trivially_unsat`. Empty clauses and
   contradictory units are not always stored in the clause database, so a
   contradiction predating `push()` could disappear. One scope snapshot now
   owns the prior contradiction, trail prefix and clause IDs. Four direct
   tests cover empty clauses, conflicting units, derived contradictions and
   nested scopes, including removal of a contradiction local to a popped
   scope. Clause retraction, learned-clause ownership, binary-edge removal,
   trail rollback and propagation-head rewinding retain their existing roles.
   Z3's distinct user-scope/decision-scope handling was inspected; its
   decision-level clearing cannot be copied to Nixie's unit fast path.

## Explicit remaining boundaries

- Arrangement search has deterministic caps of 64 shared terms and 16,384
  branch steps. Unsupported or incomplete component checks remain `Unknown`.
- FP conversion outside the documented format caps remains `Unknown`.
  This work does not add every other FP arithmetic operator.
- Fresh/cofinite set search supports Int/Real universes. Bit-vector and custom
  element universes need universe-size metadata before that search can safely
  be used. Existing validated finite witnesses remain available.
- Set witness size and encoding-work caps return `Unknown`. Inputs requiring
  an integer cardinality for an infinite set also remain unresolved.
- A raw `TermId` does not encode its AST. Array equality registration and
  decoded set assertions supply that missing information; unrelated opaque
  assertions remain explicitly unresolved.

## Verification

All-features build, Clippy with warnings denied, formatting, and documentation
with rustdoc warnings denied passed. Workspace doctests: 114 passed, 31 ignored.
The dedicated FP oracle and required ignored arrangement canary both passed.

The installed comparator was **Z3 4.16.0 (64 bit)**. The FP oracle checked 2,560
small-format conversion results across all five rounding modes. The standard
release parity suite reported 176 decisive agreements, zero wrong answers,
and one inconclusive comparison out of 177: `array_unique.smt2` is Nixie
`Unsat` versus Z3 `Unknown`, as in the earlier audit repair. It is not counted
as an agreement.

The performance landing gate passed against pinned baseline `28e82c65`.
All nine core cases preserved verdicts and had identical conflict and decision
counts (both geometric-mean ratios **1.000**). The three external cases also
preserved verdicts and were trivial at the selected counters. The auxiliary
wall ratio was 0.97; no heuristic change or speedup claim is made.

The first full nextest run completed 12,340 tests successfully but timed out
four repeated-check scope tests under the concurrent build/parity/performance
load. No assertion failed. A diagnostic check of their ten individual inputs
against the cached audit binary found nine matching decisive verdicts and the
same hard arithmetic input exceeding the short 20-second cap in both versions.
The serial diagnostic on efficiency cores passed two scope tests but still
terminated the 600-rerun convergence pin at 300 seconds. The next full run,
with eight workers on performance cores, passed 12,343 tests and timed out
only that convergence pin. The cached prior audit run already took 250.199
seconds for the same test. Its existing nextest override was therefore widened
from 300 to 600 seconds, matching the bounded arrangement-canary budget.

Before landing, main advanced with the scheduling/model-replay work through
`ade87ad3`. The isolated tree was fast-forwarded and all gates rerun against
the combined source. In that run the convergence test passed in 377.838
seconds, but the three related 180-second scope tests timed out under the
mixed gate load. All four now share the 600-second nextest override; the
solver, test assertions and all repetitions remain unchanged.

The final integrated full suite passed **12,346 tests**, with 18 default skips,
using eight workers on performance cores. The four scope tests all passed;
the convergence pin completed in 300.419 seconds. Final all-features build,
Clippy, formatting, documentation and all 114 doctests also passed.

The measured integrated release binary has SHA-256
`f162301eaf98d9b3d7e3df55ec47b8dc01ac3b2c9a968ae8d37a71c887764e41`.
Raw gate logs, including the timeout diagnostics, and the ignored parity JSON
are retained beside the landed commit's cached binary. No C/C++ solver is
linked or added as a dependency.
