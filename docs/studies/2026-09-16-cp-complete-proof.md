# Complete CP proof chain

This change closes the gap from conditional domain/table explanations to a
checked refutation of the original registered CP problem. It supports all five
built-in globals without adding an SMT-LIB theory or trusting callback axioms.

## Soundness argument and boundaries

An original `CpStatement` is an immutable snapshot built only by `CpModel`.
Generated domain/link assertions are independently checked against the original
domain descriptions and typed integer-binding requests. Their exact multiset
must agree; additional, missing, or changed assertions are rejected. The proof
excludes the main solver's CP-generated assertion positions from its original
application inputs, so an erroneous generated assertion cannot be relabeled as
an application assumption. These positions are permanent root registrations;
reset drops them and assertion pop never removes a registered declaration.
Model checking additionally visits every original binding assertion and its
function applications, even if the main encoder's input ledger is incomplete.

Untrusted proof leaves name an index in a caller-retained declaration list.
They cannot install their own domains or constraints. The checker restricts
each original exactly-one domain by the premises and the negated conclusion.
An empty remaining domain establishes the implication. Otherwise it enumerates
every assignment to the distinct variables of one original constraint; if none
satisfies that constraint, the implication follows. Foreign literals are
forgotten (a relaxation), including a foreign negated conclusion; this can lose
proof coverage but cannot make an invalid implication valid. Constraints from
separate registrations are never conflated.

The exact predicates are independent of the producer's partial-domain methods:
pairwise comparisons for alldifferent, concrete relation membership for table,
word acceptance for regular, one complete traversal for circuit, and direct
resource sums at task starts for cumulative. The latter avoids reusing the
mandatory-part event sweep. Nonnegative demands mean resource usage can increase
only at starts; half-open interval membership handles touching endpoints and
zero durations exactly. All arithmetic uses BigInt, including out-of-range
circuit successors (checked conversion rejects them).

Each accepted implication contributes `not p1 or ... or not pn or conclusion`.
The existing independent Boolean encoder reconstructs the full polarity
Tseitin CNF from original assertions plus these verified leaves. It also
includes the original domain/link assertions. Every additional SMT leaf must
pass the existing EUF or exact linear-arithmetic verifier. A fresh SAT solver
produces LRAT. Its registered input clauses must exactly equal the canonical
list; the independent LRAT checker must derive false. A raw search verdict,
client-provided CNF, or a standalone valid LRAT for another formula cannot
replace any of these steps.

The exported envelope includes CP leaves, SMT leaves, and LRAT text. The
original problem is independently supplied to checking, like the original CNF
for LRAT. Term IDs refer to the same retained TermManager. This is not an
Alethe/LFSC/SMT-LIB serialization of CP declarations. Trusted code comprises the
original declaration constructors, finite-semantic checker, canonical Boolean
translation, admitted SMT leaf verifiers, and LRAT checker; these Rust kernels
are tested, not formally verified in a proof assistant.

The existing specialized table/domain witnesses remain independently checked
at the callback adapter. The complete proof uses finite semantics for every
leaf, so it does not depend on unimplemented specialized witnesses for the
other four globals. Enumeration is bounded and can be exponential. Production
uses ten million semantic work steps and 100,000 SAT conflicts. Failure or
unsupported mixed-theory reasoning returns Unknown. Arbitrary user callbacks
remain uncertifiable, even alongside built-in CP registrations.

## Layers inspected

- Construction and immutable authority: retained declarations include exact
  values, indicator meanings, aliases, globals, and binding assertions.
- Partial filtering versus exact semantics: the checker does not call any
  producer feasibility routine; generated concrete oracles check both layers.
- Signed reasons and conclusions: polarity restrictions use exactly-one
  semantics; foreign literals only weaken the checked antecedent problem.
- Callback queues and direct final conflicts: record explanation terms on both
  paths, including conflicts returned directly by final_check.
- Search and assertion scopes: persisted records are conditional lemmas of
  permanent declarations, rechecked on export; a proof belongs to one active
  assertion stack and is invalidated on every stack/settings mutation.
- Model exits: callback replay remains required, followed by independent exact
  CP model validation and original assertion validation in checked modes.
- SAT encoding and proof inputs: reconstruct from original terms independently
  of the main encoder and compare the complete original LRAT clause prefix.
- Proof import: versioned parser rejects malformed records; imports are
  untrusted until checked against the separately retained original problem.
- Arbitrary callbacks: explicit accounting prevents a built-in registration
  from granting proof authority to other callbacks.
- Reference code consulted read-only: Z3's
  `src/smt/theory_user_propagator.cpp::propagate_consequence`, CVC5's
  `src/proof/proof_rule_checker.cpp`, CaDiCaL's `src/lrattracer.cpp`, and the
  existing Nixie Boolean/LRAT certification gate. No external dependency added.

## Verification

Final-source focused integration passed: all 30 tests across CP complete proofs, domains,
tables, globals, and the generated oracle. The generated campaign checked
6,100 public solver verdicts in certified mode; every UNSAT artifact was checked
again against retained originals. It covered 244 cases, 6,704 complete
assignments, 37,810 callback states, and 171,301 emitted explanations/conflicts.
The finite-semantic checker accepted 102,220 of 122,000 adversarial candidate
lemmas; all accepted implications held under the independent concrete oracle.
These are bounded executable tests, not a formal verification of Rust code.

An additional review found that trusting the generated domain/link assertion
buffer would unnecessarily include that producer in the proof kernel. The
validation and input separation above close this boundary. Focused regressions
mutate the generated axioms (extra false, omitted domain, conjunction replacing
disjunction, negated binding, and ill-typed binding), and corrupt the main
encoder's CP assertion ledger. Neither route may certify a false UNSAT.

The initial leaf-log-only reconstruction returned Unknown on the mixed
CP/integer-binding regression: the main search had not recorded enough SMT
leaves for an independent refutation. Reconstruction now uses the existing
independent SMT model-blocking checker plus exact CP model blockers, preserving
every admitted leaf in the exported envelope. The regression passes with a
checked complete proof. A separate test reconstructs a refutation with no main
search leaves and rejects a forged conflict for a satisfiable CP problem.

The pre-input-validation revision passed build, clippy, formatting, documentation,
and 114 doctests (29 ignored). Its full-suite run was deliberately interrupted
during compilation after the input-boundary review; it supplies no full-suite
result. Final-source repository verification is in progress and will be recorded
before landing.
