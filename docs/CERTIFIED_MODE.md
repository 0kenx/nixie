# Certified mode

Certified mode is a fail-closed policy at the public solver exit gate. Search
still uses the normal CDCL(T) implementation, but a candidate verdict is not
observable as `sat` or `unsat` until a smaller checking path accepts it. If a
certificate is missing, unsupported, malformed, or rejected, the public result
is `unknown`; cached models and unsat cores are cleared.

Enable it with `oxiz --certified-mode`, with
`SolverConfig::certified()`, or with the SMT-LIB option
`(set-option :certified-mode true)`. The CLI uses
`Context::require_certified_mode()`, so input cannot downgrade the policy with
`set-option` or `reset`.

## SAT certificates

SAT uses the model itself as the certificate. The checker converts only
concrete solver assignments and evaluates every original active assertion with
an explicit heap stack and a per-term cache. Integer and rational operations
are exact; bit-vector values and operations use arbitrary-precision integers
and preserve the declared width. Thus the common checking cost is linear in
the reachable assertion DAG, apart from the cost of the exact arithmetic
operations themselves.

The evaluator never completes an absent value or guesses an unsupported
operator. An assertion that cannot be evaluated completely makes the result
`unknown`. Current concrete coverage includes ground Boolean formulas, integer
and rational arithmetic, and the core fixed-size bit-vector operations.

## UNSAT certificates

LRAT proves that a particular clause set is unsatisfiable; by itself it does not
prove that an arbitrary SMT theory lemma is valid. The current gate therefore
accepts UNSAT only when the propositional skeleton of the assertions is already
contradictory:

1. A small independent, full-equivalence Tseitin encoder translates the
   original assertion DAG. It does not reuse the main SMT encoder's clauses.
2. A fresh SAT solver, with inprocessing disabled, refutes that canonical CNF
   while an in-memory tracer records the original clauses and text LRAT steps.
3. The pure-Rust LRAT checker checks the transcript against that exact original
   clause prefix.

The Boolean kernel supports constants, variables, `not`, n-ary `and`/`or`,
`xor`, implication, Boolean equality, and Boolean `ite`. Other Boolean terms,
including theory predicates, are independent propositional atoms. This
abstraction can prove a contradiction such as `P and not P`, but a
contradiction that depends on theory semantics makes the abstraction
satisfiable and certification returns `unknown`. Extending certified UNSAT to
those cases requires independently checkable theory-lemma certificates (or a
separately verified reduction such as bit-blasting); treating unverified theory
lemmas as LRAT input clauses would not provide the promised false-UNSAT
protection.

## Diagnostics

`Solver::certification_failure()` and `Context::certification_failure()` expose
why the latest candidate was declined. SMT-LIB `(get-info :reason-unknown)`
reports the same reason after a certification failure.
