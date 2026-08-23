# Logic contract & structural routing (established-candidates Priority 0): first slice landed (2026-08-23)

## Scope of this slice

The doc's Priority 0 names a full layer (registry + capability collector +
`EnginePlan` + incremental laziness). This slice lands the parts whose
absence produced wrong *behavior*, defers the parts that are pure
architecture:

**Landed**
1. **`LogicSpec` registry** (`oxiz-solver/src/solver/logic_contract.rs`):
   ~60 SMT-LIB 2.7 catalog entries as a declarative table (UF, arith
   fragment incl. nonlinear/diff, arrays, BV, FP, strings, datatypes,
   quantifiers; `QF_ANIA` and the AUF-family per entry — semantics never
   decoded from name substrings).
2. **`set-logic` hardening**: unknown names are rejected BEFORE any
   engine state moves (an invented `QF_LINIA` containing "NIA" no longer
   installs the nonlinear backend — acceptance test 5); a second
   `set-logic` is a command error instead of silently reconfiguring live
   engines (test 6).
3. **Capability validation at `check-sat`**: a KNOWN header is validated
   against a structural capability walk of the assertions; a violation is
   a command error (surfaced by `execute_script`), not an `Unknown`.
   Missing/`ALL` headers are never validated (structural routing —
   test 2 pins routing parity on an instance the NL backend refutes).

**Deferred (recorded)**: `EnginePlan` consolidation (engines still route
from the header name via the pre-existing matcher — the registry now
guards *what may enter*, not yet *which engine runs*); permissive
`--lenient-logic` mode; incremental collector rollback across `push`/`pop`
(the validation runs over live assertions each check, which is sound but
re-walks); declaration-signature validation (declared-but-unused symbols).

## The collector's false-positive chain (the study's real content)

Five consecutive misclassifications, each caught by our own corpora —
each a plausible-sounding rule that rejected valid files:

1. **Nonconstant-count nonlinear test**: `(* (- 1) x)` — the parser keeps
   unary minus as `Neg(IntConst)`, so "two nonconstant operands" fired on
   every Dillig-family LIA benchmark.  Fix: a *concrete-coefficient*
   predicate (numeric literal, possibly negated) — the doc's own
   "distinguish concrete-coefficient multiplication".
2. **Apply ≠ UF**: `((as const (Array Int Int)) v)` is an Apply with an
   Array result (array constructor, not UF) — rejected valid QF_ANIA.
   Fix: classify Apply by result-sort family first.
3. **Result-sort Int ≠ arithmetic**: `h: Bool -> Int` under QF_UF (our own
   pr29 regression family) — Int-RESULT applies are UF decoration or
   builtins.  Fix: `uf` only for uninterpreted-result applies; `arith`
   only from operations/comparisons, never from sorts.
4. **Int/Real provenance**: an Int literal in an NRA comparison
   (`(< (+ x x) 1)`, SMT-LIB coerces literals) — provenance enforcement
   rejected valid files for marginal contract value.  Dropped (flags stay
   as diagnostics).
5. **String builtins and lengths**: `str.len` has a dedicated `TermKind`
   (not Apply), so comparison-over-length set arith and rejected the whole
   QF_S suite; `(- 1)` sentinels in `str.to_int` ground facts made `Neg`
   an arith operation.  Fix: enumerated string-builtin kinds; comparisons
   with any string-derived operand are strings capability; `Neg` of a
   literal is a literal.

The meta-lesson (now also visible in the SBVA study): **every classifier
rule must be run against the full in-repo corpus families before it is
believed** — five of five false positives were caught by existing tests,
zero by reasoning.

## Results

* Acceptance tests 1–7 (`tests/logic_contract_acceptance.rs`): all pass.
  (Test 2 measures routing PARITY — an instance the NL backend refutes
  under an explicit header must refute identically headerless — not NLSAT
  coverage, which has honest `unknown`s independent of routing.)
* Full workspace suite 10 082; clippy/fmt/doc; Z3 parity 168/168.
* **Differential blast radius: 0 rejections across the 270-file sample**
  (was 7 false positives before the collector fixes; solved-count
  unchanged).

## Known limitations (honest)

* The capability walk is one pass over live assertions at `check-sat`:
  O(assertions) per check, no incremental caching.  Measured cost is
  negligible on the sample, but a BMC-style trace with thousands of
  checks should be profiled before trusting that.
* Under-detection is the chosen failure direction (a genuinely UF `f:
  Int -> Int` under QF_LIA passes unflagged).  Over-detection rejects
  valid files and was eliminated; under-detection merely declines to
  enforce — documented per rule.
* `EnginePlan` unification remains: `set_logic` still installs engines
  via name matching (now guarded by the registry), and `check_nlsat`
  still consults `logic.contains(...)`.  Those are the next slice's
  targets; the acceptance tests already pin the observable behavior.
