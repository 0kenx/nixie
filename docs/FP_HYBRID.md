# Symbolic floating-point hybrid

The FP hybrid dispatch combines direct reasoning over floating-point value
classes and order with counterexample-guided refinement into exact bit-vector
circuits. It makes genuinely symbolic arithmetic searchable without treating
floating-point atoms as unconstrained Booleans.

## Supported fragment

The first implementation supports Boolean structure (`and`, `or`, `not`,
implication, xor, equality, distinctness, and `ite`), FP variables and literals,
`fp.add`, `fp.sub`, `fp.mul`, `fp.abs`, `fp.neg`, all comparisons, and all seven
classification predicates. All five rounding modes are supported, including
symbolic modes through the parser's existing five-way `ite` expansion. The
rounding-mode sort has exactly five inhabitants in the lowering itself.

Formats have 2–15 exponent bits and 2–64 significand bits. This includes
binary16, binary32, and binary64, and asymmetric custom formats. The boundary
is explicit: concrete validation currently uses `FpValue`'s `u64` fields;
binary128 is declined rather than truncated. Exact real constant expressions
converted to FP are folded with the existing rational rounding procedure.

Symbolic division, square root, remainder, FMA, round-to-integral, min/max,
format conversions, FP/BV conversions, symbolic real arithmetic, arrays,
uninterpreted functions, and quantifiers remain outside this dispatch.
Unsupported assertions are never partially solved: the existing solver path
and its honesty gates retain ownership of the whole goal. Certified/proof
mode likewise keeps the existing path, because FP-to-BV proof translation is
not implemented. Configured timeout/decision limits not exposed by the
embedded SAT API also retain the existing path; conflict limits are passed
through to hybrid search.

## Pipeline

1. **Validate and collect the original DAG.** An iterative postorder walk
   validates every supported node and its operand/result sorts. The internal
   representation records original term identities and normalizes Boolean
   sugar. Unknown operators or invalid formats decline the entire dispatch.
2. **Propagate in FP space.** Each FP expression has a finite domain of nine
   classes: NaN and positive/negative zero, subnormal, normal, and infinity.
   Unconditional classification facts narrow these domains. Nixie's existing
   EUF solver closes asserted datum equalities through FP operations, keeping
   the format and rounding mode in each function symbol. `fp.eq` is excluded
   from datum merges because it identifies opposite zero signs. Arithmetic class
   tables propagate forward and backward; equality intersects domains;
   comparisons exclude NaNs and propagate the ordering of classes. A strict
   cycle in the graph of asserted comparisons and equalities proves a
   contradiction before any SAT circuit is constructed.
3. **Build an abstraction.** Classification, equality, comparison, sign
   operations, and Boolean structure get exact BV encodings. Each arithmetic
   result initially receives fresh FP representation bits constrained by
   its propagated class domain. This is a relaxation of the original goal.
4. **Check a candidate.** SAT assignments are decoded for every expression.
   Each original operation is independently evaluated. Arithmetic uses exact
   `BigRational` operations and the existing exact rational-to-FP rounding
   procedure, not the symbolic circuit's rounder. A result is accepted only
   if every definition and every asserted root is satisfied.
5. **Refine.** Each violated arithmetic definition is replaced with its exact
   circuit in the same SAT instance. Existing clauses and encoding memos
   remain; each arithmetic operation is refined at most once. Thus at most
   `number_of_arithmetic_nodes + 1` SAT checks are needed before the formula
   is exact, assuming those checks finish. Violations of an already-exact
   definition fail closed to `Unknown`.

Class domains are a deliberately coarse first direct domain. They are not
numeric intervals: this implementation does not claim numerical bound
propagation. Exact intervals over representable values, operation-specific
inverse bounds, and stronger relational lemmas can extend this interface.
Such deductions must be sound overapproximations, including NaNs, signed
zeros, directed rounding, and disconnected inverse images.

## Exact encoding invariants

The operation construction follows the specification patterns in Z3's
`src/ast/fpa/fpa2bv_converter.cpp`: `unpack`, `add_core`, `mk_add`, `mk_mul`,
`mk_rounding_decision`, and `round`. CVC5's
`src/theory/fp/theory_fp.cpp` (`wordBlastAndEquateTerm`, lazy word blasting,
and abstraction checking) provides the reference for keeping FP expressions
and introducing exact definitions as needed. These are read-only references;
the implementation and all dependencies remain Rust.

- FP is represented by sign, biased exponent, and stored fraction bits.
  SMT equality identifies all NaN encodings and distinguishes signed zeros;
  `fp.eq` excludes NaNs and identifies signed zeros.
- Addition aligns significands with guard/round/sticky information, adds or
  subtracts magnitudes, normalizes, and rounds once. Subtraction negates the
  second operand before the same procedure.
- Multiplication normalizes operands, computes the full `2p`-bit significand
  product, retains rounding/sticky information, and rounds once.
- The common rounder handles subnormal shifts, ties, carry renormalization,
  and rounding-dependent overflow to infinity or maximum finite magnitude.
- Intermediate exponents include enough signed headroom for format bounds
  **and** normalization distances. Stored exponent width alone is
  insufficient for formats such as `(2, 60)`.
- A narrowed shift count is saturated before resizing; no high shift bits
  are silently discarded. All BV constants and intermediate products are
  arbitrary-width integers.
- Arithmetic special values and zero signs are explicitly selected around
  the finite arithmetic circuit.

## State, results, and soundness

The dispatch owns a separate term manager, BV encoder, and SAT instance for
one immutable assertion snapshot. Internal symbols cannot alias user symbols.
Refinement is monotone within that snapshot. All circuit variables are frozen
against destructive SAT elimination because subsequent refinement clauses
may reference them. SAT model snapshots are explicitly adopted by the BV
decoder before reading any value.

No hybrid state survives a public check; consequently no hybrid clause or
memo can outlive a popped assertion. The outer solver's existing incremental
clauses and memos are left intact. A verified SAT assignment is translated
back into the public model using original term IDs. UNSAT cores use the
active assertion set as a sound, non-minimal core. Proof production requires
a future proof of the lowering in addition to a SAT refutation.

UNSAT from class/order reasoning is justified by necessary conditions of
the asserted facts. UNSAT from any refinement stage is sound because every
exact FP model extends to a model of that stage's abstraction. SAT requires
the independent check of all original definitions, including inactive
branches, and asserted roots. Failure to decode or validate a model never
authorizes SAT.

## Validation and performance claims

Tests evaluate generated arithmetic circuits independently of SAT, exhaust
tiny formats across all rounding modes, exercise binary64 boundary and
deterministically generated inputs, and cover asymmetric formats. Separate
tests exercise domain-only conflicts, actual arithmetic refinement,
unsupported/malformed input, Boolean polarity, and public push/pop/models.

This is a capability implementation, not a measured speedup. It does not
establish that the standing QF_FP corpus is now tractable. Any claim that
lazy refinement or a stronger domain improves search performance must use
the matched-null, multi-seed, deterministic-work protocol in
`docs/BENCHMARKING.md`.
