# Native generic finite sequences

Nixie has a distinct, interned `SortKind::Seq(element)` and
`TermKind::Sequence(SeqOp, operands)`. These are native sorted AST nodes, not
strings, named uninterpreted applications, or frontend datatypes. The current
solver implements an exact **finite-shape reduction**, not a general sequence
word-equation decision procedure. Use `(set-logic ALL)` or the Rust solver's
unspecified logic.

```smt2
(set-logic ALL)
(set-option :produce-models true)
(declare-const q (Seq Int))
(assert (= (seq.len q) 2))
(assert (= (seq.nth q 0) 7))
(assert (= (seq.nth q 1) 8))
(check-sat)
(get-value (q (seq.len q) (seq.nth q 0)))
```

Rust callers use `tm.sorts.seq(element)` and
`tm.mk_sequence(SeqOp::Unit, &[element_term])`. The latter returns a `Result`
and checks arity and every operand's sort. Empty is
`tm.mk_sequence(SeqOp::Empty(sequence_sort), &[])`. Sequence types may nest.
`seq.++` accepts one or more homogeneous operands. Empty concatenation needs
an explicit typed `seq.empty` instead.

## Semantics

The convention is CVC5's [sequence theory reference](https://cvc5.github.io/docs/cvc5-1.0.2/theories/sequences.html).
Indices are zero-based. Empty, singleton, concatenation, length and in-bounds
`seq.nth` have their usual finite-sequence meanings. `seq.nth(s,i)` outside
`0 <= i < len(s)` is unspecified, with the same congruence requirement as any
function; Nixie currently declines checks containing such a read rather than
choosing a fabricated default.

`seq.extract(s,i,n)` is empty when `i < 0`, `i >= len(s)`, or `n <= 0`.
Otherwise it takes at most `n` elements starting at `i`. `seq.update(s,i,r)`
preserves the length of `s`, overwrites starting at `i`, clips replacement
past the end, and leaves `s` unchanged when `i` is out of bounds. Replacement
is itself a sequence; replace one element with `seq.unit(e)`.

Equality is extensional: equal lengths and equal elements at every valid
index. Unused array tails, window offsets and construction grouping never
participate. Lengths, indices, and element numerals remain exact integers;
large extraction lengths clip without truncating them to a machine integer.

## Precisely supported fragment

* Quantifier-free Boolean combinations of sequence equalities/disequalities,
  sequence observations, and constraints on ordinary element theories.
* Sequences built from typed empty, unit, and concatenation. Symbolic
  elements are passed to the existing scalar theories, including arithmetic,
  Booleans, wide bit-vectors, strings and datatypes. Constructor-built nested
  sequences also work. Admission is generic in the element sort; a `Sat`
  verdict still requires the scalar solver and concrete evaluator to supply
  verifiable elements. An unavailable scalar model yields `Unknown`.
* A sequence variable may have an acyclic defining equality in the positive
  assertion conjunction, or an asserted equality `seq.len(variable) = N`
  with a nonnegative integer numeral `N <= 4096`. Each such variable is
  represented by exactly `N` fresh symbolic elements. It is not bounded by a
  guessed maximum. Multiple definitions remain asserted and are checked.
  An unbound nested sequence element of an exact-length variable is declined;
  constructor-defined nested elements are supported.
* `nth` requires an in-bounds index that becomes a numeral during reduction.
  `extract` requires numeral start and count. `update` requires a numeral
  start and a supported replacement. Ordinary arithmetic constant folding is
  allowed. Symbolic integers equal to lengths of known sequence expressions
  are supported, but arbitrary arithmetic reasoning to infer a sequence's
  shape is not implemented.
* A deterministic materialization limit of 4096 elements/work items prevents
  unbounded expansion. Exceeding it returns `Unknown`, including some large
  disequalities whose scalar expansion exceeds the limit.

Declined cases include free symbolic sequence lengths, cyclic definitions,
shape information available only under a disjunction, symbolic indices,
out-of-bounds `nth`, sequence-valued `ite`, sequence arguments/results of
uninterpreted functions, sequences inside arrays/sets/bags/datatypes,
quantifiers, other declared logics, and active user propagators. Unsupported
operators and ill-sorted syntax are errors. This is deliberately not a claim
of completeness for quantifier-free sequences, nor for every existing
scalar theory. No `Unknown` is counted as a reference match.

## Reduction, models, scopes and proofs

A check-local iterative DAG walk first collects only unconditional shape
facts. It expands constructor shapes, substitutes definitions, reduces
observations, and lowers equality to element equality. Distinct sequences of
unequal length are immediately unequal; equal-length disequality becomes
ordinary Boolean reasoning over elements. Nested element equalities use an
explicit pair stack. Fresh names are checked against the term interner so a
user cannot alias an internal element variable.

The resulting formula is sent to an isolated ordinary Nixie solver with the
same configuration. No native sequence term may escape into that solver.
The native assertion remains in the outer assertion/certificate journals,
including named assertions. Every check derives fresh reduction state from
the active stack. `push`, `pop`, and `assert` retain the existing journal and
result invalidation rules; no Tseitin memo is cleared or reconstructed.
`check_sat_only` also respects the sequence reduction instead of ignoring
assertions that were withheld from the SAT encoder.

For `Sat`, the solver reconstructs sequence variable values as native empty /
unit / concat terms. An independent interpreter executes the original
let-expanded assertions, using a separate implementation of extraction and
update (exact index comparisons versus the reducer's clipped slices).
Native compound-node model assignments cannot override sequence semantics.
Only a concretely true result for every assertion publishes the model.
After model completion, validation shares an evaluation cache across the
original assertions. The cache borrows that immutable model and one term
manager, and is discarded after validation; public queries use fresh caches.
`Model::eval`, `(get-value)` and `(get-model)` use native sequence terms and
printing. The older generic `nixie_core::model::Value` API has no sequence
value variant and its default factory returns `None`; callers must not
confuse it with the solver's `TermId` model interface.

The reduction does **not** yet export a sequence proof rule. Proof-enabled
and certified checks return `Unknown`; no scalar refutation is presented as
a proof of the original sequence formula. No sequence unsat core is exported.
The ordinary uncertified `Unsat` result relies on the exact shape reduction
and the existing scalar solver. Proof construction/checking and quantifier
instantiation must not silently treat native sequence operators as axioms;
legacy Nelson–Oppen purification declines unreduced sequence operations and
MBQI's rebuilding path reports an unsupported error.

## Interoperability with TLA

`nixie-tla-check` continues to use its existing `@so`, `@sl`, `@sf` datatype
(window offset, length, integer-indexed array). Its literal tuple sequences
and native `Seq T` values are distinct representations, with no implicit cast.
No frontend rewrite is necessary to use native sequences from SMT-LIB or Rust.

An explicit adapter for a known nonnegative length `N` can build a native
sequence by concatenating `seq.unit(select(graph, off + j))` for
`j = 1 .. N`. In the reverse direction, store native element `i` at array
index `i + 1`, choose offset zero, and carry the native length. Only valid
positions are semantic; the array outside the window remains irrelevant.
TLA reads `s[j]` translate to `seq.nth(s, j-1)` only with an in-bounds guard.
TLA's undefined `Head(<<>>)`/`Tail(<<>>)` must keep the frontend's explicit
undefinedness policy; they are not automatically the total SMT operations.

The datatype representation's structural equality compares offsets and entire
arrays. It is not native extensional sequence equality. An exact adapter for
arbitrary symbolic length needs guarded universal element equality (and
nonnegative length), or a dedicated sequence procedure. Do not identify the
two sorts, discard offsets, or compare array tails to emulate native equality.

See [the design comparison and audit](studies/2026-09-22-native-sequences.md)
for reference sources, reproducible history/queue examples and verification.
