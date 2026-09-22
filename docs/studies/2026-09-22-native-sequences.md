# Native sequence reduction: scope and reference audit

## Reference implementations read before the design

* Z3 source revision `b1168b48680a7b35d639f0243cf5b8c8a3ff0277`:
  `src/ast/seq_decl_plugin.cpp` (polymorphic signatures),
  `src/ast/rewriter/seq_rewriter.cpp` (`mk_seq_extract`, `mk_seq_nth`),
  `src/smt/theory_seq.cpp` (fixed-length reasoning, extensionality and length
  coherence), and `src/api/z3_api.h` (out-of-bounds nth contract).
* CVC5 source revision `e8c0387caeceaf631e0d3b114373b1bc7942334b`:
  `src/theory/strings/sequences_rewriter.cpp` (`rewriteSeqNth`,
  `rewriteSubstr`, `rewriteUpdate`) and `array_solver.cpp` (nth/update
  reasoning and explicit handling restrictions).
* CVC5's published [sequence semantics](https://cvc5.github.io/docs/cvc5-1.0.2/theories/sequences.html)
  and [description of the combined sequence procedure](https://cvc5.github.io/2024/02/15/sequences-theory.html).

These are read-only specifications. Nixie remains pure Rust and gains no
reference-solver dependency.

## Audit of the existing paths

| Layer | Finding and implementation consequence |
|---|---|
| Existing string sequence helpers | `nixie-theories/src/string/sequence` represents strings, integer character codes and a separate symbolic helper AST. It does not declare or solve `Seq T`. It remains separate. |
| TLA encoding | `sorts.rs` creates a datatype with offset, length and array fields. `encode.rs` implements literal operations and window-based symbolic Append/Tail/SubSeq. Structural datatype equality includes offset and out-of-window array entries; this is not native sequence equality. |
| Sorts and AST | Added a parameterized native sort and native operator enum. Sort identity distinguishes element sorts, including nested sequences. Checked construction and sort inference validate operator signatures. |
| Shared primitives | Added children, single-node rebuilding, capture-avoiding substitution, structural/alpha equality, structural hashing, congruence operator identity, term statistics and sort substitution traversal. Sequence operators share one TermKind discriminant, so SeqOp identity must be included in hash/congruence keys. |
| Parsing | Both the core parser and Context's separate command sort resolver handle `(Seq T)`. Qualified empty validates its result sort. Arity and operand checks reject invalid applications. |
| Solving | Native assertions are journalled before legacy encoding. The check-local reduction refuses unsupported residual native terms. Only positive conjuncts establish shapes; guards or disjunctions do not establish a bound. |
| Model evaluation | Separate original-formula interpretation verifies reconstructed values. A regression injects a false assignment for `seq.len` and ensures it cannot override semantics. Scalar `distinct` needs explicit evaluation in this interpreter because the legacy public evaluator leaves it unchanged. |
| Printing | Native constructor terms and parameterized sorts print as SMT-LIB. Sequence spines use a heap stack; both printers use it. Public solver model queries are covered. |
| Scope state | Existing assertion and certificate journals own native formulas; reduction state never survives a check. Tests cover Sat → push/Unsat → pop/Sat and Sat → pop → unsupported/Unknown with no stale model. |
| Proofs and ancillary paths | Proof/certified mode and user propagators decline the reduction. No fabricated sequence proof/core is emitted. SAT-only checking is routed through the same honesty gate. Legacy purification and MBQI rebuilding decline unreduced sequences. |

## Why this reduction, and where a dedicated procedure wins

An exact symbolic length-plus-array encoding needs more than a datatype:
nonnegative lengths, element semantics guarded by valid index ranges,
extensional equality restricted to those ranges, and shifted indices for
concatenation/extraction. General equality requires universal coverage;
disequality requires either different lengths or a witness index. Adding
only the observed reads is incomplete, and asserting full-array equality
changes the theory. These obligations cannot be dropped to obtain a convenient
quantifier-free array reduction.

For an explicitly fixed shape, scalar expansion gives a finite, exact
reduction: N fresh elements represent every sequence of length N, sequence
equality is a conjunction, and all operations inspect or splice those
positions. This makes a useful history/queue slice without requiring arrays
or quantifier instantiation. It costs O(N) elements per explicit sequence and
can duplicate work when many overlapping windows are materialized. The 4096
cap is a refusal limit, not a semantic bound. Completeness is relative to the
remaining scalar formula and model evaluator; it says nothing about cases
without an explicit finite shape.

A dedicated procedure, as the references implement, combines word-equation
splitting, length arithmetic, indexed-element congruence and read/write
reasoning, extensionality, and model construction. It can prove the general
append-length property without materializing any sequence and can reason
about symbolic indices. Reimplementing only its length rules would leave
word equations and element congruence unconstrained. This landing does not
claim to implement that procedure or to establish its general completeness.
Nixie still declines unrestricted symbolic lengths, symbolic-index operations,
quantified sequences, cyclic definitions and unsupported element-theory models.

The following checks were run with Nixie and installed **Z3 4.16.0**, using
`bench/native_sequences/*.smt2`. This is a semantic comparison, not a timing
or heuristic experiment; there is no performance improvement claim.

| Obligation (negated property) | Nixie finite-shape reduction | Z3 native sequence procedure |
|---|---|---|
| History append increases length by one; old length explicitly 2 | unsat | unsat |
| Same append property, arbitrary symbolic old length | unknown | unsat |
| Head of tail equals index 1; queue length explicitly 2 | unsat | unsat |
| Empty extracted window differs from native empty | unsat | unsat |
| Two empty datatype windows with offsets 0 and 1 differ | sat | sat |

The last row is intentionally a datatype formula. It demonstrates why the
existing TLA encoding cannot be counted as native extensional equality and
why silently identifying the encodings is unsound. Preserve the frontend and
use explicit guarded adapters; see [interoperability](../NATIVE_SEQUENCES.md).

## Verification record

The focused suite includes sorts/arity errors, empty/unit, symbolic elements,
concat equality/disequality, exact-length variables, symbolic integer length
observations, negative/end/huge indices, clipped updates, nested element sorts,
model output, scope invalidation, proof refusal, SAT-only routing, and a
5,000-deep constructor DAG on a 256 KiB stack. Independent interpreter tests
reject forged native-operation model assignments and disjunctive shape facts.

The opt-in differential test runs 214 cases against installed Z3 4.16.0.
Z3 4.16.0 does **not** accept `seq.update`; those cases expand CVC5's documented
update definition into Z3's native length, extract, concat and ite operations.
This is explicitly a reference-definition translation, not a native Z3
update test. The extraction matrix includes both satisfiable and unsatisfiable
length guesses. Reference errors, timeouts or Unknown never count as matches.

Run the differential test with:

```sh
cargo test -p nixie-solver --all-features --test native_sequences -- --include-ignored
```

Full landing-gate results are recorded below.

Verification used cached dependencies (`CARGO_NET_OFFLINE=true`). The initial
normal all-features build passed. The first full-suite compilation exhausted
the temporary filesystem with debug artifacts; only this worktree's build
artifacts were deleted. The completed gates use
`CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0 CARGO_INCREMENTAL=0`,
which retains assertions and test semantics. Full-suite testing uses four
threads, following the repository's recorded supervision-budget sensitivity.

The development audit also caught enum discriminant drift in the pinned
structural-hash test. New variants now append to their enums, preserving all
existing discriminants; do not prepend new variants and silently change the
search's hash ordering. Two old parser tests used now-supported sequence
syntax as their unknown-symbol sentinel. Their replacements are truly unknown
names plus explicit malformed sequence arities, not weakened error assertions.

Gate results:

* `cargo build --all-features`: passed, including the final source build.
* `cargo clippy --all-features --all-targets -- -D warnings`: passed.
* `cargo fmt --all -- --check`: passed.
* `cargo doc --no-deps --all-features`: passed with the repository's
  `rustdocflags = ["-D", "warnings"]`. Cargo rejects the guide's trailing
  `-- -D warnings` syntax for this command; the checked-in configuration is
  the effective warnings-as-errors gate.
* Separate workspace doctests: **114 passed, 31 ignored**. Nextest does not
  run doctests. The wasm cdylib is not a supported doctest target.
* Native integration suite including opt-in Z3 differential checks:
  **12 passed**, including **214 decisive reference agreements**.
* CLI example in `NATIVE_SEQUENCES.md`: `Sat`, with sequence `[7,8]`, length 2
  and element 0 equal to 7, printed as native SMT-LIB terms.
* Full Z3 parity: **176 Correct, 0 Wrong, 1 Inconclusive, 0 Timeout, 0 Error**
  over 177 cases, with actual **Z3 4.16.0**. The existing
  `AUFLIA/array_unique.smt2` case is Nixie `Unsat` versus Z3 `Unknown`, matching
  the comparator limitation recorded in the preceding heap-separation study.
  It is not counted as an agreement.
* Performance landing gate against pinned `28e82c65`: **PASS**. All nine
  nontrivial cases have identical conflict and decision counts, both geometric
  ratios **1.000**. The three configured external cases also preserve their
  trivial verdicts. There are no lost samples or changed verdicts. Wall ratio
  0.98 is only a secondary load observation, not the primary metric.
  Candidate release binary SHA-256:
  `2951155fb94a15b94125bc175cdfe93b316488368175aa740765594f17ddc428`.

The final `cargo nextest run --workspace --all-features --build-jobs 4
--test-threads 4` run is clean: **12,205 passed, 0 failed, 17 skipped**.
The optional native-sequence differential test among the skips was run
separately and passed, as recorded above.
Raw parity and performance records are retained with the landed binary under
`precompile/<commit>/benchmark/native-sequences/`; generated per-platform
parity snapshots are ignored by this repository's current `.gitignore`.
