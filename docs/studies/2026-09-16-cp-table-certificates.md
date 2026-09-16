# Independently checkable table explanations

This slice adds row-cover certificates for built-in `table` reductions and
conflicts. It does not change the filtering algorithm or enable certified
UNSAT. The remaining proof-chain boundary is explicit in [CP.md](../CP.md).

## Statement, witness, and trust boundary

`CpModel::table` captures an immutable `TableStatement`: the original column
variables (including aliases), allowed rows, original finite domains, and exact
positive/negative indicator terms. Statements are shared by reference rather
than recopied into every witness, and immutable original domains are shared
across table statements rather than copied per table. Later model additions do
not mutate them.
`CpModel::table_statements` lets a consumer independently retain these originals.

Each emitted witness stores one obstruction per table row. Queuing many
reductions therefore adds storage proportional to the number of rows per
lemma, in addition to the existing antecedent lists. This slice makes no CP
throughput claim; the ordinary performance gate exercises general solver cost,
not the cost of checking large CP tables.

A `TableCertificate` supplies exactly one obstruction for every original row.
The conclusion is either false or a negative indicator for a table variable.
The four obstruction rules are:

1. A row value is absent from the original domain.
2. Two columns alias the same variable but have different row values.
3. An indexed premise excludes the row value or fixes that variable to another
   value, using the finite-domain exactly-one semantics.
4. Negating a value-exclusion conclusion fixes a variable to a value different
   from this row's value.

The proof is a finite disjunction argument: suppose the premises and the
negation of the conclusion hold. Table membership requires some original row.
The witness independently blocks every row, a contradiction. Thus the premises
imply the conclusion, **relative to the original CP domains and table**. An
empty relation needs an empty cover; an empty-arity relation containing the
empty tuple cannot be refuted by such a cover. Duplicate rows each need their
own witness slot. Aliases and wide integers are checked exactly.

The checker in `nixie-theories/src/cp/table_proof.rs` reads no callback state and
calls no feasibility routine. Witness construction is separate, in
`table_explanation.rs`; it runs the checker before emitting a step. A missing
or invalid generated witness yields `Unknown`, never a table conflict. All
untrusted witness indexes use checked access; the checker uses bounded loops,
not recursive term/row walks. Original statements are immutable and can only
be obtained through validated CP construction.

The solver also authenticates the certificate's statement identity against
those retained by `register_cp` and checks the exact implication. A callback
cannot substitute an empty relation to refute a satisfiable registered table.
The direct final-conflict path checks queued certificates before accepting its
conflict; model replay checks them independently as well. Current truth of all
premises remains a separate requirement: a logically valid conditional lemma
cannot justify propagation after its premise was popped or contradicted.
Registration installs statement identities only after callback registration
succeeds, and solver reset drops them with the callbacks.

These witnesses are library data attached to `Consequence`, observable through
`UserPropagatorManager::get_consequences`. They are not a portable SAT proof
export. Domain-only lemmas, non-table globals, and arbitrary uncertified client
axioms retain the earlier trust boundary. The existing certified/proof-mode
honesty gate remains unchanged.

## Reference inspection

Z3's `src/smt/theory_user_propagator.cpp::propagate_consequence` translates fixed
antecedents into a clause or external conflict justification. It does not
provide an independent verifier of arbitrary client semantics. CVC5's
`src/proof/proof_rule_checker.cpp` separates rule checking from proof production
and rejects malformed rule arguments. These local read-only references informed
the adapter/checker boundary; neither solver is linked. The table rule itself
is the direct disjunctive semantics of the existing allowed-tuple constraint,
not a new SMT-LIB theory or theory-combination axiom.

## Tests and evidence

- A standalone adversarial test enumerates 842,688 witness/implication
  combinations, including invalid indexes, premise polarities, foreign terms,
  and unsupported conclusions. It accepts 528; every accepted implication is
  independently checked against the concrete satisfying assignments. No CP
  filtering routine supplies the expected answer or the candidate witnesses.
- Targeted mutations reject omitted premises, changed conclusions, missing row
  coverage, incorrect aliases, and out-of-range indexes. Empty/inhabited
  zero-arity tables and 131-bit values exercise boundary semantics.
- Callback tests retain the original statement across later domain additions
  and nested rollback, and require a certificate on a direct final conflict.
- Solver tests inject mutated certificates and valid certificates for forged
  tables, both during assignment and direct final conflict. They require
  `Unknown` with no model/proof. A valid certificate with a false current premise
  is also rejected. A separate model-gate unit test bypasses search entirely.
- The existing generated oracle checks attached certificates against retained
  originals. For pure-table cases, an implication that is not justified by
  domains alone must have a table certificate. Its exhaustive assignment oracle
  still checks every emitted implication independently of the certificate.
  The run checked 21,880 attached certificates among 171,301 consequences and
  conflicts across 244 instances and 37,810 callback states; these include
  repeated emissions, not 21,880 distinct lemmas. All 6,100 public solver
  verdict/model checks and 6,704 complete assignments still agree with the oracle.

The enumeration is bounded test evidence about the implementation of the
checker. The disjunction argument above explains the rule; neither is a
machine-checked proof of the Rust implementation or an end-to-end CP UNSAT
certificate.

## Landing verification

Verified on the implementation in this commit, based on `ed206689`, on Linux
x86_64. Compilation used four jobs, with test/dev debug information disabled
for the build and test gates. No search policy or heuristic was changed.

| Check | Result |
| --- | --- |
| `cargo build --all-features` | Pass |
| `cargo nextest run --workspace --all-features --test-threads 4 --no-fail-fast` | 11,887 passed, 14 skipped |
| `cargo test --workspace --all-features --doc` | 114 passed, 29 ignored |
| `cargo clippy --all-features --all-targets -- -D warnings` | Pass |
| `cargo fmt --all -- --check` | Pass |
| `cargo doc --no-deps --all-features` | Pass; workspace `rustdocflags` denies warnings |
| Explicit `pete_cxs_bp_is_unsat_on_every_trajectory` model-validation canary | Pass, 147.745 seconds |
| Z3 differential parity, installed **4.16.0** | 176 decisive agreements, 0 wrong, 1 inconclusive |
| Performance gate against cached `ac8279e5` | Pass; conflicts and decisions ratios both 1.000 |

The parity inconclusive case is `array_unique.smt2`: Nixie reports `Unsat`, Z3
reports `Unknown`; this is not counted as agreement. The performance gate has
10 measured instances and two trivial instances, with unchanged verdicts.
Its secondary wall-time ratio was 1.00. These results establish gate neutrality,
not an improvement or a measurement of large-table certificate overhead.

An earlier full-suite run had one 300-second timeout in
`solver::scope_rebase_tests::re_running_the_search_on_an_unchanged_goal_converges`
under heavy host load. The same test passed in isolation in 232.21 seconds;
the final full-suite rerun passed every scheduled test. The earlier CP landing's
recursive-function timeout is already fixed upstream by `05bc3654` and also
passes here. This landing needs no timeout exception.

An additional, non-gating `cargo check -p nixie-theories --no-default-features`
failed before reaching CP, in unchanged `nixie-math` code. The independent
control `cargo check -p nixie-math --no-default-features` reproduces the same
92 compile errors, including missing `std`/collection imports and the frozen
clock assertion. No math sources or feature definitions are changed here.
This configuration remains unverified; the successful all-features gates do
not establish `no_std` support.

The matching release binary, raw logs (including the initial timeout and
optional configuration failure), statuses, and parity JSON are retained under
`precompile/<this-commit>/benchmark/cp-table-certificate-verification/`, with
the binary at `precompile/<this-commit>/nixie`.
