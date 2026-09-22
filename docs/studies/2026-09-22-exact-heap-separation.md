# Exact heaplet separation: implementation and audit

This landing adds the restricted Rust API documented in [`HEAP.md`](../HEAP.md).
It reduces Boolean combinations of exact integer heaplets to QF_LIA and checks
every published heap model against the original formulas. No native heap
primitive was present before this work; arrays, datatypes, arithmetic, user
propagation, and model-validation paths were inspected before choosing the
reduction. It changes no existing theory dispatch or SAT search heuristic.

## Semantic audit

| Layer | Invariant and evidence |
| --- | --- |
| Input vocabulary | Owned typed handles, no raw `TermId` escape; a foreign handle fails before definitions/assertions are changed. Boolean formulas cannot be passed to `Heaplet::star`. |
| Spatial composition | Flattened points-to lists retain duplicate occurrences. Validity requires every address nonzero and pairwise distinct; agreeing values never make overlapping ownership valid. |
| Heap identity | Equal lengths plus cell membership characterize map equality only under validity. Both implication directions include the relevant validity conditions. Permuted heaplets, unequal values, invalid duplicates, and nil are covered by exhaustive truth patterns. |
| Negative formulas | No existential heap-split variables occur under negation. If no atom is true, a heap of maximum heaplet length plus one realizes that exact truth assignment. Pure `true` is distinct from `emp`. |
| Arithmetic | Integer constants, original-input operations, and extracted heap cells use `BigInt`. Backend model terms are accepted only as concrete integers (or denominator-one rationals); unsupported extraction declines. Wide literal and symbolic tests exclude truncating false verdicts. |
| SMT integration | Permanent defining constraints go through the ordinary QF_LIA solver. The dedicated API hides that backend and its internal atoms, so clients cannot accidentally bypass heap validation. No custom unproved conflict clauses are introduced. |
| Incremental state | All heaplets are registered before first push/check. Original assertions have scope-length checkpoints, while backend scopes use their existing journal. Every mutation invalidates the published model. Exhaustive symbolic cases repeatedly push and pop two levels. |
| Witness construction | A positive backend atom selects its concrete map; all-false gets the cardinality witness. Missing variable assignments are explicit candidate completion followed by independent validation, never accepted on completion alone. |
| Independent validation | The original arena is evaluated without consulting generated formulas or backend assignments to compound terms. Concrete maps reject duplicate/nil addresses. Tampered values, aliasing, nil allocation, missing variables, and wrong Boolean controls are rejected. |
| Depth and ownership | Original arena edges are indices, not recursively owned nodes. Evaluation and destruction pass a 50,000-negation test on a 256 KiB native stack. `Arc` identity rejects handles and models from another solver. |
| Proof/result boundary | Proof-producing and certified configurations return `Unknown`; no heap proof translation is claimed. Backend `Unknown` and failed model validation propagate honestly. |

The sufficiency proof for the pairwise reduction is in `HEAP.md`. Tests cover
all 256 complete Boolean assignments for eight ground atoms and all 576
assignments for four symbolic atoms across 36 location/data valuations. The
oracle enumerates all partial maps on three non-nil locations with two values;
three cells witness the all-false class for these at-most-two-cell atoms.

## Reference alignment

Read CVC5's separation theory source (label singleton/disjointness rules, nil,
negative spatial assertions, and model extraction), Reynolds et al., TACAS 2016,
and Viper's fractional-permission semantics. The supported fragment deliberately
excludes Boolean operators inside separating conjunction and fractional shares.

Reference executable: **CVC5 1.3.4**. Nil is explicitly fixed to integer zero to
match this API. The first reference harness attempted incremental mode; CVC5
rejected it with `separation logic not supported with incremental solving`.
The corrected harness checks each flattened scope in a fresh process. Do not
retry incremental CVC5 separation mode on this version. Nixie's incremental
tests use the exhaustive oracle directly.

## Verification environment

The work was isolated in a worktree. The initial normal all-features build
passed. The first full-suite compilation was stopped before tests ran because
debug artifacts nearly exhausted the temporary filesystem. Only this worktree's
target directory was removed. Subsequent development/test gates use
`CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0 CARGO_INCREMENTAL=0`; these
disable debug information and incremental compilation, not assertions or tests.
Dependencies are locally cached (`CARGO_NET_OFFLINE=true`).

The documentation gate uses `cargo doc --no-deps --all-features` with the
repository's `.cargo/config.toml` `rustdocflags = ["-D", "warnings"]`, because
Cargo does not accept the guide's trailing `-- -D warnings` for `cargo doc`.
Doc tests run separately; `nextest` does not execute them.

## Gate results

* `cargo build --all-features`: passed (also repeated on the final source).
* `cargo clippy --all-features --all-targets -- -D warnings`: passed.
* `cargo fmt --all -- --check`: passed.
* Documentation with warnings denied: passed.
* `cargo test --workspace --all-features --doc`: 114 passed, 31 intentionally
  ignored. Cargo reports that `nixie-wasm`'s cdylib has no supported doc-test target.
* Heap integration tests including both optional CVC5 tests: **14 passed**.
  All **832** truth-assignment queries agree with both exhaustive models and
  **CVC5 1.3.4**; `unknown` is not counted as agreement.
* `heap_allocation` example: passed, extracting `{-2: 9, -1: 7}` and refuting
  the aliasing counterexample. Negative addresses are legal under this API.
* Z3 parity (`./bench/z3_parity/run_parity.sh`), actual comparator **Z3 4.16.0**:
  **176 Correct, 0 Wrong, 1 Inconclusive, 0 Timeout, 0 Error** over 177 cases.
  The inconclusive case is the existing `AUFLIA/array_unique.smt2`: Nixie gives
  `Unsat`, Z3 gives `Unknown`. This is not counted as a match, and reproduces
  the comparator limitation recorded in prior studies.
* Performance gate against pinned `28e82c65`: **PASS**. All nine nontrivial
  corpus cases have identical conflicts and decisions (both geomeans **1.000**).
  All three configured external cases also preserve their trivial verdicts.
  No verdict mismatch or lost sample occurred. Wall ratio was 1.01 as a
  secondary load check, not the primary metric. Candidate release binary SHA-256:
  `ec6ea615c11357747163e02912a3064df6c55a338877174e6b7b432e6a742a52`.

The first completed full-suite attempt ran 12,189 tests: 12,186 passed,
three existing `scope_rebase_tests` timed out (180/180/300 seconds), and 16 were
skipped. There were no assertion failures. The full gate was repeated with
`--test-threads 4`, preserving the test bodies and supervision budgets:
**12,189 passed, 0 failed, 16 skipped**. The three previously timed-out tests
passed in 82.914, 82.749, and 224.015 seconds. No solver/test code or timeout
increase was needed. The two optional CVC5 tests among the skips were explicitly
run and passed separately, as recorded above.
