# Independently checkable finite-domain explanations

This slice supplies the domain lemmas missing from the preceding table-certificate
slice. It does not enable end-to-end certified UNSAT. The remaining work includes
certificates for the other globals and exporting the axioms and lemmas into the
SAT proof chain.

## Rule and trust boundary

An immutable `DomainStatement` describes one original finite domain with unique
values and Boolean indicators. Exactly one indicator holds. The original
`BigInt` values and positive/negative terms are shared with the CP model through
an immutable `Arc`; later domain additions cannot change the statement.

`DomainCertificate` has three checked rules:

1. **DistinctFixed:** two indexed premises must be different positive indicators
   in the same original domain, and the conclusion must be false. At-most-one
   semantics contradicts their conjunction.
2. **Exclusion:** an indexed premise must be a positive indicator in the domain,
   and the conclusion must be the negative indicator of a different value.
   At-most-one semantics implies the exclusion.
3. **Exhausted:** the conclusion must be false and the witness must contain
   exactly one premise index per original value, in original order. Every index
   must designate that value's negative indicator. At-least-one semantics
   contradicts the conjunction. The empty domain has the valid empty cover.

Duplicate literal occurrences cannot establish distinct selections, and repeated
cover indexes cannot hide a missing value. Wrong polarity, foreign terms,
unsupported conclusions, and out-of-range indexes are rejected. Unused premises
only weaken the implication; their current truth remains an independent adapter
obligation. No rule uses rounded integers or unbounded native recursion.

The checker calls neither filtering nor witness production. The producer chooses
a rule from the recorded signed reasons and checks it before attaching it. A
missing witness for a domain-only step yields `Unknown`. The existing filtering
algorithm and search policy are unchanged. Exhaustion witnesses store one index
per original value; the other witnesses have constant size. Checking and producer
lookup add work; no CP throughput improvement is claimed.

## Layers examined

- **Construction:** the existing constructor rejects non-Boolean-variable
  indicators, repeated values, and indicator reuse within the model. The
  statement constructor is sealed; consumers retain originals before consuming
  the CP model. Original domains are immutable and shared.
- **Domain reduction:** unknown fixed-value terms remain `Unknown`; two positive
  selections, empty original domains, and exhausted domains now require checked
  conflict witnesses. Selecting one value supplies a checked exclusion of each
  unfixed alternative. No global feasibility routine is used by the checker.
- **Explanation:** rules check exact literals and exact conclusions, with checked
  access for every untrusted index and complete coverage for exhaustion.
- **Registration and SAT integration:** domain statement identities are installed
  only after successful callback registration. Every attached domain and table
  certificate must independently validate. Direct final conflicts use the same
  queue validation; arbitrary callbacks without metadata retain their existing
  trusted-client contract.
- **Scopes and reset:** callback queue snapshots clone certificates; retained
  originals survive nested rollback unchanged. A conditional lemma stays valid
  when its premises are popped, but cannot propagate until all reasons are true.
  Solver reset drops registered identities with callbacks and assertions.
- **Model and proof boundary:** model replay invokes certificate validation
  independently of search. Proof/certified-mode capability checks remain
  unchanged. These are lemmas relative to the CP exactly-one declaration,
  not bare Boolean tautologies or a portable full UNSAT certificate.

The read-only Z3 user-propagator `propagate_consequence` implementation informed
the distinction between a client's semantic obligation and the adapter's signed
antecedent/current-truth checks. CVC5's `ProofRuleChecker` confirms the separate
checker boundary and rejection of malformed arguments. Neither is linked.

## Evidence

The standalone adversarial test enumerates **2,993,160** candidate implications
and witnesses, accepting **2,496**. It covers candidate rules, premise-index
mutations (including `usize::MAX`), missing/surplus exhaustion covers, signed
premise lists of length zero through three, and supported/unsupported conclusions
for domains of sizes zero through three. Every accepted implication is evaluated
against concrete one-hot assignments and both values of an unrelated Boolean.
The expected semantics never call the producer or filtering code. Empty domains,
singletons, duplicate literals, foreign statements, and 132-bit values are covered.

A separate callback test visits every three-state partial assignment (unfixed,
false, true) for domains of size zero through three, including inconsistent
assignments, and requires a valid domain certificate on every emitted step.
It checks **79** emitted certificates and exercises later model additions and
nested push/pop. The generated CP oracle also authenticates/checks domain
certificates across all five globals and mixed
models: **33,258** domain certificates and **21,880** table certificates among
**171,301** consequences/conflicts, across **244** instances, **37,810** callback
states, and **6,704** complete assignments. These counts include repeated
emissions. All **6,100** public solver verdict/model checks pass. Pure-table
models must now attach either a domain or table certificate to every step, while
the independent assignment oracle still checks implications.

Solver regressions inject mutated and substituted witnesses during assignment
and direct final check, require true current premises, revoke statement authority
on reset, and exercise independent model replay. A valid table certificate cannot
hide an invalid domain certificate attached to the same consequence. A separate
callback test rejects non-Boolean fixed-value terms without emitting a conflict.
Proof mode remains `Unknown`.

These are bounded implementation tests plus the rule arguments above, not a
machine-checked proof of the Rust code.

## Verification conditions and first-run timing failures

Verification uses Linux x86_64, based on `bd05775b`, with four compilation jobs
and dev/test debug information disabled. The initial full all-features nextest
run used four test workers. It ran all 11,903 scheduled tests: 11,899 passed,
two failed wall-time assertions, and two hit the runner's 180-second limit;
14 were skipped by the existing test configuration. The nonpassing tests were:

- `odd_width_identity_pairs_hold`: outer runner timeout. The unchanged test
  executable passed in isolation in **193.79 seconds**, with every original
  assertion enabled and a finite 600-second outer limit.
- `qfidl_dtp_s1_dense_route_is_fast_and_correct` and
  `qfidl_dtp_s14_unsat_is_fast_and_correct`: both produced the expected verdict,
  then failed the test's five-second elapsed-time assertion after about ten
  seconds. Unchanged isolated reruns passed in **0.08** and **0.19 seconds**.
- `arith_incremental_matches_replay_fuzz`: outer runner timeout.

These tests do not register CP propagators; their implementation and inputs are
unchanged by this slice. Host load averages rose above 190 during verification.
The evidence supports rerunning with less concurrency and more outer-runner
time; it does not establish a solver performance change. The initial failed
run is retained, not omitted from the record.

The complete suite is rerun with two workers and a temporary copy of the
repository's nextest configuration that raises each outer `terminate-after`
count to at least ten 60-second periods. Test groups, inputs, assertions,
solver budgets, and ignored-test settings are unchanged. In particular, the
arithmetic tests' five-second assertions are preserved. This runner-only
configuration is archived with the logs; the repository configuration is not
changed. No failed or timed-out test is accepted as a passing result.

## Final verification results

The full rerun passed **all 11,903 scheduled tests**, with 14 existing skips and
no failures or timeouts, in 1,205.054 seconds. Arithmetic incremental fuzzing
passed in **191.234 seconds**; the bit-vector identity test passed in **83.459
seconds**. The two arithmetic wall-time tests passed in **0.112** and **0.150
seconds**, retaining their original five-second assertions. The standard-budget
first run was not clean; the successful full rerun uses the explicitly documented
outer runner budget above.

| Gate | Result |
| --- | --- |
| `cargo build --all-features` | Pass |
| Full workspace/all-features nextest, two workers, archived runner configuration | 11,903 passed, 14 skipped |
| `cargo test --workspace --all-features --doc` | 114 passed, 29 ignored |
| `cargo clippy --all-features --all-targets -- -D warnings` | Pass |
| `cargo fmt --all -- --check` | Pass |
| `cargo doc --no-deps --all-features` | Pass; workspace rustdoc flags deny warnings |
| Explicit model-validation canary `pete_cxs_bp_is_unsat_on_every_trajectory` | Pass, 307.984 seconds, existing repository runner configuration |
| Z3 differential parity, installed **4.16.0** | 176 decisive agreements, 0 wrong, 1 inconclusive |
| Performance gate, cached baseline **ac8279e5** | Pass; conflicts and decisions ratios both **1.000** |

Parity's inconclusive case remains `array_unique.smt2`: Nixie reports `Unsat`,
Z3 reports `Unknown`, which is not counted as agreement. The performance gate
has ten measured instances plus two trivial instances and no verdict changes.
Its secondary wall-time ratio is 0.80. The deterministic counters establish
neutrality on that corpus, not a throughput improvement or a measurement of
large-domain certificate overhead.

Rust compiler: `rustc 1.96.0 (ac68faa20 2026-05-25)`. The full rerun command was:

```sh
CARGO_BUILD_JOBS=4 CARGO_PROFILE_TEST_DEBUG=0 CARGO_PROFILE_DEV_DEBUG=0 \
  cargo nextest --config-file /tmp/nixie-cp-domain-loaded-host-nextest.toml \
  run --workspace --all-features --test-threads 2 --no-fail-fast
```

The matching release binary is cached at `precompile/<this-commit>/nixie`.
Raw logs and statuses, the temporary runner configuration, Cargo lockfile,
parity JSON, and an artifact manifest are retained under
`precompile/<this-commit>/benchmark/cp-domain-certificate-verification/`.
