# Native sequence optimization

## Pre-registration

Start from `c9090b8d`, whose solver code matches the measured `3a42cb2d`
binary. The motivating workload is the native fixed-length history family,
especially the 28.86B-instruction length-512 case. Inspect a symbolized
unchanged baseline before attributing the cost or changing the hot path.

Aim to remove redundant work without changing inference, search ordering,
budgets, sequence semantics, or independent model validation. For purely
mechanical changes preserving the same search, compare complete-process
user instructions against the unchanged implementation, with the existing
22-case ten-seed corpus and Z3 4.16.0 records. No claim about independent
Nixie seed variation: the existing native child-solver seed propagation
limitation remains in this experiment. A search-policy change would require
a separately specified matched-null experiment and is outside this plan.

Accept only a material reduction (>5%) in supported-history work with no
lost decisive answers or incorrect verdicts, and passing full correctness,
parity, and performance gates. Report every corpus result and any regressions
outside the motivating family. Use pinned, non-multiplexed user instruction
counts as primary; wall time only as a secondary observation. Reuse existing
cells, keep diagnostic configurations separate, and preserve failed
experiments instead of rerunning or silently dropping them.

Cache lifetime is a correctness constraint. Z3's model evaluator binds its
rewriter cache to a model and resets on model/completion changes
(`src/model/model_evaluator.cpp:746–818`). CVC5 also caches model-value work
and uses explicit traversal state (`src/theory/theory_model.cpp`). A Nixie
evaluation cache must bind an immutable model and one term manager, never
outlive model completion or leak into another check, and retain the iterative
DAG walk and refusal of fabricated native operator assignments.

## Diagnosis and changes

The symbolized baseline changes the earlier attribution: the length-512
history spends about 25% of sampled instructions in `EufSolver::pop`, 18%
in `__strncmp_avx2`, 8.6% in `getenv`, and substantial remaining work in
exact rational arithmetic. The native child search performs 462,672 decision
trace events. Independent validation is not the primary cause of the large
search cost; caching it alone would not address these hot paths.

Three mechanical changes remove redundant work:

* EUF `pop` skips the complete `term_to_node.retain` scan when the scope
  removed no nodes. All three insertion sites allocate each term's own node,
  including applications already congruent with an existing node; merges do
  not rewrite that map. Therefore no entry can be removed in this case.
  Scopes that created nodes keep the exact previous retain operation/order.
  All union-find, signatures, watches, reasons and explanation-cache rollback
  remain in their original order. Z3's egraph similarly undoes term mappings
  with node creation records (`ast/euf/euf_egraph.cpp:411–445`).
* The arithmetic bound-write diagnostic `NIXIE_BOUND_TRIPWIRE` is read once
  through `OnceLock`, like the existing SAT diagnostic flags. It still emits
  the same diagnostics when enabled before first use; it no longer scans the
  environment on every lower/upper write. This flag changes diagnostics only,
  not bound values, explanations, work budgets or scheduling. Mid-process
  environment mutation is no longer a way to toggle this diagnostic.
* Final validation uses one iterative sequence `Evaluator` across all
  original assertions. Its immutable model borrow and exclusive term-manager
  borrow bind the caches to one model and one manager. Completion uses fresh
  evaluators as assignments are filled. No cache survives a check, model
  mutation, `push`, `pop`, assertion or public model query. Failure-local
  traversal state cannot contaminate the next root. Native operator model
  assignments remain ignored; unsupported evaluations still return Unknown.

The evaluator work regression constructs 128 reads of one shared sequence:
exactly `4*128+2` unique nodes expand across all roots, and reevaluating those
roots expands none. Other new regressions cover cyclic models, failed walks,
model changes and forged native results; a nested EUF scope test alternates
node-creation and merge-only rollback and checks exact term/node identities.
Existing deep-DAG, scope, arithmetic and EUF fuzz tests cover the surrounding
paths. No sequence fragment, AST ordering or search policy was changed.

## Measured result

The 22-case corpus was measured at the original CPU/event/cap settings with
ten requested seeds: **190/220 decisive candidate runs, 30 Unknown, zero
wrong answers/errors/timeouts**, matching the original Nixie coverage exactly.
All 190 decisive baseline/candidate pairs have valid instruction counters.
The three symbolic probes still return Unknown; no Unknown counts as a solve.
The native child-seed propagation limitation is unchanged.

| History length | Baseline instructions | Candidate instructions (median [min–max]) | Candidate/baseline |
|---:|---:|---:|---:|
| 8 | 6.133M | 5.259M [5.257–5.262] | 0.8574 |
| 32 | 22.171M | 13.443M [13.442–13.450] | 0.6064 |
| 128 | 255.054M | 95.691M [95.684–95.713] | 0.3752 |
| 512 | 28860.809M | 11005.940M [11005.844–11006.773] | 0.3802 |

The length-512 case uses **62.0% fewer instructions (2.63× less work)**.
Across the four history sizes the geometric ratio is **0.5218**; across all
19 commonly solved cases it is **0.8730**. All other cases lie between
0.9915 and 1.0113, inside the ±5% neutrality band. No cases were dropped.
The full per-case, ten-seed distributions are retained in `summary.json`.

Against the original Z3 4.16.0 records, the geometric ratio over 15 commonly
solved cases is **0.0504** (19.84× fewer user instructions).
The four original Z3 timeouts remain censored, and Z3 still solves the three
symbolic probes this Nixie slice declines. This is a conditional result on
the synthetic fixed-shape corpus, not a claim about general sequence solving.

The candidate and symbolized unchanged baseline have **byte-identical
464,880-line** complete stdout/decision/conflict traces on `history-512`,
including all 462,672 decision events. SHA-256 of each complete trace:
`6749ea7391c6b7128e47a2e81e923ab6635d76d37434f5ae5246e58dd72284d5`.
That observed trajectory identity agrees with the structural argument:
no-op map scans and inactive diagnostics cannot change inference, and the
validation cache runs after search with a fixed model. This is engineering
work reduction, not a heuristic policy treatment compared with a weak null.

The remaining ~11B instructions and hundreds of thousands of decisions are
still a scaling limitation. A future change to encoding or search must be
measured separately; this landing does not claim to remove that search.

## Reproduction and verification

The benchmark runner `bench/native_sequences/compare_optimization.py` takes
`--candidate`, the original record directory as `--baseline`, and `--out`.
It records new cells once, fingerprints the candidate and environment without
saving environment secrets, and joins existing Nixie/Z3 cells without reruns.
`--summarize-only` checks cache identity and regenerates summaries without
executing solver cells. The original benchmark did not fingerprint its
inherited environment; that limitation persists in historical comparisons.
The large effect is additionally supported by the unchanged-search trace.

The release build retains symbols (`CARGO_PROFILE_RELEASE_STRIP=none`) for
profiling; optimization, LTO and codegen settings are unchanged. Baseline
symbols, profiles and the original trace are cached with `c9090b8d`; the
candidate binary and comparison records will be cached with the landed commit.
Debug/test gates use `CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0
CARGO_INCREMENTAL=0` to fit the shared filesystem, retaining assertions.

During verification, `32e2b695` added a heap statistics/seed API and benchmark
example on main. The pre-integration workspace run was stopped during test
compilation, that commit was fast-forwarded into the worktree, and all full
build/lint/doc/test gates restarted on the integrated tree. The resulting
release executable is **byte-identical** to the already measured candidate:
`1b82996ba06c3ec34448638bebfd26c4bfb528f65236a82a1112982f10558e2c`.
Consequently no comparison, profile or CLI gate cell was rerun under a new
label just because the base commit advanced.

Completed verification:

* Native integration suite, including opt-in Z3 differential: 12 passed,
  with 214 decisive agreements against installed Z3 4.16.0.
* Focused evaluator unit tests: 5 passed, including the new shared-work and
  cache-lifetime regressions.
* Full Z3 parity: 176 Correct, 0 Wrong, 1 Inconclusive, 0 Timeout, 0 Error
  across 177 inputs. The existing `AUFLIA/array_unique.smt2` remains Nixie
  Unsat versus Z3 Unknown and is not counted as a match.
* Performance landing gate: PASS; all nine nontrivial cases have identical
  conflicts and decisions (both geometric ratios 1.000). Three configured
  external cases retain their verdicts. Secondary wall ratio 1.19, under
  concurrent build load, is not used as a performance-improvement claim.
* Standing instruction comparison: geometric ratio **1.0010** over all
  12 cells, with unchanged verdicts/conflicts. This confirms neutrality
  outside the motivating sequence history family.

Final integrated workspace gates:

* `cargo build --all-features`: passed.
* `cargo clippy --all-features --all-targets -- -D warnings`: passed.
* `cargo fmt --all -- --check`: passed.
* `cargo doc --no-deps --all-features`: passed with the repository's
  `rustdocflags = ["-D", "warnings"]`.
* `cargo nextest run --workspace --all-features --build-jobs 4
  --test-threads 4`: **12,208 passed, 0 failed, 17 skipped** (327.662s).
* Separate workspace doctests: **114 passed, 0 failed, 31 ignored**.

The separately required ignored congruence canary
`pete_cxs_bp_is_unsat_on_every_trajectory` **passed** (118.579s). It was run
explicitly because `.config/nextest.toml` and the test documentation require
it before congruence/model-checking changes; its longer budget was unchanged.

Main's subsequent `622f03ca` heap performance report was also fast-forwarded
into the worktree. That commit changes documentation only; no Rust source,
binary, or test behavior changed after the integrated gates above.
