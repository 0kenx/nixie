# Exact heap separation

`nixie_solver::heap::HeapSolver` is a dedicated, pure-Rust API for
**quantifier-free Boolean combinations of exact symbolic heaplets and linear
integer arithmetic**. It owns its term arena and underlying `Solver`, preventing
heap atoms from accidentally being checked as unconstrained Boolean variables.
It is also reachable through `nixie::solver::heap`. It does not add SMT-LIB
`declare-heap`, `sep`, or `pto` commands to the general parser.

## Supported fragment

Locations and stored values are arbitrary-precision mathematical integers.
Zero is the distinguished nil location and is never allocated; negative locations
are allowed. A heap is a finite partial map from nonzero integers to integers.
No finite location universe or user-selected heap bound is assumed.

The grammar is:

```text
t ::= integer | integer-variable | t+t | t-t | integer*t
H ::= emp | t |-> t | H * H
F ::= true | false | Boolean-variable | t=t | t<=t | H
    | not F | and(F,...) | or(F,...)
```

`Heaplet::emp`, `Heaplet::points_to`, and `Heaplet::star` construct `H`;
`HeapSolver::reify` turns `H` into `F`. Boolean operators may nest arbitrarily
outside heaplets, with either polarity. Implication, equivalence, and exclusive
or are expressible using `not`/`and`/`or`. Disequality and strict comparisons are
expressible by negation. Pure formulas have their usual interpretation on every
heap. In particular, `true` is not `emp`.

* `emp` holds exactly when the heap is empty.
* `x |-> v` holds exactly when the heap is the singleton `{x -> v}` and `x != 0`.
* `H1 * H2` holds when the current heap is the union of **disjoint** heaps
  satisfying its operands. Duplicate addresses make it false even if the values
  agree. An empty separating conjunction is `emp`.
* Classical conjunction evaluates both operands on the **same** current heap;
  it does not add ownership. Thus `(x |-> v) and (x |-> v)` is satisfiable, while
  `(x |-> v) * (x |-> v)` is not.

There is one current heap per solver. This release excludes Boolean formulas
inside `*`, magic wand, quantification, inductive predicates, allocation commands,
concurrency verification, fractional ownership, and unrestricted entailment.
It also excludes array/datatype-valued cells, nonlinear data expressions, and
mixing arbitrary general-SMT terms into the dedicated API. The typed constructors
make these exclusions explicit; unsupported syntax is not abstracted away.

## Allocation and validity example

Run `cargo run -p nixie-solver --example heap_allocation`. The executable example
constructs the symbolic post-allocation state

```text
P = (x |-> 7) * (y |-> 9)
```

and extracts a concrete two-cell heap. To verify `P => x != y`, it pushes a
scope and asserts the counterexample condition `x = y`. The resulting `unsat`
establishes that these two exclusively owned allocations cannot alias. Popping
restores the satisfiable post-allocation state.

Generally, validity of a supported `F` is checked by satisfiability of `not F`.
An entailment `P |= Q` **within the grammar above**, over the same valuation and
heap, is checked as `P and not Q`. `Unsat` proves this validity, `Sat` supplies a
validated counterexample, and `Unknown` proves neither. This does not implement
a program verifier, unrestricted entailment, or validity of excluded predicates.

## Reduction and correctness argument

This is the exact-heaplet specialization of finite-map/set labeling, reduced to
QF_LIA. Flatten each heaplet `Hi` into a list of `(location,value)` terms. Let:

* `Vi` require non-nil, pairwise distinct locations;
* `Eij` require equal list length and, for each cell of `Hi`, a cell of `Hj`
  with equal location and value;
* `pi` be the reified Boolean atom for `Hi`.

The defining constraints are `pi => Vi` and, for every unordered pair, both

```text
pi => (pj <=> (Vj and Eij))
pj => (pi <=> (Vi and Eij)).
```

Under `Vi` and `Vj`, `Eij` is equality of finite maps: equal finite cardinalities
and inclusion imply equality. It is insensitive to list order. Invalid heaplets
cannot be true, but negating them is perfectly meaningful.

Necessity follows by interpreting each `pi` as satisfaction on the concrete
current heap. For sufficiency, if some `pi` is true, take the map described by
`Hi`. The constraints make every `pj` agree with satisfaction on that map.
If all `pi` are false, choose a heap with `M+1` cells, where `M` is the maximum
registered heaplet length (zero if none). Its cardinality differs from every
registered heaplet, so every `pi` is indeed false. Infinite integer locations
provide these cells without restricting the pure valuation. Consequently the
reduction preserves satisfiability under **arbitrary outer Boolean contexts**.
The `M+1` case is a witness construction, not an assumption bounding input heaps.

At check time the implementation extracts entailed heap-atom units from the
original Boolean DAG (true conjunctions, false disjunctions, and negation).
It substitutes these constants into the definitions before backend encoding.
The original assertions remain active and imply equivalence of the original
and specialized definitions. True disjunctions and false conjunctions do not
force individual children. If every atom is forced false, every guarded
definition is a tautology and no heap arithmetic is encoded. A false atom's
validity/map comparison is still required when another atom may be true.
`set_definition_simplification(false)` selects a semantics-equivalent diagnostic
control that retains symbolic atoms while using the same deferred staging.

The encoding costs O(n² k²) in the worst case for n heaplets of at most k cells.
This first implementation targets small allocation/aliasing obligations; it
makes no performance claim for large heaps. There is no new search heuristic.

## Models, scope state, and proofs

`HeapModel` publishes a finite `BTreeMap<BigInt,BigInt>` and named integer and
Boolean assignments. A positive heap atom selects its concrete heaplet map;
otherwise extraction constructs the larger witness above. Omitted backend
variables receive explicit candidate values (zero/false), followed by mandatory
validation; completion alone never justifies `Sat`.

The independent checker evaluates the **original input arena**, not generated
pairwise constraints, and ignores backend assignments to compound expressions.
For each heaplet it builds a concrete map, rejects nil or duplicate locations,
and compares that map with the candidate heap. It then evaluates every active
original assertion using exact `BigInt` arithmetic. Traversal and arena drop
are iterative, with no recursion over input formulas. Callers may also use
`evaluate` and `validate_model` on inspected or modified models. Foreign solver
handles/models and missing assignments are errors.

Reify all heaplets before the first `push` or `check`. The spatial vocabulary
is fixed for that solver. Specialized definitions live in a private backend
scope above the active user assertions. They are removed before `assert`, user
`push`, or successful user `pop`, and regenerated at the next check. Repeated
checks without such mutations reuse them. Assertions can be added in nested
scopes; the underlying solver retains its ordinary incremental tables and
rollback journal. No solver is rebuilt at each check. `assert`, `push`, `pop`, and term construction invalidate
the published model. Scope underflow and late reification are errors. Create a
new solver to change the registered spatial vocabulary.

`Sat` is released only after the concrete model passes the independent checker.
Backend resource limits, incomplete backend model extraction, or failed original
formula validation yield `Unknown`, with `reason_unknown()` explaining the
boundary. Integer constants and checker arithmetic never truncate; backend
arithmetic limitations remain honest `Unknown` boundaries.

**No heap proof translation or proof export is implemented.** Ordinary `Unsat`
relies on the reduction argument and the existing QF_LIA solver. A configuration
requesting proofs or certified verdicts returns `Unknown` for this API, including
trivial instances. No underlying arithmetic proof is advertised as a proof of
the original spatial formula. Unsat-core extraction is not exposed here.

## Fractional permissions: separate extension

Disjoint heaps provide exclusive cell ownership, not fractional ownership.
Viper's fractional permission semantics permits read access at any positive
fraction and write access only at full permission; permissions to the same
location add, with a total no greater than one. Implementing that would require
an explicit permission component and exact composition checks, including stored
value agreement for overlapping positive shares. None of those operations or
claims is part of this release. See the
[Viper fractional-permission semantics](https://viper.ethz.ch/tutorial/permissions-fractional.html).

## Infrastructure inspected and references

Before adding the API, searches of `nixie-*` found no `SepStar`, `SepPto`,
`PointsTo`, `declare-heap`, `sep.emp`, or separation-logic implementation.
Inspected existing infrastructure:

* `nixie-theories/src/array`: total arrays, read-over-write and extensionality;
  these do not encode partial-heap ownership or separation.
* `nixie-theories/src/datatype`: constructors, selectors, and acyclicity;
  recursive datatype values are not inductive spatial predicates.
* `nixie-theories/src/arithmetic`: exact LIA reasoning and its overflow/resource
  decline paths; the heap reduction uses the existing QF_LIA solver.
* `nixie-solver/src/solver/user_propagation.rs`: explained callbacks and proof
  authentication; no heap callback exists. The exact reduction avoids introducing
  an unproved custom conflict-clause generator.
* `solver/model_builder.rs`, `solver/model_eval.rs`, and `solver/types.rs`: model
  extraction and iterative evaluation. A separate original-input evaluator is
  needed to certify spatial semantics rather than only the generated constraints.

Read-only reference inspection covered CVC5's
`src/theory/sep/{kinds.toml,theory_sep_rewriter.cpp,theory_sep_type_rules.cpp,theory_sep.cpp}`:
singleton labels, disjoint child labels, nil exclusion, handling negative spatial
constraints, and concrete label-model extraction. This implementation neither
links CVC5 nor ports its broader magic-wand/quantifier machinery.

The semantic and decision-procedure reference is Reynolds, Iosif, Serban, King,
[*A Decision Procedure for Separation Logic in SMT*, TACAS 2016](https://cvc4.github.io/publications/2016/RIS%2B16.pdf),
especially §2.1 (finite partial heaps and exact points-to), §3 (labeling), and
the discussion of finite representations. Our restricted grammar permits the
direct finite-map reduction above; we do not claim the paper's entire fragment.

`nixie-solver/tests/heap_separation.rs` compares every complete Boolean assignment
over a small heaplet vocabulary against independently enumerated finite maps,
and includes a CVC5 reference test with nil fixed to zero:

```bash
cargo test -p nixie-solver --test heap_separation
CVC5=/path/to/cvc5 cargo test -p nixie-solver --test heap_separation \
  cvc5_ -- --ignored
```

The reference test treats any `unknown`, error, missing output, or wrong verdict
as a failure. CVC5 1.3.4 rejects incremental separation logic, so it checks each
flattened active scope in a fresh process. Nixie's scope restoration is tested
directly against the exhaustive model oracle.

Performance measurements use the [exact-heap benchmark suite](../bench/heap_perf/README.md):
allocation, aliasing, stored-value disagreement, permutation and negated heaplets,
with CVC5 native SL and CVC5/Z3 UF+array references. `HeapSolver::statistics()`
exposes encoding sizes and backend search counters; these are diagnostics, not a
complete-work metric. `set_random_seed` selects a reproducible backend seed and
invalidates a previous model. The suite measures retired instructions through
encoding, solving and independent model validation. These measurements concern
the exact-heap LIA reduction, not inductive predicates or native SL performance.

The [measured performance study](studies/2026-09-22-exact-heap-performance.md)
records both successful workloads and the all-negative scaling limit, with ten
seeds, complete-work instruction counters, and CVC5/Z3 comparisons.
