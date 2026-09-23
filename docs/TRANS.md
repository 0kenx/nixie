# The Transcendental Theory (δ-Satisfiability)

Nixie decides constraints over the reals with **transcendental functions** —
`(exp x)`, `(log x)`, `(sin x)`, `(cos x)`, `(atan x)`, `(sqrt x)` — using
**dReal-style δ-satisfiability**: interval constraint propagation (ICP)
driving a dPLL loop, with interval arithmetic whose enclosures are
mathematically guaranteed. Real arithmetic with even one of these functions
is *undecidable* (the integers are definable through `sin`/`exp`), so no
decision procedure exists; this engine is the honest calculus for that
world:

* **`unsat`** answers are true refutations.
* **`sat`** answers are **δ-satisfiability** witnesses — printed as
  `delta-sat` — never claimed exact models.
* everything else is **`unknown`**, never a guess.

This follows the δ-decision framework of Gao–Avigad–Clarke (the dReal
solver); dReal users should feel at home.

## The fragment

Ground, quantifier-free goals whose arithmetic (over `Real`) is built from
`+ − * /`, the six transcendental functions, numeric `ite`, and
`≤ < > ≥ = ≠ distinct`, under arbitrary Boolean structure (`and or not =>
xor ite`). Variables are `Real`-sorted. Set the logic to `QF_NRT` (or leave it
unset/`ALL`).

**Ground uninterpreted functions over the reals** are admitted via
Ackermannization before the Boolean abstraction: every application `f(t…)`
becomes a fresh Real variable and the functional-consistency implications
`(t1 = t1' ∧ …) ⇒ v = v'` join the Boolean skeleton, so the dPLL loop
carries exactly the ground congruence semantics EUF would (applications
whose arguments are quantifier-bound are never Ackermannized — those goals
stay declined). A `distinct` expands to its pairwise negated equalities
(arity ≤ 16; beyond that the goal is declined rather than atom-bombed).

Everything outside the fragment is **declined with `unknown`**, not
approximated: quantifiers, uninterpreted functions with non-ground
occurrences, arrays, strings, FP, datatypes, integer-sorted variables. The
reasoning is always the same: an encoding that *drops* the semantics of a
construct solves a weaker problem than the one asked, which yields false
`sat`s. (A closed logic like `QF_LRA` rejects a transcendental atom at the
logic-contract layer, as it does any nonlinear arithmetic.)

## Semantics

For a constraint `e ⋈ c` (normalized so the right side is a constant), the
engine decides against the **δ-weakened** bound `c ± δ·(1+|c|)`:

* **`unsat`**: the δ-weakened *conjunction under every Boolean assignment*
  is proved empty by box pruning. Since weakening only ever adds
  solutions, δ-unsat implies unsat — a sound refutation.
* **`delta-sat`**: a witness point was found (and re-verified after
  rounding to the published rationals — what `(get-value …)` prints is
  exactly what was checked) that satisfies every constraint within its
  δ-tolerance. This is a model of a δ-perturbation of the formula, not of
  the formula itself; the CLI therefore prints `delta-sat`, dReal's
  spelling, rather than `sat`.

Strict comparisons weaken to their non-strict forms in both directions:
`¬(a < b)` is exactly `a ≥ b`, and for the positive direction the δ-slack
dominates the strictness, so `a < b` is decided as `a ≤ b`. Under
δ-semantics this is exact, not an approximation.

**Totalized functions** (SMT demands totality; dReal's choices):

* `log(x)` for `x ≤ 0` is `−∞` (so `log(x) ≤ c` holds for any `c` there,
  while `log(x) ≥ c` with finite `c` forces `x > 0`);
* `sqrt(x)` for `x < 0` is `0`;
* division by an interval that may contain 0 evaluates to the whole line
  (a sound over-approximation) and *blocks verification* of any constraint
  whose value flows through it — the witness must pin the divisor away
  from 0 or the verdict stays `unknown`.

## Architecture

```
check-sat
  └─ dispatch_trans_solver            (nixie-solver/src/solver/check_trans.rs)
       ├─ gate: trans terms present? open logic / QF_NRT?
       ├─ Tseitin the Boolean skeleton over the ARITHMETIC ATOMS
       │    into a private nixie-sat instance
       └─ dPLL loop:
            ├─ SAT assignment → per-assignment compilation
            │    (numeric ites resolved by evaluating the condition)
            ├─ solve_conjunction              (nixie-theories/src/trans/)
            │    ├─ forward interval evaluation + backward contraction
            │    │    (HC4-style, over the shared term DAG; every node
            │    │     carries a value interval + provenance deps)
            │    ├─ δ-weakening applied ONLY at constraint roots
            │    ├─ point-witness acceptance: midpoints rounded to
            │    │    Rational64, re-verified, published
            │    └─ branch (finite half first) on the widest variable
            │         that feeds a compound node
            ├─ ICP unsat(assignment) → valid blocking clause over the
            │    implicated atoms (culprit provenance when available)
            ├─ δ-witness → install model, answer delta-sat
            └─ unknown → honest unknown
```

The **dPLL ∘ ICP** split is dReal's: the SAT engine owns the Boolean
structure, the interval engine owns each conjunctive fragment. The
alternative (feeding everything to one box search) cannot handle
disjunctions; the other alternative (the CDCL(T) core) has no interval
theory wired into its combination layer.

### Why `unsat` is sound

Three invariants carry the refutation:

1. Every interval is an **outward-rounded enclosure** of the true range
   (`nixie-math::transcendental`): arguments are exact dyadic rationals,
   series are summed in directed interval fixed-point with rigorous tail
   bounds, constants (`ln 2`, `π`) are exact-rational brackets. No host
   libm is on the proof path.
2. Backward contractions are **exact real arithmetic** (`t ∈ log(v)` for
   `v = exp(t)`, `a ∈ v/b` when `0 ∉ b`, `x ∈ ±[√lo, √hi]` for
   sign-definite squares, …): they never remove a solution of the (weak or
   strong) constraint system.
3. The δ-weakening lives **only at constraint roots**; an empty box
   therefore refutes the weakened conjunction, which refutes the original.

The blocking clause for a refuted assignment is a valid theory lemma for
the same reason: δ-unsat of a conjunction implies its unsat. SAT-core
unsatisfiability after finitely many such lemmas is a proof.

### Known incompleteness (by design)

* **Unbounded periodic goals**: `sin(x)² + cos(x)² = 0` over all of ℝ is
  refutable only with periodicity reasoning ICP does not carry; bisection
  can never exhaust an unbounded ray, and the engine answers `unknown`
  (bounded variants refute quickly). dReal has the same shape.
* **Budgets**: branch nodes (100k default) and propagation steps are
  bounded; exhaustion is `unknown`.
* `≠` prunes only in its whole-box form: a disequality conflicts when the
  root interval lies entirely inside the δ-window (no point of the box can
  δ-satisfy it); otherwise it verifies pointwise. Splitting a box to
  exclude a single point is disjunctive and not attempted.
* Deep `let`/`ite` chains or huge coefficients may hit the encoder gates
  before the ICP runs.

## Semantic decisions (2026-09 optimization round)

Three defects found by benchmarking (`bench/trans`, 20-goal corpus) and
fixed — each pinned by a test or visible in the table below:

1. **Transcendentals stay INLINE (no `$p` purification proxies).**  The
   grammar-driven arith purifier used to replace `(exp (- t))` with a
   fresh `$p0` plus a definition atom.  Since δ-weakening applies per
   atom, a purified definition *chain* doubles the effective δ: the
   published point satisfied the purified form exactly on its δ-edges
   while the original formula was 2δ off (`sin x + cos y = 1` converged
   to `sin(x)−s = −0.001`, `s+cos(y)−c = +0.001`, … — a witness of the
   rewritten problem only).  Transcendental nodes are now arithmetic
   constructors (`purify_arith::is_arith_constructor`), dReal-style:
   one atom stays one atom.
2. **The publication check is EXACT rational arithmetic.**  The witness
   evaluates the published `Rational64` point with exact
   `BigRational` brackets (the `*_rational` enclosures in
   `nixie-math::transcendental`), against the exact weakened bounds
   stored per constraint.  The previous f64 check lost by one ulp at
   boxes that converged exactly onto a δ-edge (measured: 99,974
   identical failed witnesses on the decay-envelope goal).
   Definition-shaped equalities additionally get a point-repair sweep
   that snaps proxy variables to their defining expression, so the full
   δ budget lands on the real constraints.
3. **Pruning bounds carry a few ulps of slack** beyond the exact
   admissible bound (δ+ε pruning).  This is sound for `unsat` — the
   ε-larger weakened problem contains the δ-weakened one, so emptying
   the larger still empties the smaller — while the exact witness keeps
   demanding the true δ.

Also fixed on the way: a 1-ulp interval can no longer be branched on
(the bisect midpoint rounds to an endpoint, so the "other half" equals
the parent — an infinite dive), and a branch that runs out of
branchable variables now backtracks into its deferred sibling instead
of aborting the whole solve with `unknown`.

### Corpus results (release build, this machine, Z3 4.16.0)

25 goals, `bench/trans/corpus/`: nixie decides **25/25** (14 delta-sat
witnesses, 11 refutations) in ≤ 131 ms each; Z3 decides **0/25** —
`unknown` on every sin/cos/atan goal it accepts, and it has no
`exp`/`log`/`sqrt` on Reals at all (parse error).  Full table:
`precompile/<sha>/benchmark/trans/*.tsv`.  Headline moves from the
optimization round: coupled `sin x + cos y = 1` 729 ms→17 ms *and*
unknown→delta-sat; the decay envelope 554 ms→98 ms→35 ms and unknown→
delta-sat; the far-window periodic root (`sin x = 0.5` on `[90,100]`)
303 ms→53 ms via the periodic-aware first split; bounded Pythagorean
refutation 41 ms→19 ms.  The fragment round (2026-09-23) added the
UF-congruence, `distinct` and nested-trans goals (t21–t25) — classes
that were honest-`unknown` before it.

## Options

* `(set-option :delta <rational>)` — the δ (default `0.001`, dReal's).
  A larger δ widens what counts as δ-satisfiable; `unsat` answers are
  sound for every δ ≥ 0.
* `(set-option :trans-max-branches <uint>)` — branch-node budget
  (default `100000`). Exhaustion answers `unknown`, never a guess.
* `(set-option :trans-max-propagations <uint>)` — propagation-step budget
  (default `8000000`).

## Numeric hygiene

The witness values are `Rational64` midpoints, converted back through the
rigorous interval layer and **re-verified** before publication — the
`((x (/ n d)))` a `delta-sat` prints is exactly the point that was checked.
No floating-point value is ever printed as a model component without that
round-trip.

## Where the code lives

| Piece | File |
|---|---|
| Rigorous interval enclosures (exp/log/sin/cos/atan/sqrt/asin) | `nixie-math/src/transcendental.rs` |
| ICP engine (propagation, contraction, branching, δ) | `nixie-theories/src/trans/mod.rs` |
| dPLL dispatch (Tseitin over atoms, blocking clauses, model) | `nixie-solver/src/solver/check_trans.rs` |
| `QF_NRT` + capability classification | `nixie-solver/src/solver/logic_contract.rs` |
| Parser surface (`exp` `log` `sin` `cos` `atan` `sqrt`) | `nixie-core/src/smtlib/parser/build.rs` |
| Integration tests | `nixie-solver/tests/trans_delta_icp.rs` |
