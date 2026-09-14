# A wrong `sat`: an array index equal only by arithmetic

**Status:** **closed** 2026-09-14. Found and fixed the same day. The reproducer
and its three controls are `nixie-solver/tests/array_arith_combination.rs`
(the first is no longer `#[ignore]`d); the structural guard is
`solver::tests::every_numeric_equality_atom_carries_its_trichotomy`.

## The reproducer

```
n0 = 0
n1 = n0 + 1
(select (store base 1 7) n1) = 2
```

`n1` is `1`, so the read is `7`, so this is **unsatisfiable**. The solver
answered **`Sat`**, with a model that states the contradiction outright:
`n0 = 0`, `n1 = 1`, `select(store(base, 1, 7), n1) = 2`.

## What was not wrong

Three controls, all passing before the fix and after, all in the same file:

| given | verdict |
|---|---|
| `n1 = 1` directly | `Unsat` — correct |
| `n1 = n0`, `n0 = 1` (an EUF chain) | `Unsat` — correct |
| `n0 = 0`, `n1 = n0 + 1`, `n1 # 1` (no array) | `Unsat` — correct |

The array theory reads over writes correctly, EUF closes equality chains
correctly, and the arithmetic solver refutes the disequality correctly. Only
the **combination** failed — an index equality that nothing but arithmetic
entails.

## The root cause

`instantiate_array_axioms` did emit the right lemma. For `select(store(base,
1, 7), n1)` it asserts the flat read-over-write encoding

```
(=> (= n1 1) (= (select (store base 1 7) n1) 7))
(or (= (select (store base 1 7) n1) (select base n1)) (= n1 1))
```

so the atom `(= n1 1)` exists, gets a SAT variable, gets its
`Constraint::Eq(n1, 1)`, and gets a parsed linear form. All of that was
already true. What it did **not** get is a **trichotomy clause**.

The trichotomy `(a = b) ∨ (a < b) ∨ (a > b)` is the *only* channel by which a
numeric disequality reaches the tableau. `process_constraint`'s negative-`Eq`
branch tells EUF and the bit-vector solver and stops there — and it must, the
simplex has no `≠`. With the clause present, a `false` equality atom unit-
propagates into a strict bound; without it, arithmetic never hears about the
atom at all and the tableau stays free to give `n1` the value `1` while the
Boolean level believes `n1 ≠ 1`.

`Solver::ensure_numeric_equality_splits` establishes that clause for every
numeric equality in the **assertion spine**, at the top of every `check`. It
walks `self.assertions`. A lemma-minted atom is in no assertion, so the walk
structurally cannot see it — and array axioms are asserted as SAT clauses, not
as assertions.

**The confirming measurement**, before any fix: adding the tautology
`(or (= 1 n1) (not (= 1 n1)))` to the input — which changes nothing
semantically but puts the atom in the spine — turned the same goal `Unsat`.

## The fix

`nixie-solver`: make the trichotomy an invariant of *encoding* a numeric
equality atom rather than a property of the assertion walk.

* The `Eq` arm of the encoder queues `(lhs, rhs)` in
  `Solver::pending_numeric_eq_splits` whenever it mints a numeric equality
  atom while `solving` is set.
* `encode_depth` drains the queue at `depth == 0` — every *top-level* entry
  into the encoder, which is `encode` plus the handful of lemma emitters that
  call `encode_depth(.., 0)` directly — so the clause exists before the caller
  adds the clause that will use the atom.
* Assertion-time atoms are left to `ensure_numeric_equality_splits`, so the
  clause order on input-only problems is unchanged.

The invariant is pinned by
`every_numeric_equality_atom_carries_its_trichotomy`, which scans
`var_to_constraint` after a check and fails if any numeric `Eq` atom's pair is
missing from `numeric_eq_split_pairs`. Without the fix it fails naming three
pairs.

## The layers checked, and what each one turned up

Per `AGENTS.md` #2, fixing one layer proves nothing about the others.

1. **`ensure_numeric_equality_splits`** — spine-only. *The root cause.* Fixed.
2. **`process_constraint`, negative `Eq`** — informs EUF and BV, never
   arithmetic. Correct as written (the simplex has no `≠`); the trichotomy is
   the channel. Now says so in a comment, so the next reader does not
   re-derive it from a wrong `sat`.
3. **`refine_arrangement_splits`** — mints `(= a b)` care-split atoms with no
   trichotomy: **a second, independent instance of the same defect**, in a
   non-array path. Closed by the same fix.
4. **`repair_congruence_gap`** and the store-congruence premise pairs in
   `instantiate_array_axioms` — both already called
   `emit_collision_trichotomy` explicitly. They were right; they were also the
   evidence that this hazard was known one call site at a time rather than as
   an invariant.
5. **`add_arith_eq_trichotomy`** (MBQI) — gated to `Apply` operands, with a
   comment claiming `Select` terms are "handled by the array theory". That
   claim is false and is exactly what this bug rested on: the array theory
   mints the index equality, it does not give it arithmetic meaning. The gate
   is no longer load-bearing (the encoder covers those atoms now) and is left
   as written so MBQI's clause order does not move; the comment is corrected.
6. **`Constraint::Diseq`** (from `Distinct`) — same no-arith shape, but no
   lemma emitter mints a `Distinct`; every one comes from the spine, where
   `add_arith_diseq_split` covers it. No defect.

## Verification

* `cargo nextest run --workspace --all-features` — **11 669 passed, 0 failed**.
* `./bench/z3_parity/run_parity.sh` with z3 **4.16.0** — 177 benchmarks,
  **100.0 % parity, 0 mismatches**; the recorded per-environment verdicts are
  unchanged.
* End to end, the TLA+ shape this came from:

  ```tla
  VARIABLES n, s
  f[k \in 0..3] == IF k <= 0 THEN 0 ELSE 1
  Init == n = 0 /\ s = f[n]      Next == n' = n + 1 /\ s' = f[n']
  Inv  == s < 100
  ```

  before: `counterexample 1: 1 step(s)` / *does not replay*.
  after: `no counterexample of 3 step(s) or fewer`.

## The cost, stated honestly

`pete_5s` (QF_UFIDL, `arrangement_round_regressions`) still answers `unsat`,
and gets **≈5.5× slower**: 3.16 / 3.16 / 3.35 s at the parent commit against
17.61 / 17.63 / 18.29 s with the fix (debug build, n = 3 each, settled load,
same checkout). Wall clock is a *reported* cost here, never a policy input;
an earlier single reading of 31.8 s was taken while the machine was building
under other agents and is discarded.

The cause is *not* clause volume: the instance gains **101** trichotomy
clauses over its whole run. It is the 202 new `lt`/`gt` atoms, which arrive
with no phase guidance and are free decision fodder — the same shape the
injective-map A-family suppression was introduced for ("each free
comparator-ish atom conflicts only at final_check, one arrangement per full
re-descent").

This is a soundness fix, so the matched-null rule does not gate it (a wrong
answer is a bug at n=1). The cost is real and is the follow-up:
`add_arith_trichotomy_clause` already pins a deterministic acyclic orientation
on its `lt`/`gt` atoms, but only under `has_array_ops && plain_vars`.
Extending that hint to lemma-minted pairs is a *heuristic* change and needs
its own matched null and ≥10 seeds per `docs/BENCHMARKING.md` — it is not
bundled here.

## How it surfaced

Not from the corpus. From a function read at a state variable's value, which
is as ordinary as TLA+ gets. It was caught by the **trace replay** in
`nixie-tla-check`: the harness decodes a reported counterexample and re-checks
it with `nixie-tla`'s evaluator, and reported this one as *decoded but did not
replay* rather than counting it as a violation. Two specifications in the
905-module corpus hit it, `Rec3.tla` among them.
