# A wrong `sat`: an array index equal only by arithmetic

**Status:** open, found 2026-09-14. **This is a wrong `sat`** — the class
`AGENTS.md` opens with. Reproducer and controls are checked in as
`nixie-solver/tests/array_arith_combination.rs`; the failing one is `#[ignore]`d
so the build stays green, and turning it on is the fix's acceptance test.

## The reproducer

```rust
n0 = 0
n1 = n0 + 1
(select (store base 1 7) n1) = 2
```

`n1` is `1`, so the read is `7`, so this is **unsatisfiable**. The solver
answers **`Sat`**.

## What is not wrong

Three controls, all passing, all in the same file:

| given | verdict |
|---|---|
| `n1 = 1` directly | `Unsat` — correct |
| `n1 = n0`, `n0 = 1` (an EUF chain) | `Unsat` — correct |
| `n0 = 0`, `n1 = n0 + 1`, `n1 # 1` (no array) | `Unsat` — correct |

So the array theory reads over writes correctly, EUF closes equality chains
correctly, and the arithmetic solver refutes the disequality correctly. What
fails is only the **combination**: an index equality that nothing but
arithmetic entails.

## Where it comes from

`instantiate_array_axioms` does the right thing structurally. For a read over a
store chain it emits the flat read-over-write encoding — for each store index
`ki`, `(index = ki) => select = vi`, plus an else clause — so the atom
`n1 = 1` *exists*. The SAT solver may set it false; the arithmetic solver
should then refute `n0 = 0 /\ n1 = n0 + 1 /\ n1 # 1`, and does when that
disequality is asserted directly (control 3). It does not when the disequality
arrives as a lemma-minted atom.

**Tried and did not fix it:** calling `track_theory_vars` on the lemma before
`self.encode(inst, manager)` in `array_axioms.rs`. The terms get theory
variables; the atom still is not refuted. So the missing step is not variable
interning but whatever registers an equality *atom* as an arithmetic
constraint — `parse_arith_comparison` and the `var_to_constraint` table that
`build_model` also reads. A lemma-minted comparison appears not to reach it.

That is where to look, and it is one layer past where this investigation
stopped.

## How it surfaced

Not from the corpus. From this, which is as ordinary as TLA+ gets:

```tla
VARIABLES n, s
f[k \in 0..3] == IF k <= 0 THEN 0 ELSE 1
Init == n = 0 /\ s = f[n]
Next == n' = n + 1 /\ s' = f[n']
Inv  == s < 100
```

A function read at a state variable's value. It has no counterexample and is
reported as violated at step 1, with `s = 2` in a state where `f[1]` is `1`.
`f[0]` and `f[1]` — literal indices — are fine; `f[n]` is not.

It was caught by the **trace replay** in `nixie-tla-check`, which decodes a
reported counterexample and re-checks it with `nixie-tla`'s evaluator: the
harness reports it as *decoded but did not replay* rather than counting it as a
violation. The bounded check's direction turns this into a false *violation*
rather than a missed bug, so `NoViolationWithin` is not affected — but a user
is told their specification is broken when it is not.

Two specifications in the 905-module corpus hit it today, `Rec3.tla` among
them, and both are surfaced as unverified rather than silently counted.

## Why it was not fixed here

It is a theory-combination defect in a part of `nixie-solver` this
investigation had not worked in, and the obvious one-line hypothesis was tested
and refuted. Guessing again at the encode-to-theory-atom pipeline risks
breaking the array and arithmetic families to fix a bug that is, for now,
contained and visible. The reproducer is four lines; the controls say exactly
which three mechanisms are innocent.
