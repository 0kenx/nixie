# A wrong `sat`: an array index arithmetic entails equal to a constant one

**Status:** **closed** 2026-09-14. Reproducer and controls:
`nixie-solver/tests/array_index_entailed_equal.rs`.

This is the *second* wrong `sat` behind Apalache's `Rec3.tla`, and it is a
different defect from
[`2026-09-14-array-index-equality-from-arithmetic.md`](2026-09-14-array-index-equality-from-arithmetic.md).
That one was fixed first; `Rec3.tla` kept failing, which is how this one was
found.

## The reproducer

```
select(A, 0) = 0
select(A, 1) = 1
n0 = 0,  n = n0 + 1
select(A, n) = 5
```

`n` is `1`, so congruence gives `select(A, n) = select(A, 1) = 1`, so this is
**unsatisfiable**. The solver answered **`Sat`**.

Two controls in the same file:

| given | verdict |
|---|---|
| `n = 1` **directly** | `Unsat` — correct, congruence alone decides it |
| `n = n0 + 2` (index `2`, unconstrained) | `Sat` — correct, and the guard against a blanket refutation |

## Why it is not the previous bug

There is **no store**. Nothing mints an index-equality atom, so no trichotomy
clause can exist to be missing — the previous fix cannot reach this shape. The
gap is one step earlier, in what the theory-combination probe is allowed to
*consider*.

`nelson_oppen_combine`'s arithmetic → EUF direction proposes a pair `(a, b)`
for an entailed-equality probe when both are EUF **application arguments**
(`euf.app_argument_terms()`) and both are arithmetic **interface terms**
(`arith.interface_terms()`). `n` is both. The constant `1` is an application
argument — `select(A, 1)` is interned for congruence — but it was never an
arithmetic interface term, so the pair `(n, 1)` was never proposed,
`entailed_equal_reason` was never asked, EUF never merged them, and the
congruence `select(A, n) = select(A, 1)` never fired.

This is exactly the `pr30#3` class, one theory over. The fix for that one
lives in `purify_numeric_uf_args`: constant numeric arguments of an
un-purified `Apply` are *pinned* into arithmetic as interface terms fixed to
their literal value. That walk handles `TermKind::Apply` and walks straight
past `TermKind::Select` and `TermKind::Store`.

## The fix

Give the same walk a `Select`/`Store` arm: a constant numeric **index** is
pinned into arithmetic as an interface term.

Pinned, not purified — deliberately. The array theory matches store and select
indices by `TermId` (`direct_store_map`, `row_same_guard`,
`build_read_over_write`'s `entries.iter().any(|(ki, _)| *ki == index)`), so
substituting a proxy variable for a constant index would silently change which
writes a read is judged to alias. The pin is the tautological row `c = c`: it
constrains nothing, and its only effect is to make the constant visible to the
interface-equality machinery.

Soundness of the pin is unchanged from the `Apply` case — see
`pin_quantified_uf_const_arg`: the row can never be violated, its reason tag
names no literal and is recorded as an empty `DerivedReasons` explanation, and
the merge it enables is re-verified by `entailed_equal_reason`'s two
feasibility checks, so it is a deduction rather than a guess and cannot cause
a false `unsat`.

## How it surfaced

Apalache's `Rec3.tla` computes Fibonacci twice — iteratively and with a
recursive function over `0..15` — and asserts the two agree. It has no
counterexample. Nixie reported one at step 1, with

```
n = 1,  fibComp = 1,  fibCompPrev = 0,  fibSpec = 2
```

i.e. `Fib[1] = 2`. The recursive-function encoding is an array plus one
equation per domain point (`select(@recfun_Fib_0, k) = …` for each ground
`k`), and the read is at the *state variable* `n'`. With `n' = 1` reachable
only through arithmetic, no equation ever applied to the read, and `Fib[n']`
floated free — the trace shows it taking whatever value the invariant needed.

Reduced further: `Inv == s < 1000` on the same shape produced `s = 1000`,
which is the clearest possible statement that the read was unconstrained.

`Fib` at *literal* indices (`Fib[1] = 1 /\ Fib[2] = 1 /\ Fib[3] = 2 /\ …`) was
always correct, which is what localises the defect to the variable index.

After the fix, `Rec3.tla` reports **no counterexample of 3 step(s) or fewer**.

## A correction to the previous study

`2026-09-14-array-index-equality-from-arithmetic.md` said two corpus
specifications hit that defect, "`Rec3.tla` among them". The corpus re-run
after that fix landed showed `Rec3.tla` still failing, so that attribution was
wrong: `Rec3` exercises *this* defect. The two are genuinely distinct — one
needs a store to mint the index atom, the other needs no store at all — and
the minimal reproducer used for the first fix (a non-recursive `f[k] == IF k
<= 0 THEN 0 ELSE 1` read at a variable) really did rest on the trichotomy gap.
The corrected claim is in that study's own text.
