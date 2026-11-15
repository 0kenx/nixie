# QF_BV term-rule port + the And-fold soundness bug it exposed (2026-11-15, HEAD `2382fdec`)

**Context:** the open item was "AIG structural hashing in the bit-blaster —
BBB-32 spends 27 s where z3 takes 0.03 s".  This session decomposed that gap
end-to-end, ported the two z3 term rules the miter class needs, found and
fixed a real false-`unsat` in the shipped cascade the port exposed, and
re-measured everything on the fixed base.

## 1. The BBB-32 gap decomposition (the diagnosis was incomplete)

At current HEAD (lean-BV v2), BBB-32 unified runs ~3.4 s (z3 0.037 s), not
27 s (that was the eager path pre-lean-BV).  Decomposition:

| leg | measurement |
|---|---|
| nixie SAT core on **z3's full-pipeline CNF** (59 079 v / 99 370 c) | **0.045 s** (kissat 0.028, z3-sat 0.06) |
| nixie blast of the same instance | 185–220k vars / 491–615k clauses |
| z3 blast after its `simplify` | 73k v / 142k c; unsimplified blast 118k/387k |
| SAT-core BVE on our encoding | 10 M resolutions, 83–90k vars eliminated, search counters bit-identical with BVE off — a time wash |
| our search over our encoding | 366k decisions / 4.7k conflicts for a trivially-`sat` instance |

**The SAT core and inprocessing are exonerated.  The whole class gap is the
bit-blast encoding** (3.8× clauses, 2.5× vars vs z3's post-simplify blast),
plus z3's post-blast `simplify + solve-eqs + aig` sharing passes that we do
not have.  `:sat-mk-var 1` in z3's stats is a psat-wrapper artifact — the
SAT solver does get the big CNF and solves it in ~0.01 s.

z3's term-level simplifier kills exactly the two shapes the miter is made
of (verified on the preprocessed goals: 0 `bvult`/`bvsub` remain):

* `0 <u x − y` → `¬(x − y = 0)` (our `bounds_ult` already does this) then
  **`isolate_term`** (`bv_rewriter.cpp:2779`): `t1 + t2 = c → t1 = c − t2`
  turns `(x − y) = 0` into the plain equality `x = y` (~10× cheaper to
  blast: XNOR+reduction vs subtractor+comparator);
* **`bv_le2extract`** (default-on in z3): a constant operand with its top
  set bit below the width splits `≤u` into a high-part-zero equality plus a
  low-part compare (kills the `c <u X` bounds atoms).

## 2. The port found a real soundness bug (landed as `2382fdec`)

The `isolate_term` re-entry re-rewrote already-rewritten children (memo
*values* are not memo *keys*), which double-rewrote the mask chains — and
the **`flatten_bitwise` And arm folded two chain constants with
`(acc * v) % modulus` (multiplication!) instead of `acc & v`**.  The product
only coincides with the conjunction when a constant is 0 or all-ones, so
`(bvand #x00ffffff (bvand #xff00ffff x))` folded to mask `0x00ff0001`
instead of `0x0000ffff`.  Reachable by *any* second rewrite of a pass-1
output (pass 1's `bvor 0` elimination creates the adjacent-`bvand` nesting
the fold needs).  Reproduced standalone as a false `unsat` (z3: `sat`) on
the **landed baseline binary**, independent of the new rules:

```
(declare-fun x () (_ BitVec 32))
(assert (= (bvand #x00ffffff (bvand #xff00ffff x)) #x00000021))  ; sat
```

Found via the stratified-sample wrong-verdict check on
`stp_samples/run_03230.trace.cond_025442_0x41821d_00.smt2`, ddmin'd to a
single conjunct.  Fix: `acc & v`; siblings audited (`|`, `^`,
`mask − value` — all correct).  Regressions: the standalone shape, an
exhaustive 4-bit mask-pair property (256 pairs), the corpus instance.
Verification: full 12 803-test suite, parity 171/0/6, perf gate PASS,
randomized differential fuzz (~900 atoms, widths 3/4/8, equalities and
comparisons, cascade dump vs z3 oracle — the fuzzer that would have caught
this class pre-landing; keep `/tmp`-style recipes: dump via
`NIXIE_BV_DUMP_PRE`, delete the dump file before every run — stale dumps
produced false positives twice).

**Bonus:** the fix moved the 170-sample from 143 → **145 solved, zero wrong
verdicts** (the corrupted masks were costing solves).

## 3. The port itself: measured wash — NOT landed

With the And-fix in both arms (stratified 170-sample, 10 s cap, seed
20261115, z3 oracle):

| arm | solved | wrong | median time ratio | p90 |
|---|---|---|---|---|
| `2382fdec` (fix only) | 145/170 | 0 | 1.0 | — |
| + isolate/le2x/ultcore | 145/170 | 0 | 1.0 | 1.2 |

Zero solve flips.  BBB-32 (single instance, trajectory-chaotic): plain
~10 s both arms; IR mode 2.4 s without the rules vs **4.4 s with them**
(the split atoms hurt the IR layer's sharing).  The rules are z3-parity
correct (fuzzed clean) but our pipeline has no blast-level consumer that
profits from the term shapes: z3's win comes from the *shared hash-consed
blast + post-blast solve-eqs + AIG* consuming those shapes, which is the
architectural piece we lack.  Reverted by inverse edit; the exact port is
in git history inside this study's session (also preserved below).

## 4. Redirected precondition for the class (item #1 update)

The lever is **not** more term rewrites.  Ranked by measured headroom:

1. **Blast-level structural sharing**: z3's blast builds circuits over the
   hash-consed expr DAG (identical gates intern once) and then runs
   `solve-eqs` + `aig` on the blasted form.  Our blast Tseitin-encodes
   fresh vars per gate (gate-SH maps default-off; IR mode = the analog,
   net-negative on the 509-corpus in 2026-09 but never re-screened after
   lean-BV v2 + the And-fix — IR is 2.4 s vs 10 s plain on BBB-32 now).
2. If a blast-sharing path lands, **re-arm the isolate/le2extract port**
   (the term shapes it produces are what the sharing layer consumes; on
   BBB-32 alone the miter equalities are ~10× cheaper blasted).

Port recipe (for the re-arm): `isolate_eq` operates on the monomial view
with `bvsub` destructured (`eq_sum_monomials`, sign-carrying worklist),
cancels, requires one pure-constant side and ≥2 monomials on the other,
isolates the first monomial (a `−1·u` first monomial isolates the rest),
rebuilds the moved side negated **in the monomial domain** (never emit a
`bvsub`; never re-enter `rewrite` — memo values are not keys, the re-entry
double-rewrites; that is how the And bug was reached).  `le2extract`:
const-rhs `a ≤u b → a[w−1:lnz+1]=0 ∧ a[lnz:0] ≤u b[lnz:0]`, const-lhs the
implies form; route `bvult` through `¬(b ≤u a)` first (z3 `mk_ult`).

## Session data

Sample: seed 20261115, 17/family × 10 families = 170 (list at
`/tmp/qfbv165.txt`, not archived — regenerating with the same seed
reproduces it).  z3 verdicts: 94 unsat / 53 sat / 14 unknown / 9 timeout.
