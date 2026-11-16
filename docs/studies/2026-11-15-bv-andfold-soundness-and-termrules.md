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

**Erratum (process, corrected same session):** the A/B initially recorded
here ran with the port accidentally active in *both* arms — after the
soundness commit I restored the rules file and rebuilt before re-running,
then inverse-edited the source without rebuilding, so the "base" binary
(and, worse, the `precompile/2382fdec` cache entry) carried the rules.
The cache entry has been rebuilt from the true HEAD; the corrected A/B
numbers below are from the verified arms (dump-probe confirms the base
leaves `(bvult x #x00000041)` unsplit, the port splits it):

| arm | solved | wrong | flips vs base | median time ratio | p90 |
|---|---|---|---|---|---|
| `2382fdec` (And-fix only, verified) | 145/170 | 0 | — | 1.0 | — |
| + isolate/le2x/ultcore | 145/170 | 0 | +2/−2 | 1.0 | 1.5 |
| same port on a 150-instance miter screen (tacas07, BuchwaldFried, Goel, brummayerbiere×3, Wolf, bmc-bv) | 88/150 | 0 | **0** | 1.0 | 1.5 |

The 170-sample flips are two boundary-cap gains (Sage2) against two
boundary-cap losses (uclid convert-jpg2gif, sage) — churn, not signal.
The miter screen — the port's design target — shows **zero** effect:
the term shapes our blaster receives are not the bottleneck there
either.  BBB-32 (single instance, trajectory-chaotic): plain ~10 s both
arms; IR mode 2.4 s without the rules vs 4.4 s with them.  The rules
are z3-parity correct (fuzzed clean) but our pipeline has no
blast-level consumer that profits from the term shapes: z3's win comes
from the *shared hash-consed blast + post-blast solve-eqs + AIG*
consuming those shapes, which is the architectural piece we lack.
Reverted by inverse edit; the exact port is preserved below.

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

## Addendum (same day): the IR re-screen — decisively negative, default stays off

The redirected precondition's first probe (re-screen `NIXIE_BV_IR=1`
after lean-BV v2 + the And-fix, never done since the 2026-09 −16
verdict): **120/170 vs 143/170 (net −23), zero wrong verdicts** (both
arms of this comparison ran the erratum's rules binary — the IR
on/off contrast is internally consistent; the rules cost ~2 cells
net, so vs the true base the gap is ≥ 21 either way).
`uclid` collapses 16 → 2 (the macro-heavy catchconv/convert-jpg2gif
meganodes), `spear` 17 → 12, `Sydr` 13 → 10; wins are bruttomesso +1,
lfsr, one Sage2 cell.  The 2026-09 verdict not only stands, it
sharpens: the deferred Tseitin pays only on the structural-miter
minority and costs the macro/megabyte majority far more.  BBB-32's
IR 2.4 s vs 10 s plain is a single-instance trajectory, not class
evidence.  Do not re-screen IR globally again without a *per-class*
gate that excludes meganode-heavy inputs (the 2026-09 gate study found
no blast-time separator; the family-level split here suggests the
separator, if any, lives at parse/cascade time — e.g. meganode-skip
counters, not IR activity stats).


## Second addendum (same day): `NIXIE_BV_GATE_SH` screened as a default — LANDED (`254d79bf`)

The eager-sharing arm that differs from IR's deferred-Tseitin design:
blast-time hash-consing of identical gate nodes (one shared SAT var per
distinct and/or/xor over the same operand pair).  Screened on both
corpora with the corrected base:

| screen | base | GATE_SH=1 | wrong |
|---|---|---|---|
| 170-sample | 145 | **149** (+4, all Sage2) | 0 |
| miter-150 (tacas07, BuchwaldFried, Goel, brummayerbiere×3, Wolf, bmc-bv) | 88 | **91** (+3: smulov2bw048/064, minand032) | 0 |

Zero losses on both.  The four Sage2 crossings re-verified at a 25 s
cap as deterministic 1.7–6× speedups (bench_2947 14.1→3.0 s,
bench_7099 >25→4.0 s), not boundary wobble; the miter gains include
the historically `GATE_SH`-closed cells (2026-09 round-6 notes), so
the flip also subsumes those opt-ins.  Median +3.7 % on
already-decided cells (the map probe), p90 1.5.  Landed default-on
with `NIXIE_BV_GATE_SH=0` as the opt-out; scope-safety argument in the
commit; full bar green (12 805 tests, parity 171/0/6, perf gate
counter-identical).

Net session effect on the two screens: **145→149 and 88→91 solved at
the default**, plus the false-`unsat` And-fold fix.


## Third addendum (same day): the strength reductions moved to the blast layer — LANDED (`73e9c641`)

A blast-size instrument (`NIXIE_BV_BLAST_STATS=trace`, one stderr line per
encoded operator: op/width/var-delta) attributed BBB-32's blast: **366
`BvSub` × ~210 vars = 92 %** of the word-op budget.  Every miter atom
spelled `(bvsub X Y)` built a subtractor + comparator.

Two attempts at the fix, with the architectural lesson between them:

1. **Term-level `isolate_eq` re-armed (sub-aware monomial view, the §4
   recipe verbatim): works on the eager route, REGRESSES the unified
   route catastrophically** — `sage/app12/bench_4186` 0.21 s → 19–32 s.
   Root cause: the unified path blasts at *assert* time on original
   terms, and the check-time "preprocessing-parity pass" asserts the
   cascade's rewrites **alongside** the originals — the isolated
   equalities double the atom coverage instead of replacing it.
   Bisected all four pieces (census, both atom specializations,
   ult_gate consts) before isolating the term rule as the sole cause.
   Removed; the recipe stays in §4 for the eager route only.
2. **Blast-layer specializations (landed)**: `(x−y)=0` → `x=y` (XNOR+
   reduction), `0 <u (x−y)` → `x≠y`, `(x−y) <u 0` → false, `≤u` duals;
   a per-reference census in the unified collectors skips blasting a
   subtractor whose every reference is specializable; `ult_gate` folds
   constant-side comparators (`0 <u b` = negated all-zero reduction,
   `a <u MAX` = negated AND-reduction, `a <u 0` = false).

Measured: BBB-32 blast 185k → **114k vars (−38 %)**, solve ~10 s →
**6.5 s**; miter-150 **89 → 91** (rfunit_flat-64 timeout→sat 5.9 s,
bitrev1024 timeout→unsat), zero losses/wrong; 170-sample 148 → 147
(one 5.5 s→cap boundary cell, median 1.0); GATE_SH wins intact;
934-atom differential fuzz clean (widths 3/4/8/16); full bar green.


## Fourth addendum: the completed encoding-budget class map (`51b9044d`)

The atom-level attribution completes the instrument.  Where the
remaining QF_BV encoding gap lives, per class, after the landed
slices (And-fix, GATE_SH, miter/const reductions):

* **BBB-32-class (tacas07 miters)**: blast 114k vars vs z3's 59k.
  Comparisons (AtomUle+AtomUlt ≈ 54k) are var-vs-var and already
  share through GATE_SH; the **add/sub pointer chains (≈49k)** —
  `bvadd(x, bvsub(S, x))`-class algebra the cascade collapses to `S`
  — are built verbatim because the unified route blasts originals at
  assert time.  Precondition recorded: **blast the cascade output**
  (the `NIXIE_BV_DEFER_BLAST` architecture, prototyped 2026-09) or
  replicate the monomial cancellation at the blast walk.
* **asp-class (gryzzles, DL-as-BV)**: 621 `(x − y) = c` 4-bit
  difference atoms; z3's `simplify` eliminates every `bvsub`
  (isolate-term class), leaving plain var-var comparisons, 46k
  vars / 84k clauses vs our 61k/171k.  Our SAT core solves z3's CNF
  for gryzzles.8 in 0.032 s — the class gap is encoding + the
  CDCL(T) wrapper (2.4 M theory_props), not search.  Precondition:
  the DL-recognition / theory_i_arith item (weeks-scale), or a fused
  `(x−y)=c` increment-compare specialization (est. ~30 % circuit,
  class-narrow — not pursued this session).
* Const-side `c <u X` splits (z3 `le2extract` as a circuit) measured
  as the wrong target on BBB-32: its remaining comparisons are
  var-vs-var.


## Fifth addendum: the deferral re-screened on the current base — net negative, stays opt-in

`NIXIE_BV_DEFER_BLAST=1` (landed machinery, default off) re-screened
after the strength reductions, on the corrected arms:

* BBB-32: **2.2 s → 0.44 s (5×)** — blasting the cascade output
  collapses the pointer chains exactly as the class map predicted;
  the old false-`sat` family (`s3_clnt_*`) is z3-consistent (the
  `dfa1c754` budget fix cured it).
* But the screens: 170-sample **148 → 146 with three `sat → unknown`
  degradations** (spear nnrpd/innd — the 2026-09 "model-path holes":
  the honesty gate catches weakened rewritten sets and degrades
  honestly); miter-150 **92 → 88** (Wolf zipcpu ×2, minand032,
  smulov4bw ×2 lost, nlzbe gained); p90 2.0 on both.

Net −6 solves across 320 for one 5× class win: **not a default**.
The precondition it leaves: capture the pointer-chain collapse
*inside the assert-time blast* — a monomial-cancellation pass over
the collected `bv_sorted` before `encode_bv_term_recursive` runs
(same algebra as `cancel_monomials`, applied at the walk's
operand set) — so the raw emission never happens and no
deferral/equisatisfiability exposure exists.  That is the item's
next concrete slice.


## Sixth addendum: blast-time monomial cancellation — built, measured, reverted

The fifth addendum's precondition was implemented exactly as recorded:
`cancel_sum_term` (sub-aware monomial view over the collected
`bv_sorted`, strictly-shrinking guard, residual aliasing via
`alias_bv_bits`) running before the unified pass's blast loop — the
deferral's pointer-chain collapse with zero deferral exposure.

Two findings, then a negative:

1. **Guard subtlety**: `combine_like` folds duplicate monomials
   (`x + x → 2x`), which passes a naive length-shrink guard without
   any cross-side cancellation — the "residual" is then a full
   reassociated rebuild that un-shares the DAG (bench_4186 exploded
   to 5.8 M SAT vars via per-link-pass re-blasts before the
   distinct-key guard fixed it).
2. **The idiom misattribution**: BBB-32's add/sub pointer chains
   exist only in the *cascade output* — the original file has no
   `bvadd` at all (its subs feed extract/mask chains only the full
   cascade folds).  The cancellation therefore left BBB-32's blast
   untouched (114k vars both arms); it targeted the SAGE originals
   (`bvadd(x, bvsub(S, x))` verbatim) — whose solves were already
   fast and did not flip.

Screens: 170-sample 148 → 147, miter 92 → 91 — net −2 (two
7 s→cap boundary cells), zero gains, zero wrong verdicts, median
1.009.  **Reverted** (tree byte-identical to `51b9044d`).  The
BBB-32-class collapse requires the *whole* cascade rewrite before
the blast — that is the deferral (net −6, fifth addendum) or a
future routing change, not a local algebraic pass.  The class item's
remaining recorded headroom stands as: defer-blast behind a
per-class gate, or nothing on this route.


## Seventh addendum: lean-BV v3 — the BoolApp truth-node gate — LANDED (`0ef7d9c7`)

The asp-class profile (gryzzles.8, pprof sync harness, FP build) put
**35–42 % of the solve inside `EufSolver::merge → congruence::propagate`**
hash probes.  Root cause: every assigned BV comparison atom is a
`Constraint::BoolApp`, and that branch interned the whole comparison
term into EUF and merged it into the canonical truth nodes — on every
assignment, for every atom.  The lean-BV v1/v2 gates covered Eq/Diseq;
this channel was untouched.

In exactly-QF_BV no UF/select can appear, so no congruence over these
nodes can ever fire — the walk re-decides what the bit-blast owns.
The v3 gate returns early under the same declared-logic envelope as
v1/v2.

Measured: gryzzles.8 profile 1 107 → 605 samples (EUF frames vanish);
**the full asp family (496 files, 10 s cap, 8-way): 74 → 94 decided
(+20 net: 24 gains — rand/maze cells z3 cannot decide — against 3
trajectory losses), median 0.879 on both-decided, zero wrong
verdicts** (every z3-decided flip matches; the self-annotated
`_sat`/`_unsat` filenames all consistent).  Screens: 170-sample
147 → 148, miter 91 → 90 (one 9.9→10.04 boundary cell).  554-atom
differential fuzz clean; full bar green (12 807 tests, parity
171/0/6, perf gate counters 1.000 / wall 0.96).
