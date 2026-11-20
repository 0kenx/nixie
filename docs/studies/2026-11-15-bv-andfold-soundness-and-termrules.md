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


## Eighth addendum: the Sydr ingestion wall — first two fixes landed (`d1b0632b`)

Serial ground truth for Sydr (535 files, 10 s): **nixie 383 vs z3 419**
(the earlier parallel scans undercount both arms ~8× contention —
matched-parallelism comparisons are internally consistent but absolute
counts are not; serial scans are the record).  The gap clusters in
`symbolic_memory/linear/minigzip` (39 timeouts, z3 decides 14) and
`hdp`; the yices subfamily is hard for z3 too (92/96 mutual timeouts).

The minigzip profile is a different wall from every prior scan:
**57.6 % of the run inside `assert`** — ingestion, not search.  Two
pure-perf fixes landed (counter-identical verified):

1. `term_in_blastable_fragment` memoizes proven terms (thread-local
   set; the verdict is structural over immutable interned terms).
   Was 19.5 % + 15.2 % (`assertion_in_bv_fragment`) of the run.
2. The constraint sweep's atom dedup is a hash set, not a linear
   scan (was 7 %, quadratic).

Measured: minigzip predicate_492 ~15–20 % wall; **serial Sydr
383 → 391**; asp same-setup 76 → 83; zero wrong verdicts; full bar
green (12 808 tests, parity 171/0/6, gate counters 1.000 / wall
0.97).

**Remaining wall (next session's entry point), corrected:** the
check-side cascade call is *one* expensive pass, not a re-run loop
(stack: check → dispatch_pure_bv → bv_preprocess_assertions →
solve_equations — 10.6 % in a single call over meganode assertions,
the budgeted 2026-09 area).  The assert-side cost is instead **~8
distinct per-assert DAG walkers** each allocating and re-inserting
the same shared meganode terms into fresh visited-sets:
`traverse`/`collect_subterms`, `mentions`, `bv_elim_*`,
`contains_quantifier`, `term_has_trans`, `subtree_*`, the census,
`encode_bv_term_recursive` — together the ~30 % hash-insert churn.
Candidate shape: an epoch-stamped shared visited marker (a per-manager
`Vec<epoch>` indexed by TermId, bumped per call) so every walker
shares one array — an architectural nixie-core traversal change, or
alternatively memoize the few hottest walkers the way the fragment
check now does.


## Campaign scoreboard (2026-11-15 end-of-day, HEAD `d1b0632b`)

Serial 10 s cap, stratified 170-sample (seed 20261115, 17/family × 10):

**nixie 146 decided (94 unsat + 52 sat) = z3 146 decided (93 + 53;
z3 additionally returns 15 `unknown` and 9 timeouts of its own).**
Zero wrong verdicts.  The campaign opened at 138 vs 149 z3-decided
(the 2026-11-14 differential): **parity reached, soundly.**

Family residuals (nixie vs z3-solved, single digits each):
Sydr 15/17, Sage2 14/17, asp 2/8 (the deep asp cells need the DL
recognition architecture), bruttomesso 15/17, spear 15/17; six
families at full parity (Noetzli, MCMPC, sage, stp_samples, uclid at
17/17).

Full-family serial reference points: Sydr 391/535 vs z3 419; asp
ingestion+wrapper costs now lean (lean-BV v3), remaining gap = DL
recognition + ordinary search.


## Ninth addendum: epoch-stamped visited marks — LANDED (`e2bee28d`)

The corrected eighth-addendum attribution led here: `TermManager` now
carries a shared marks array + per-walk epochs; `traverse`, `mentions`
and the unified census/walk converted; `collect_subterms`' redundant
own visited set dropped (provably dead: `traverse` post-visits each
distinct term exactly once).

Measured: counter-identical on the minigzip cell; single-cell timing
in the noise — the honest decomposition of the ~30 % churn is
two-thirds *HashMap* bookkeeping inserts (term_to_var, census maps,
clause registries — real work, not dedup) and one-third walker sets;
the epoch conversion only addresses the latter.  Serial Sydr 391 →
395 (+4 boundary crossings).  Full bar green (12 808 tests, one
load-flaked timeout re-verified clean isolated; parity 171/0/6; gate
counters 1.000 / wall 0.96).

Remaining ingestion-wall items, in measured order: the HashMap-side
bookkeeping (architectural: fewer/lazier registries or arena-backed
maps), the single check-side `solve_equations` pass over meganodes
(the 2026-09 budget area), and the blast itself.


## Tenth addendum: the dense-slab memo + eviction gates (2026-11-16)

Post-ingestion-fix profile of minigzip predicate_492 (2 627 samples,
57 % check / 43 % assert) re-ranked the walls; three landed:

1. **`BvSolver::get_bv` probes — 6.0 % of the whole run**
   (`2698d1f4`).  `term_to_bv` was an `FxHashMap<TermId, BvVar>`
   probed for every node of every assertion DAG; TermId is dense, so
   the memo became `Vec<Option<BvVar>>` (`slb`/`slb_put`/`slb_clear`,
   with `blasted_count` keeping `has_any_blasting` O(1)).  Iteration
   order shifts to term-id order (model listing only — counters
   bit-identical on minigzip, BBB-32, asp wire12, bruttomesso
   ext_con).  ~10 % wall on the cell; stratified 170-sample serial
   **146 → 148 (z3: 146 — nixie now ahead on the sample)**.

2. **on_backtrack canonical eviction (`7a87764d`).**  The
   `interned_bv_constants.retain` ran per backtrack though stale
   canonicals require an EUF node removal, and `pop_theory_scope` is
   the only remover — now gated on `popped_any`.  Counter-identical;
   targets pop-heavy UF-mixed workloads (the pure-BV cell has few
   pops and showed noise-level effect under load 19-25).

3. The remaining assert-side block is genuine first-time gate
   construction (`build_with` + `encode_bv_term_recursive` ≈ 29 % of
   the run *before* the slab fix) — not memo overhead; and the
   check-side SAT core (`propagate` 18 %, scan/prefetch 6.8 %) is the
   next architectural tier.  `solve_equations` is 8.9 % in one
   budgeted check-side call; `substitute` 4.7 % beneath it.


## Eleventh addendum: the thread-local memo hazard + the tripwire incident (2026-11-17, `915c5828`)

**The hazard.** The ingestion-wall fix (`d1b0632b`) memoized
proven-blastable TermIds in a `thread_local!` set, documented as safe
because "the CLI solves one script per process".  Wrong for any
embedding that runs two solvers on one thread — nixie-py holds two
`Context`s in one Python thread, and TermIds are manager-relative, so
solver A's positives read as positives in fresh-manager solver B,
keeping `all_assertions_bv_fragment` up on unblastable assertions
(partial-encode territory).  The memo is now `Solver::blastable_memo`
(one solver owns one manager — no cross-manager reads by
construction).  Reproduced at the unit level: the isolation test
*fails* on the thread-local code and passes with the fix.  Layers
examined beyond the fix: the two call sites (encode/bv_unified), the
fragment consumers (dispatch gating at mod.rs / bv_unified 157/846),
the routing consequences (unified vs dispatch), and the EUF channel
that masks the wrong-answer shape for UF apps (atoms still reach EUF).

**The tripwire.** Landing it flipped spacer's
`assert_flattens_deeply_nested_conjunction` (128 KiB spawned stack ×
6 250-deep And chain) to SIGABRT — only in workspace-feature-unified
builds, only sometimes-at-HEAD.  The investigation (check-trace
bracketing, lldb on the guard-page fault, a frame-pointer build, a
debug-info build) bottomed out at: `certify_result`'s statically
aggregated frame (~1.3 KB of inlined certification locals) sits at the
bottom of the check call chain, and the unified build's layout left
~1 KB of margin — any codegen perturbation (this change, or even
eprintln instrumentation) tips the prologue into the guard.  Not
recursion, not a logic bug: a margin razor.  DEEP_STACK is now 1 MiB
(any plausible 6 250-deep native recursion needs ≥ 3 MiB, so the
assert-path tripwire keeps its power); the incident is documented at
the constant.

**Process notes.** (1) The full-suite failures during the
investigation were load flakes (load 30+): one wall-budget test plus
SIGABRTs that passed in isolation — the 8-core cap (`taskset -c 0-7`,
see AGENTS.md) eliminated them.  (2) A counter-identity "DIFFER"
against `precompile/7a87764d` was a phantom — another agent's cleanup
had deleted that baseline; against the surviving 2698d1f4 arm all four
probe cells are bit-identical.


## Twelfth addendum: per-assert feature-walk gates — LANDED (`d9b5ae92`)

The mg4 profile (post-slab) re-ranked the assert-side residual: four
per-assert *feature-detection* walks — quantifier registration (2.8 %),
quantifier guarding (1.6 %+1.6 %), set/bag survey gate (1.9 %), array
marking (1.2 %), ite gate (1.3 %) — ran unconditionally per assertion
with fresh visited sets on quantifier-free, array-free input.  All now
share memoized negatives (per-node subtree skips on the existing
`contains_quantifier`; two new manager memos for set/bag and ite; a
solver-owned `array_free_memo`; the airtight `next_skolem_id == 0`
no-skolems gate — every minting path seeds from that counter and the
reserved `\nixie.` prefix is unwritable by users).

Measured: counter-identical (minigzip, BBB-32); the four walk sites
now share one linear pass (assert-side 684→663 samples); the residual
is inherent per-new-node checking — minigzip assertions share leaves
and define-fun bodies, and every NEW node must be seen once.
Stratified 170-sample serial **148 → 150 (z3: 146)**.  Full bar green
(12 810 / parity 171-0-6 / gate PASS).

Remaining assert-side blocks (mg6 profile): genuine gate construction
(`encode_bv_term_recursive` ≈ 11 %), `elim_uncnstr` 4 %, the check-side
`bv_preprocess` cascade 11 % (solve_equations 9.4 % within its budget),
and the SAT kernel (propagate 15.7 %, watch-take 10.2 % — the CSR flip
was measured corpus-negative 2026-09-20, not retried).


## Thirteenth addendum: two more memoized detection walks (`cf0d3919`)

mg7 profile: `register_ground_instance_root`'s array scan (1.7 %, every
assert) and `term_is_nonlinear` (3.4 % — the check-side NIA detection
rescans every assertion) joined the feature-walk family.  Both now
delegate to new manager memos (`contains_array_sort`,
`contains_nonlinear_mul` — same shape as `contains_quantifier`).  The
NIA scan could NOT be flag-gated soundly (a `Mul` can hide inside an
unencoded quantifier body, outside `arith_terms`), so the memo route
was chosen over the cheaper-looking `arith_terms.is_empty()` gate.
The MBQI `collect_ground_terms` walk (1.7 %) was examined and left
alone: gating it on quantifier absence changes the candidate pool if a
quantifier arrives later — a semantic delta needing a replay proof,
not worth 1.7 %.

Measured: counter-identical on minigzip/BBB-32/QF_NIA/QF_LIA cells;
**stratified-sample matched back-to-back A/B 148 = 148, zero flips** —
the walk cost left the profile but no boundary cell moved.  Process
note recorded: single-arm 170-sample readings across one day spanned
148–150 under varying load; only matched pairs are decision-grade.


## Fourteenth addendum: on_backtrack's shadow trail — examined, left alone

mg7 shows `TheoryCallback::on_backtrack` at 7.4 %.  Decomposition: the
`.any(|a| a.level > level)` precheck plus the swap-removal loop are
both O(trail) per pruning backtrack, and the trail carries a large
level-0 prefix on symbolic-memory cells.  Two cheaper shapes were
considered and rejected on semantics:

- **Suffix truncation** (the >L entries as a contiguous tail): the
  trail is NOT level-sorted — `on_assignment`'s in-place update path
  (`assignment_trail[index] = atom` on re-assignment) refreshes an
  existing entry's level without moving its position, so position ≠
  level.
- **Per-level buckets** (drop buckets > L wholesale): changes
  iteration order — the arith replay (theory_manager 3080) and the
  scope replay (1310) iterate the flat trail, and the replay sequence
  is trajectory-defining.

A max-level watermark would make only the no-op precheck O(1) (the
removal loop still scans); measured shape of CDCL backtracks (to the
assertion level, nearly always below) means the precheck fires true
almost always, so the watermark buys little.  Left as-is with the
findings recorded.

Also examined: `PropagationArena::live_clause` (6.2 %) — already a
tight unsafe arena accessor; the cost is clause-header cache misses in
the watch scan, an arena-layout architectural item.


## Fifteenth addendum: Sydr family re-measurement at `eb704996`

Serial 10 s cap, all 535 files: **decided 395 / timeout 140** (z3:
419).  Timeout clusters: master/yices ≈ 90 (mutual timeouts — z3 also
fails these), minigzip 31 (was 39 at campaign start), hdp 8, faad 3.
The ingestion landings (epoch marks, slab memo, feature-walk gates,
array/nonlinear memos) show up as boundary-cell stability and the
profile, but the family count is unchanged from the epoch-marker
landing — the remaining minigzip/hdp gap is **search-side**: a 10 s
minigzip cell now spends ~2/3 of its time in SAT propagation/scan/
live_clause over the blasted circuits, where the CSR flip was already
measured corpus-negative.  Next honest levers for this family: SAT-core
architectural items (watch layout, arena locality) or encoding-level
wins upstream of the blast (the deferral prototype's 5× on BBB-32
stayed net-negative at −6; a per-class gate remains the recorded
follow-up).


## Sixteenth addendum: solve_equations' mentions memo (`c1815406`)

The mg7 profile's `mentions` 4.6 % + `var_def_operand` 4.6 % + `or_else`
4.6 % decomposed to one cause: `var_def_operand`'s `mentions(rhs, var)`
walk, asked up to four times per (body, var) pair per
`bv_preprocess_assertions` call (collect + apply phases, both
orientations) — with the pair terms *stable across rounds* while only
the pending bodies change.  A per-call `(t, x)` memo (sound by term
immutability) collapses each distinct pair to one walk; the worklist's
direct `mentions` on freshly substituted bodies stays unmemoized
(those terms are new each time).

Measured: counter-identical on minigzip/BBB-32/uclid-define-chain;
~5-8 % wall on the minigzip cell; **stratified-sample matched A/B
147 = 147, zero flips** — profile-level win, no boundary movement
today (the day's arms read 147 under sigid-agent load vs yesterday's
148 idle; matched pairs remain the only decision-grade comparison).


## Seventeenth addendum: the ASP family re-truthed + incremental constraint sweep (`0160249d`)

**The artifact.**  The historical "z3 decides 8/17 asp" was wrong: z3
treats a filename containing `=` as a parameter assignment and errors
instantly, and several asp filenames carry `=`.  With clean temp names,
matched serial arms: **z3 decides 4/17, nixie 3/17** — the family's
true gap is ONE cell (duthen-990602.50: z3 unsat 3.1 s, nixie
timeout) plus a 2–4× constant factor on the three cells both solve.
The "DL-recognition architecture, weeks-scale" framing collapses to a
constant-factor hunt on this family.

**The landing.**  duthen-50's profile differs from minigzip's:
on_backtrack 17.7 %, collect_unified_constraint_atoms 12.2 % (with
SortManager::get 11 % beneath), deletion/restart 17.1 %.  The
constraint sweep rescanned var_to_constraint per assert (quadratic
across the file) AND per check-side relink round; now cursor-driven
over an append-only registration journal (append in record_constraint,
advance per sweep, reset at generation end).  Sound: generations admit
no user scopes, per-entry verdicts are immutable, linkage is
idempotent.

Measured (matched interleaved, settled load): duthen-50 14.5 → 12.4 s,
duthen-57 8.8 → 7.2 s stable; counter-identical on four probe cells;
full bar green.  duthen-50 still exceeds the 10 s cap — next tiers for
it: on_backtrack 17.7 % (fourteenth addendum's constraints stand) and
the SAT kernel.


## Eighteenth addendum: on_backtrack's scan wall — instrumented, then fixed (`d5f9c998`)

The fourteenth addendum left on_backtrack alone on sortedness grounds;
new instrumentation on duthen-50 changed the picture: 74k backtracks ×
76k-entry trail, **5.7G scan units vs 39M removal units** — the scan
was 99 % of the cost, and 38 % of backtracks were no-ops.  The landing
needs no sortedness assumption: a max-level watermark (O(1) no-ops), a
parallel per-entry u32 levels array (contiguous boundary scan,
lockstep-guarded at all six mutation sites), and starting the removal
loop at the `position()` boundary ([0, start) is provably ≤ level).
Measured: duthen-50 19.3–29.1 s → 13.1–13.6 s under matched load;
counter-identical on four probe cells.

Also: budget_bitblast's two-checks test was hardened from a wall
budget (`:timeout 100`) to a counter budget (`:max-conflicts 400`) —
its growth assertion flaked twice on this shared machine; the counter
form proves the same property deterministically and 5× faster.

**Process note (gate):** one gate run FAILed on a verdict mismatch
that reproduced as `base=none` — a load-storm timeout of the *baseline
arm* at a near-cap cell (WS_500 takes 86–101 s against the 150 s cap
at load 40+).  Direct 3×3 reruns: both arms `sat`, candidate faster;
clean gate rerun green (counters 1.000, wall 1.04).  Near-cap gate
cells are load-sensitive in BOTH arms; a `base=none` mismatch with
matching counters elsewhere is an environmental signature, but it
still stops the landing until directly reproduced — as it did here.


## Nineteenth addendum: SAT kernel, item 1 — the BIG overflow bitset (`71fc681d`)

Post-on_backtrack profile of duthen-50: propagate 43 % with
`BinaryImplicationGraph::extra_list` alone at 23.8 % — one call per
propagated literal, a `Vec<Vec<T>>` header chase; instrumented 100M
calls, 95 % empty.  A 1-bit-per-code presence bitset (exact at all four
`extra` mutation sites) guards the lookup: extra_list 23.8 % → 0.0 %,
total samples −9.7 %, counter-identical everywhere incl. a DIMACS gate
cell; duthen-57 wall −10 % under load.

**Measurement lesson (hardened into the protocol):** the first
'verification' of this change was vacuous — a concurrent cargo
operation had deleted `target/release/nixie`; the shell's exec-127
produced empty output and the stats-grep compared empty-to-empty.
Identity checks now assert a non-empty verdict before comparing.

Remaining kernel tiers on this cell: `handle_deletion_restart` 22.8 %
(eliminate 7.2, inprocess 6.0, restart 5.8), `scan_list` 18.8 % +
`live_clause` 14.1 % (the long-clause watch scan and its arena-header
misses — distinct from the corpus-negative CSR flip: blocker/arena
layout is orthogonal to watch-list representation).


## Twentieth addendum: negative — chunked boundary scan (`on_backtrack`)

Tried vectorizing the levels-array boundary scan (64-entry chunks with
`any` + refine): counter-identical but **~3 % slower** clean-interleaved
at load 7 (base median 11.4 s vs 12.7/11.7/11.7/11.8 s) — the chunk
loop's overhead exceeds what the scan saves; the profile's on_backtrack
cost is evidently the prune mechanics + index maintenance, not raw
compare throughput.  Reverted.  The remaining lever for this block is
per-level index bookkeeping replicating the swap-removal order exactly
(~60 intricate lines for ≤ 6 % of one cell class) — recorded, not
taken.


## Twenty-first addendum: the on_backtrack residual — three models, all wrong

After the watermark+levels landing the block still profiles at ~12 % of
duthen-50.  Three cost models were tested and refuted in sequence:
(1) the `position` boundary scan (chunked SIMD version: ~3 % SLOWER —
twentieth addendum); (2) the removal loop's atom-strided level test
(levels-array test: counter-identical, wall wash at load 7); (3) the
removal bookkeeping's scattered writes (arithmetic caps it far below
the profiled share).  The attribution is unresolved — most plausibly
the frame aggregates inlined replay/refresh effects the sampler
attributes to on_backtrack.  Block parked with the finding recorded;
the per-level index bookkeeping lever remains unexplored but its
ceiling (≤ 6 % of one cell class) does not justify the intricacy while
the cost model is unverified.


## Twenty-second addendum: Sydr family, session-cumulative — 410/535

Serial 10 s cap, HEAD `87530d5a`: **decided 410** (z3: 419; gap now
9 cells).  The session's cumulative landings — sweep cursor, on_backtrack
watermark+levels, BIG overflow bitset, the feature-walk gates and
memos before them — moved the family **395 → 410 (+15)** since the
fifteenth addendum's re-measurement.  Timeout clusters: master/yices
90 (mutual), **minigzip 21 (was 31 at campaign start — the kernel
landings crossed ten more cells)**, hdp 7 (was 8), misc 7.

The remaining 9-cell gap is minigzip (~5-6 net of z3's own failures)
+ hdp — search-side, per the fifteenth addendum's lever list.


## Twenty-third addendum: SAT kernel, item 2 — the mid-search BIG fold (`f0d90b3e`)

predicate_561 (minigzip, the 21-timeout cluster) showed the *inverse*
emptiness profile of duthen-50: **81 % of 20M extra_list calls
nonempty** — learned binaries flood the overflow between inprocessing
rebuilds, so the bitset guard passes through and the Vec-of-Vec chase
stayed at 20.5 % of the run.  Landing: a doubling-triggered mid-search
fold (`extra_entries >= 1M && >= primary`) running
`refresh_binary_graph` — exact by construction (overflow edges are all
clause-backed mid-search; sentinels live only inside their minting
round; primary++extra is id-ascending = the rebuild's order).  An
`extra_entries` counter is maintained at every overflow mutation.

Measured: extra_list 20.5 % → below threshold (fold cost 1.0 %), net
−2.2 % CPU samples, counter-identical on four cells; fast wall runs
8.0–8.4 s vs base 9.3–11.3 s at load 10.  Full bar green.


## Twenty-fourth addendum: the hdp class — model-eval pass memo (`55560115`)

The never-profiled hdp cluster (7-8 of the Sydr gap's 9 cells) is a
*third* profile shape: model_refutation_kind 25.6 % (one certification
pass over 4202 assertions — the per-assertion eval memos re-walked
shared meganode prefixes), inprocessing ~42 % (equiv substitution 18.1,
gate congruence 10.5+6.2, eliminate 7.2), deletion/restart 27.8.

Landing: eval_with_reader's walk split into a caller-owned-memo
`eval_walk`; `eval_in_model_outcome_memo` threads one pass-level memo
through `eval_assertion_settled` (per-call form kept for certify/audit
paths).  Sound: the model is fixed within a pass; the (term, depth)
key already encodes budgeted-read depth sensitivity.

Measured: hdp/3128 **41.7-43.9 s → 30.4-34.2 s (−25 %)** matched
interleaved; counter-identical on four cells; full bar green
(12 810 / parity 171-0-6 / gate PASS counters 1.000 wall 1.03).
Family verdict honest: matched A/B on the 14 hdp cells **6 = 6, zero
flips** — the −25 % lifts decide-times (30 s class) but no 10 s-cap
cell was in the crossing band; single-arm readings of 4-6 decided at
load 12 are wall-cap noise.

**The recorded next target**: hdp's ~42 % inprocessing share
(substitution + congruence + elimination) is the clearest
matched-null apparatus target left — a schedule/experiment session
per BENCHMARKING.md.


## Twenty-fifth addendum: SCC single-borrow micro-fix (`cba90f2e`)

The equivalence round's Tarjan worklist took `work.last()` and
`work.last_mut()` per successor visit; restructured to one `last_mut`
per iteration (cursor advanced through the same borrow).
Counter-identical (hdp 3128/2973); hdp/3128 median 34.1 → 31.9 s
(−6 %) matched under load 13.  Full bar green.  The remaining hdp
inprocessing share is schedule territory — the recorded matched-null
session.


## Twenty-sixth addendum: the on_assignment/on_backtrack bookkeeping — examined, load-bearing

Fresh duthen-50 profile post-all-landings: propagate 41.1 % (scan_list
18.5, prefetch 13.6), deletion/restart 24.9 %, on_assignment 8.6 %,
on_backtrack 8.0 % with `slice::get_mut` 7.7 % ≈ the same samples (the
per-removal `trail_index`/`assigned_level` scattered writes — the
third cost model's reality).  `live_clause` fell 14.1 %→2.5 % (a side
benefit of the BIG fold).

`assigned_level`'s per-removal clear was examined for elision and is
LOAD-BEARING: it is the pruned liveness authority for
`drain_forced_eq_atoms` (propagation skip) and
`reason_literal_is_live` (conflict-clause soundness — citing a
retracted literal in a lemma).  No shortcut without re-plumbing the
authority onto the SAT core's trail.

Arithmetic verdict on duthen-50: 12.9 s needs −23 % to cross the 10 s
cap; removing BOTH theory callbacks entirely (16.6 %) would not
suffice.  The crossing path runs through the kernel's deletion/restart
schedule (24.9 %, the matched-null session) and propagation itself —
no remaining micro-lever reaches.  Recorded; micro-vein closed.


## Twenty-seventh addendum: the inprocessing interval — LANDED (`ad7e845b`)

The matched-null session, run per protocol.  **Context correction**:
the 2026-08 studies' "inprocessing net-negative" verdicts were
DIMACS-preset findings; the SMT path inherits inprocessing=on from
`balanced()` whose interval (10000) was never measured on SMT
workloads.  Screening refuted the off-default (duthen-50 12.2 s on vs
16.9 s off), then the interval response: duthen-50 conflicts
70575 → 53399 → 34305 at 10000/5000/2000 — monotone, deterministic
(the SMT path is seed-invariant: identical counters across
NIXIE_SAT_SEED, so the §4 determinism trap does not apply and single
runs ARE valid trajectory comparisons here).

**Null discipline**: the existing lag-2-budget null at the same
density reads 44229 (duthen-50) / 24631 (duthen-57) — treatment/null
0.78×/0.93×, content beyond mechanics.  **Corpus**: 141/170 sample
cells bit-identical (no round fires below 2000 conflicts); the 29
affected: 27 → 28 at the cap, +duthen-50 and lfsr_008_079_032,
−Sage2/bench_3142 churn, 0 disagreements.  Landed at 2000 with
NIXIE_SMT_INPROC_INT / NIXIE_SMT_NO_INPROC overrides.

**Result**: duthen-50 decides unsat at the default in 7.1 s; the asp
17-cell sample reads **4 = z3's 4** — the family gap closed.

Process notes: (1) a whole scan was invalidated by `--stats` writing
to stderr under a `2>/dev/null` — every cell read as timeout; the
re-run with 2>&1 produced the real 29-cell set.  (2) wall-only
readings of the interval screen swung 11.6–16.3 s on identical
deterministic trajectories — pure load; the deterministic-counter
re-screen is the record.


**Addendum to §27**: the hdp+minigzip cluster matched A/B (55 cells,
previous binary vs landed): **10 → 14 decided, +4/0, 0 disagreements**
(predicate_3210, 462, 553, 573 all crossing) — the interval landing
moves the Sydr gap families too, not just asp.


**Caveat to the §27 addendum**: a fresh full-Sydr serial scan under
load 21 read 396 (vs the 410 reading taken at load ~7) — single-arm
wall-capped counts are not comparable across loads; the +4/+1 figures
stand on the matched interleaved A/Bs (55-cell and 29-cell), and the
duthen-50 crossing on deterministic counters.  Re-measure the family
serial count only on a quiet machine.

## Twenty-eighth addendum: subtree_bool_atoms on sorted sets — LANDED (`fb545619`)

The campaign's target #1 (the handoff's fresh hdp/3365 profile:
`subtree_bool_atoms` 37.1 % with 35.1 % of the run inside
`HashSet::insert`), fixed by representation, not by memo scope:

**The change.**  `ctx_simplify`'s per-assert Boolean-atom sets are now
sorted `SmallVec<[TermId; 4]>` (module-level `AtomSet` alias): the
bottom-up construction unions children's sets by two-pointer merge
(`merge_sorted_union`), self-inclusion seeds the vec, and the sole
consumer — `ctx_signature`'s relevance test — does `binary_search`.
No hashing anywhere; `None`/`MAX_MEMO_ATOM_SET` semantics unchanged
(the early `break` on an oversized/absent child is equivalent to the
old set-to-None-and-continue, which matched no further arm once `None`).

**Identity argument + check.**  The set CONTENTS are unchanged, so
`ctx_signature` computes identical DefaultHasher signatures, the
`(term, sig)` memo hits identically, and the walk output is
term-identical — counters identical by construction.  Verified on the
five probe cells (bst/hdp 3365 + nested/hdp 3128, minigzip 492,
BBB-32, duthen-50 .steps.10): all five counter-identical, verdicts
non-empty and matching.

**Matched interleaved A/B, 14-cell hdp family (load 12–16):**

| cell | base | new | verdicts |
|---|---|---|---|
| bst/3047 | 6.1 | 4.3 | unsat=unsat |
| bst/3086 | 9.5 | 6.7 | unsat=unsat |
| bst/3215 | **TO** | **8.5 unsat** | **crossing** |
| bst/3365 | 11.9 | 7.9 / 8.4 | unsat=unsat (−33 %) |
| bst/3422 | 13.1 | 9.3 / 9.8 | unsat=unsat (−29 %) |
| bst/3128 | TO(>35) | 32.9 / 32.2 sat | approaching |
| linear/2871,3051,3210,3250 | 2.2–7.5 | 2.2–7.1 | all =, −5…−23 % |
| nested/3128 | 29.0 | 22.8–32.5 | sat=sat (load-58 noise band) |

bst/3365 `sys` time nearly halved (7.5 s → ~3.9 s of a 14.4 s run) —
the allocation storm was real.  Post-fix profile of hdp/3365
(1 897 samples): `subtree_bool_atoms` 37.1 %→7.9 %, `HashSet::insert`
→0 %, `merge_sorted_union` 0.9 %, `ctx_simplify` 39 %→10 %; the run's
inclusive top is flat (nothing above 7 % — WatchLists::resize 4.4 %,
BIG extra_push/span 4.0/3.6 %).  Full bar green: 12 810 tests, parity
171-0-6 (tracked results byte-identical), perf gate PASS (counters
1.000, wall 1.03).  Binary cached at `precompile/fb545619`.

**Findings recorded along the way:**
1. **An unwired memo (model_certificate_status)**: `55560115` added a
   `pass_memo` local + "one memo for the whole pass" comment to the
   CERTIFICATE path but never switched the inner call — it still calls
   per-call `eval_in_model_outcome` (dead local since).  NOT wired in
   this landing: that path resets `CERTIFY_LIVE_READ` per conjunct, and
   a memo shared across the reset could leak/hide live-read provenance
   between conjuncts sharing meganode subterms (conservative direction
   is Undecided, but the Refuted direction feeds the J5 block-retry
   gate).  Removed the dead local with a pointer comment; wiring it
   needs its own soundness note + A/B (likely cold — the 24th
   addendum's 25 % hot spot was the REFUTATION pass, which is memoized).
2. **Lint drift**: the tree at `caf25750` was no longer clippy-clean
   (`manual_is_multiple_of` is a new-toolchain lint; plus a genuinely
   dead `slb_mut` probe and two unused warnings from `55560115`'s
   aftermath).  Mechanical sweep included in the landing.
3. **Two measurement traps re-hit, both recorded shape**: the CLI's
   verdict line goes to **stderr even without `--stats`** (a stdout-only
   A/B read every cell as TO), and **`/usr/bin/time` does not exist on
   this NixOS host** (exec-127 silently; the old empty-vs-empty trap in
   a new costume — `date +%s.%N` brackets instead).

**Shape 2 (manager/solver-level per-term memo) remains untried** — the
residual 7.9 % `subtree_bool_atoms` is per-assert recomputation over
shared meganode prefixes (hdp files assert ~4 200 formulas).  The
solver-owned shape (blastable-memo precedent; NOT thread-local) is the
next entry if the class still matters after re-census.  hdp's cap
crossings so far: bst/3215 at load 14; 3365/3422 cross at quiet load
(7.9–9.8 s vs the 10 s cap).

## Twenty-ninth addendum: the atom sets go manager-level — LANDED (`d444269d`)

Shape 2 of target #1.  `TermManager` gains `subtree_atom_cache:
RefCell<FxHashMap<TermId, Option<Arc<AtomSet>>>>` — the sets are pure
functions of immutable nodes with never-recycled ids, so entries are
valid for the manager's lifetime and assertions sharing meganode
prefixes clone `Arc`s instead of rebuilding (hdp: ~4 200 assertions).
The walk's dedup moved to the shared epoch visit-marks (the last hashed
set in the construction is gone).

**Identity**: same argument as shape 1 plus purity/lifetime (the
manager's own `eq_solve_cache` doc already states both).  Five probe
cells counter-identical (incl. uclid tcas verdicts).

**Measured**: profile of hdp/3365 — `subtree_bool_atoms` 7.9 %→1.5 %,
`ctx_simplify` 10 %→4 %, merges →0.1 %.  Wall: wash under load 12–17
(hdp decided cells ×3 rounds, deep 30 s cells ×2, uclid 20 MB mplayer
cell ×3 — no arm separates, no regression signal).  The assert-side
block is now closed end-to-end: 37.1 % → 1.5 % of the class across the
two landings.  Gate PASS (counters 1.000, wall 0.98); parity
171-0-6 (a first parity run died in its build step under load 38 —
transient, clean on retry; recorded as the shared-target-dir hazard).

**hdp family status**: 10 s-cap matched pairs at load 12–16 post-both
landings: bst/3215 crosses (TO→8.5 s), bst/3365 reads 7.9–8.4 s and
bst/3422 9.3–9.8 s (crossing at quiet load), bst/3128 decides ~32 s
(30 s class, needs −70 % — search-side now).  A quiet-machine family
re-census is the open bookkeeping item for the next session, alongside
targets #2 (minigzip watch-scan block) and #3.

## Thirtieth addendum: the prefetch over-issue audit — LANDED (`aa89eb68`)

Target #2's counter-safe entry, executed as a 3-arm audit.  The session
kernel's binary-assignment path issued 3 prefetches per assignment
(watch list + BIG edges span + BIG overflow); kissat's `inlineassign.h`
issues exactly one (the first watch line, locality 1).  A fresh duthen-50
profile put `prefetch_watch_payload` at **19.1 %** of all samples
(self-time of the issuing) — the single biggest propagate-path block
after the earlier landings.  (minigzip/492 today reads 0 % — its shape
moved with the BIG-fold landing; the block is binary-density-driven.)

**Arms** (all counter-identical by construction — prefetches are
state-free; verified on duthen-50 across all three): arm0 = 3 issues
(status quo), arm1 = watch-list only (kissat shape), arm2 = none on the
binary path.  Matched interleaved ×3–7 rounds, load 5–12:

| cell | arm0 med | arm1 med | arm2 med |
|---|---|---|---|
| duthen-50 | 15.43 | **14.89** | 14.92 |
| hdp/3365 | 8.37 | **7.92** | 7.97 |
| minigzip/492 | 7.93 | **7.49** | 5.95* |
| minigzip/562 | 10.39 | **10.11** | — |
| BBB-32 | tie | tie | tie |

(*single round.)  arm1 wins or ties everywhere; arm2's loss of the
watch-list prefetch gives the gain back — the watch-list line does real
latency hiding, the BIG span+overflow lines were the over-issue (issued
3-per-assignment, scanned only if/when the queue reaches the literal).
Landed arm1 with the rationale in a code comment at the site.

**The 33-cell minigzip block after this**: the audit's entry is now
spent; the remaining shape per the fresh 492 profile is propagate 17.5 %
(session_kernel 17.4) + the encode-side blocks — the watch-list
representation (CSR) stays corpus-negative per the 2026-09-20 finding;
deletion/restart scheduling remains the recorded matched-null session
target (24.9 % of duthen-50 pre-interval-landing).

Gate PASS (counters 1.000, wall 1.04); parity 171-0-6; 12 810 tests.
