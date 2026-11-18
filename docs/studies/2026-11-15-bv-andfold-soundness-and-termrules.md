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
