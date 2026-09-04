# Inprocess-round gating: no gate — and the scheduled ELS had been silently dead (2026-09-05)

Follow-up to `2026-09-04-inprocessing-standing-corpus.md`, which pre-registered
"Open (next campaign): a *gating policy* for the mid-search rounds — the
win/loss split may be observable".  This study ran the telemetry rung of the
§10 ladder for that gate, closed it (**the win/loss split is trajectory
reshuffle, not an instance property; no observable separates it**), and in
the process found and fixed a real bug the telemetry exposed: **the
conflict-scheduled equivalent-literal substitution (ELS) has been a silent
no-op since `58df118`** — a latch set before the call it guards.  The fix
lands with the ELS pass still default-off (measured net-negative at the cap
when actually executed), the default trajectory **bit-identical** to the
previous release, and the 6s167-opt anchor improved 0.35× when the pass is
enabled.

All numbers are deterministic counters (conflicts/propagations); wall is
sanity only.  Corpus: `precompile/corpus-sc24f/` (54 files).  Off-arm
baselines: result store `precompile/dcfc089/benchmark/runs/sc24f/` (seed 0).

## 1. Per-round telemetry: what an inprocess round actually does

`NIXIE_INPROC_TRACE=1` (landed with this study) prints per scheduled round:
cost (`props_in_round`), yield, per-pass deltas (`els units shr sub tred
tfailed`), plus `gate_congruence`/`els_one_shot` firing lines.  Swept over
the 19 decisive files (10 winners, 9 losers of the 2026-09-04 A/B):

* **Cost and yield do not separate winners from losers.**  The biggest
  zero-content spenders are *winners*: qwh.50 — 12 rounds × ~10 M props
  (the `MAX_VIVIFY_PROPS` ceiling), total yield **274**; worker_550 — 9 ×
  10 M props, yield **216**; shuffling-2 — 1 × 10 M props, yield 78.
  Meanwhile cheap near-zero-yield rounds *lose* (mp1-Nb7T42: 136 rounds,
  median 815 k props, total yield 2 712).
* **Pass attribution:** on qwh.50 / worker_550 / mp1 every round shows
  `els=0 units=0 shr=0 sub≈15 tred=0` — `orig` never changes on mp1
  (412 776 → 412 776 at every round).  A round that changes nothing in the
  DB still flips the verdict: its effect there is pure search-state
  perturbation.
* **Static DB shape does not separate either** (orig size, learned/orig,
  learned-growth-per-conflict, walk counters all fail).
* **Yield per round does not separate**: Timetable yields 7 707/round and
  is destroyed; stable-300 yields 2 818/round and wins 0.21×.

## 2. Uncensored losses, then the seed test: the decisive list is reshuffle

Uncensored (900 s cap) on/off conflicts for the 9 sat→TO losers: g2-slp
1.09×, noL 1.45×, crypto1 3.3×, af-synthesis 8.1×, mp1 15.0×, rbsat 15.9×,
Timetable and 64_25 TO at 900 s.  Only g2-slp/noL are cost-dominated (the
kissat-shaped effort-bounding idea would recover exactly those two).

But a 10-seed CRN sweep (`off` / `full (INPROCESS=1)` / `rounds_only`,
60 s cap; `SEED=0` verified ≡ unset) shows the list is not an instance
property: **mp1 — the 15×-destroyed file — solves *better* under the full
bundle at seeds 1–10** (5/10 solved, median 15.6 k conflicts, vs off 6/10,
median 33.3 k); qwh.50's off-arm TOs at all ten seeds (its standing 0.37×
"win" was one draw vs one draw); worker_550's 0.06× rounds-only win TOs at
seeds 2–6.  Per §6/§11.1 the per-file win/loss list is **dominated by
trajectory reshuffle**; the exceptions are the three tails the parent study
already verified seed-robust (mrpp 0.53×, FmlaEquivChain 0.35×, 6s167
0.56× — all unsat, all yield-heavy rounds).

**Consequence:** a gate must fire per instance/round from online state; no
online signal separates the classes (§1) and the classes themselves are
not stable across seeds for anything but the three real tails.  Selecting
the default-seed winners would be hindsight-oracle policy (§6).  **No gate
is implementable; the thread closes.**  The pre-registered matched-null
protocol (scrambled pass content) never became necessary — no treatment to
null.

## 3. Kissat component knockout: the residue is the simplification fixpoint

Per-component knockout of kissat 4.0.4 on the anchors (conflicts):

| arm | 6s167-opt | FmlaEquivChain | mrpp_4x4 |
|---|---|---|---|
| default | 19 164 | 377 701 | 179 485 |
| `--probe=0` | **544 777 (28.4×)** | 746 083 (1.98×) | 323 013 (1.80×) |
| `--sweep=0` | 50 908 (2.66×) | 829 147 (2.20×) | 239 476 (1.33×) |
| `--eliminate=0` | 37 786 (1.97×) | 460 736 (1.22×) | 223 390 (1.24×) |
| `--transitive=0` | 27 992 (1.46×) | — | — |
| `--{backbone,congruence,substitute,factor}=0` | 0.47–1.02× | 0.89–1.30× | 0.76–0.95× |
| `{sweep,backbone,vivify,transitive}=0` | 72 667 (3.79×) | — | — |

With its probe subsystem disabled, kissat needs **more** conflicts on
6s167-opt (545 k) than nixie with inprocessing off (118 k).  Note what
kissat 4.0's "probe" is: `src/probe.c` is a 104-line *driver* — the round
iterates congruence → substitute → backbone → vivify → sweep (kitten) →
substitute → transred → factor to a fixpoint (`proberounds`); there is no
classic failed-literal lookahead in it at all.  No single component
carries the 28× (largest: sweep 2.66×; several knockouts *improve*
kissat); the leverage is the **fixpoint interaction**.  kissat's
statistics on 6s167: 335 units (7%), 429 hyper-binaries, 3 258 vars
eliminated (70%), 665 substituted, 410 congruent, 28 950 kitten solves.

This **re-attributes the 6s167-opt 6.5× residue** of the parent study: the
"~3.7× learned-clause-quality/retention residue" framing was a symptom —
kissat's small heavily-reused learned DB is what the search looks like
*after* structural collapse (70% of variables eliminated, ~27% merged as
equivalences).  Retention was never the carrier (consistent with the
closed `2026-09-02` retention studies, T/N ≈ 1.0).

## 4. The bug the telemetry exposed: the scheduled ELS was a silent no-op

Instrumenting why our structural numbers are so much weaker (nixie on
6s167: `substitutions=0` vs kissat's ~1 237 merged vars) found it: the
conflict-scheduled ELS slot (`learn.rs`, introduced by `58df118`,
2026-08-20) sets the one-shot latch **before** calling
`substitute_equivalent_literals`, whose first line is exactly that latch's
guard — every scheduled ELS call returned immediately.  With the default
`presearch_collapse = false` the pre-search ELS site is skipped too, so
equivalence substitution — and the gate-congruence closure it hosts
(`congruence.rs`, enabled in every preset) — executed **nowhere** on the
default path.  The `0ed8543` "BVE + ELS on by default, 3.6–14×"
measurement (2026-08-21, one day later) had therefore measured BVE alone.
The SMT freeze-collapse path (`enable_equiv_substitution: freeze_collapse`)
was equally affected.

**Fix** (landed): the slot keeps its cadical-parity schedule (root
backtrack + one-shot latch — part of every shipped default trajectory
since `58df118`, kept unconditional so the default trajectory is
preserved) but now calls the latch-free
`substitute_equivalent_literals_round()` — the variant `inprocess()`
rounds already use — gated on `enable_equiv_substitution` and
`destructive_preprocessing_safe()` exactly like the `inprocess()` ELS call.
Pinned by `scheduled_els_executes_when_enabled` (php(7,6) + an explicit
x≡y pair; asserts `stats().substitutions > 0` — fails on the buggy form).

### What actually running the ELS does (why the preset stays off)

With the pass enabled on the standing corpus (single-seed screen,
verdict-checked, 0 mismatches): 6s167-opt **118 191 → 41 280 conflicts
(0.349×)** — the congruence closure finds 4 526 AND gates and folds 203
substitutions on that file (kissat: ~2 700 gates/round × 6 rounds), bigger
than the entire inprocessing bundle's 0.69× — but solved-at-cap drops
50 → 41 (nine near-cap files TO, the same sat-side signature as the
bundle).  Per the §3 enablement rule (solved must not be worse) the
CaDiCaL preset keeps `enable_equiv_substitution: false`, now with an
honest comment instead of an inert `true`.

## 5. Landing evidence

* **Identity gate (default path): PASS.**  The landed tree vs
  `precompile/dcfc089` over the 54-file corpus: every decisive file
  verdict- AND conflicts-bit-identical (j3037 377 306, worker_550
  106 143, g2-slp 344 655, x9-08075 751 542, crypto1 2 308 198,
  FmlaEquivChain 2 147 581 = the stored seed-0 record, mrpp 249 027, …).
  Earlier screens suggesting −9/−12 files traced to (a) a result-store
  join bug (tails carry 10 seeds/file; the join must filter `seed == 0`)
  and (b) wall-cap censoring under concurrent load — not to behavior
  changes.  (Also recorded: a scare about run-to-run "nondeterminism" on
  mrpp was a regex matching `stable_conflicts=`'s substring — the solver
  is bit-deterministic.)
* **SMT differential** (270-instance pinned sample vs z3, freeze-collapse
  default now running *real* ELS in the embedded core): **0 verdict
  differences** vs the pre-fix baseline build, both arms 160/160 agree
  with z3, 0 soundness disagreements, par2 2311 → 2318 (+0.3%, neutral).
* **Canaries:** `pete/cxs-bp-ex-safety` `unsat`; `wisas/xs_8_13` `unsat`;
  `pete_cxs_bp_is_unsat_on_every_trajectory` PASS (312.7 s).
* **Full bar:** build, 10 467 tests (incl. the new regression test),
  clippy, fmt, doc, Z3 parity 170 files / 0 mismatches.

## 6. What is open; what not to retry

* **Do not retry**: any per-instance/per-round gate over the inprocess
  bundle (§1–2); effort-bounding as a *verdict* lever (recovers only the
  two cost-dominated losers); the pre-search one-shot (no-op, parent
  study); yield-threshold gating (yield does not separate).
* **Open, evidence-backed**: kissat-shaped **pre-search equivalence
  extraction at full effort** — run the (now working) ELS + congruence +
  probing *before* search, kissat-style, instead of once mid-search at
  conflict 2 000.  The mid-search one-shot measured −9 at cap here, but
  kissat's collapses are pre-search fixpoints; a pre-search variant
  (possibly gated on detected gate structure, à la the 4 526-gate signal)
  is the next pre-registered A/B, with the matched-null discipline of §2.
  The larger missing piece (kitten sweep, 2.66× single-component on
  6s167) remains a separate campaign.

## Reproduction

Telemetry/seed/screen scripts + raw logs: `precompile/corpus-sc24f/`
(`telemetry.py`, `seed_sweep.py`, `els_fix_screen.py`; logs under
`/tmp/inproc_telemetry/` were scratch).  Kissat knockouts:
`kissat --statistics [--probe=0 …] <corpus>/…-6s167-opt.cnf`.  The ELS-on
arm: set `enable_equiv_substitution: true` (CaDiCaL preset) on the landed
tree.

## 7. Follow-up (same day): pre-search ELS at full effort — no-go

The §6 open item was tested immediately: `els_presearch` (landed as A/B
infrastructure, default off; `ELS_PRE=1` in `stats_solve`) runs the ELS
round — BIG refresh, AND/XOR gate-congruence augmentation, SCC fold,
rewrite — to a bounded fixpoint (≤4 rounds) *before* search and consumes
the mid-search one-shot latch (kissat `probe_initially` shape).

**Pre-registered gates** (before the run): advance iff solved-at-60 s ≥
baseline AND conflicts geomean ≤ 0.95 over both-decisive AND the 6s167
anchor gain survives; drop otherwise; any verdict mismatch stops
everything.

**Result (54-file 3-arm screen, CRN vs stored seed-0 baselines,
0 verdict mismatches):**

| arm | geomean vs base | 6s167-opt | notes |
|---|---|---|---|
| off (landed default) | 1.0000 | 118 191 | identity re-verified |
| `ELS=1` (mid-search one-shot) | 1.0339 | 41 280 (0.349×) | 203 folds |
| `ELS_PRE=1` (pre-search fixpoint) | 1.0352 | 43 365 (0.367×) | **571 folds** |

The fixpoint extracts **2.8× more equivalences** (571 vs 203 on the
anchor) yet converts none of it into corpus conflicts-to-verdict.  The
per-file effects of pre vs mid move in *both* directions (x9-09054 0.26×
under pre but unchanged under mid; mrpp 1.66× under pre vs 0.89× under
mid; rbsat TO under pre at 90 s on an otherwise-quiet core but identical
under mid) — the damage is not a placement artifact; it travels with the
ELS content per file, in the now-familiar sat-side-destruction signature
(rbsat/af-synthesis/Timetable TO; mp1 2.6×; summle_X11112 11×).  Per the
pre-registered rule: **drop**; `els_presearch` stays default-off A/B
infrastructure (`els_presearch_folds_before_search` pins the wiring).

**What this closes:** ELS *placement* is exhausted as a lever on this
corpus (mid-search one-shot and pre-search fixpoint both measured,
both fail).  The 6s167-class anchor win (0.35×) is real, seed-robust
(§4), and available behind `enable_equiv_substitution`, but its corpus
price is the sat-side losses.  The remaining evidence-backed gap is the
kissat simplification fixpoint's *content* we still lack — kitten sweep
(`--sweep=0` ⇒ 2.66× on 6s167) and its interaction with eliminate —
a separate campaign per §3.

## 8. Second follow-up (same day): structural gate-gating dead at telemetry; kitten sweep sized thin

Two closure measurements for §6/§7's remaining "open" items:

**Gate-count gating (dead at the telemetry rung).**  `GATE_COUNT=1` in
`stats_solve` (landed; `Solver::detected_gate_count` accessor) prints the
AND/XOR gate count of the parsed formula — a seed- and
trajectory-invariant formula property, the one signal family §1 had not
tested.  Counts across the 54 files: 64_25 4.07 M, g2-ak128booth 571 k,
g2-slp 85 k, mp1-klieber 30 k, summle 7.8–10.5 k, shuffling-2 7.6 k,
6s167-opt 4 507, j3037 866, simon 512–800, Timetable 80, and **0 on 30
files**.  The join against the ELS arms' win/loss list fails: zero-gate
files appear on *both* sides (winners x9-09054 0.26×, stable-300 0.47×;
losers rbsat TO, mp1-Nb7T42 2.6×, mrpp 1.7×) — because the ELS round's
*binary-SCC* content is independent of gate structure.  The signal gates
only the congruence half of what it would need to gate.  Not retried.

**Kitten sweep (sized, deprioritized).**  kissat `--sweep=0` over the
whole 54-file corpus: geomean **1.0121** (40 both-decisive), solved
47 → 45, strongly bimodal (without sweep: 6s167-opt 2.66×, FEC 2.40×,
mp1-klieber 3.96× worse — but j3037 **0.11×**, summle_X11112 0.30×,
circuit_48i 0.67× *better*).  Even for kissat, sweep is a ~1 % corpus
effect with a per-file lottery profile.  A multi-thousand-line embedded
sub-solver port priced against that reference measurement fails any
priority bar; the 28.4× probe-knockout on 6s167 was the *interaction*,
not sweep.  Downgraded from "open campaign" to "not before a component
that sizes bigger".

**Where this leaves the standing 1.332× gap**: the equivalence/
inprocessing lever family is measured to exhaustion at every rung short
of the kitten port (which sizes thin) — mid-search one-shot and
pre-search fixpoint both no-go, placement-independent sat-side damage,
no structural or online gate.  The anchor win (6s167 0.35×, seed-robust)
ships behind `enable_equiv_substitution`.  The remaining standing-gap
levers live elsewhere: worker-class memory/binary density (out of this
campaign's scope by charter) and BCP throughput (measured closed ×4).

## 9. Third follow-up (same day): binary-chain factoring ported — sound slice, anchor 0.44×, corpus not yet

The remaining standing-gap lever was sized from kissat component knockouts
on worker_550: `--factor=0` costs kissat **21.5×** conflicts there
(2 003 → 43 083; every other probe sub-pass neutral or helpful), and
worker_550 + shuffling-2 carry almost the whole 1.332× standing geomean
(remove them: ~1.08×).  Recomputed gap decomposition: both are
SAT files solved by kissat/cadical in long phase-guided descents
(227/58 decisions per conflict vs our 6.8), and our conflict counts on
them are wildly seed-dependent — the lever is *descent reliability*, and
kissat's descent on worker_550 is factoring-made.

**Ported** (`solver/factor.rs`, kissat `factor.c` first slice): for a
literal `f` with binaries `(f ∨ q_i)` and a second literal `g` whose
clauses `(q_i ∨ g)` witness every matched partner, replace the quotients
with dividers `(x ∨ f) (x ∨ g)` and `(¬x ∨ q_i)` over a fresh `x`,
keeping the witnesses.  Equisatisfiable and model-preserving (all three
model cases extend: `f∧g → x=F`; `¬f → q_i → x=T`; `f∧¬g → witnesses
unit-force every q_i → x=T`).

**The polarity bug the harness caught** (recorded for the pattern): the
first port read the witness as `(¬g ∨ q_i)` — kissat's watch positions
make it `(q_i ∨ g)` — and the flipped direction is UNSOUND: a model with
`f ∧ ¬g ∧ ¬q_j` satisfies every original and flipped witness but has no
`x` extension.  300 random differential trials and the fixture tests all
passed anyway (the shape is rare in small random formulas); the corpus
A/B's verdict checking caught it as **18 sat→unsat flips** before
anything landed.  Both the fixture polarity and a targeted
counter-model regression (`factor_witness_polarity_regression`) pin it
shut.

**Measured (corrected, 54-file A/B, verdict-checked, 0 mismatches, 0
invalid models):** geomean 0.9519 over 23 both-decisive — strong real
wins (worker_550 106 143 → 46 659 = **0.44×**, stable-300 491 382 →
43 067 = 11×, frb65 4.6×, j3037 2.6×, crypto1 recovered 2 308 k → 667 k)
against real losses (summle class 2.4–5.6×, Timetable/qwh/af-synthesis/
64_25/rbsat/circuit_64i TO at cap).  Net at the cap: not better than
baseline.  Per the enablement rule the slice lands **default off**
(`SolverConfig::enable_factoring`, `NIXIE_FACTOR=1` / `FACTOR=1` in
`stats_solve`) as sound, tested A/B infrastructure.

**Recorded next slices** (each pre-registered before measuring): chain
refinement beyond one `g` per `f` (kissat's quotient chains — its 51 466
factored vars on worker_550 vs our 7 228 come from depth + re-arming),
large-clause factoring (same-size matching through minimal watch lists),
post-elimination placement (kissat runs factor inside probe rounds after
eliminate, `factordelay` skipping the early rounds — our slice is
pre-search only), and fresh-variable decision integration (kissat
queue-front; a naive `bump_decision_hint` measured harmful here,
1.26× on worker_550).

## 10. Fourth follow-up (same day): incremental BIG compounding — both gap-carriers collapse

The volume blocker was found by round telemetry: with a single
end-of-pass BIG rebuild, round 2 saw 86 486 candidates and introduced
**zero** — the new quotient binaries `(¬x ∨ q_i)` were invisible to the
adjacency scans, so no candidate could match them as witnesses (kissat
connects new binaries to its watches immediately inside the pass).
Maintaining the BIG incrementally per application (`add_bin` + edge purge
on quotient deletion) lets the fixpoint compound — and it is the
compounding that carries the anchor wins:

| file | base | §9 slice | + compounding |
|---|---|---|---|
| worker_550 | 106 143 | 46 659 (0.44×) | **6 679 (0.063×)** — kissat: 2 003 |
| shuffling-2 | 23 130 | — | **449 (0.019×)** |
| stable-300 | 491 382 | 43 067 (11×) | 99 114 (5.0×) |
| mp1-Nb7T42 | 106 295 | 1.62× worse | 71 299 (0.67× better) |

**Both files that carry the entire standing conflicts geomean collapse to
kissat-class descents** (worker: 195 k decisions, 4 restarts — the long
descent; wall 26.4 s vs 31.6 s).  Compounding also *reverses* some §9
losses (mp1 1.62× → 0.67×).  Soundness unchanged: the compounding applies
the same verified transformation (fixture now pins 2 introductions:
round 2 legitimately re-factors the kept witnesses against the round-1
quotients); 300-trial differential and the corpus A/B stay at 0 verdict
mismatches / 0 invalid models.

Remaining losses (quiet-core verified): Timetable, af-synthesis, 64_25,
rbsat, circuit_64i TO; summle class 1.9–6.6×; si2 2.4×; ITC 3.9×;
worker_20 4.9×; 6s167 1.24×.  Rounds >1 are not the cause (summle/ITC
regress at rounds=1); **binary density does not gate it** (measured:
winners worker 100 %/shuffling 83 %, losers rbsat 99.9 %/qwh 98.9 %/
ITC 95.6 %/af-synthesis 90 % — both classes live at high density), so
the bimodality is the familiar inprocessing-class per-file chaos plus
real damage, not a formula-invariant property we can gate on.  kissat
itself shows the same profile (its `--sweep=0` knockout *improves* j3037
9×).  Default stays off; the recorded next question is whether any
loss-side mitigation exists at all (fresh-var phases? placement?), or
whether factoring joins ELS in the "real anchor win, corpus-negative"
bin.

Wall cost of the pass on huge DBs measured acceptable: worker_550's full
factored solve is 26.4 s vs the default's 31.6 s (the pass is included).

## 11. Fifth follow-up (same day): the §6 seed gate falsifies the anchor collapses

The §10 collapses were default-trajectory draws.  10-seed CRN
(`off`/`NIXIE_FACTOR=1`, 120 s cap, then sequential quiet-core 300 s runs
to strip wall contamination from the pass itself):

| file | off (seeds 1–10) | factored (seeds 1–10) | sequential quiet, factored |
|---|---|---|---|
| shuffling-2 | **10/10** solved, cf 185–4 818 | 0/10 (all TO) | seed 1: 3 872 (6.7× worse); seed 2: 1 936 (1.34× worse); seed 3: 1 084 (2× better) |
| worker_550 | 4/10, cf 2 463–28 015 (median 15 009) | 1/10 under load | seed 1: 15 745; seed 2: 22 289 — inside the off-arm's own band |
| stable-300 | 7/10, cf 9 302–1 325 495 | 4/10 | paired 0.196× over 2 both-decisive seeds (n too small) |

Two findings:

1. **The collapses are trajectory reshuffle, not effect** (§6 criteria
   (a)+(b): high-seed-variance files, no survival at fresh seeds).  The
   deeper re-attribution: *worker_550's off-arm conflict distribution is
   itself a P(descent) lottery spanning 2.5 k–106 k+* — the file's share
   of the "standing gap" was a bad default draw, and the factored 6 679
   was a good draw from the same class of distributions.  Neither number
   is a file property.  (Consistent with §2's mp1 lesson and the
   qwh/worker_zero-yield wins of the inprocessing study.)
2. **The pass has a wall-cost hazard the deterministic budget does not
   see**: ~20 s on worker_550's 10.3 M clauses and ~60 s on shuffling-2's
   4.7 M — under a 60 s cap that is an automatic TO regardless of search
   path.  The edge-visit budget must be scale-aware before any default
   consideration (kissat's is tick-based, i.e. work-proportional).

**Campaign verdict (factoring)**: the port is sound and landed as opt-in
infrastructure; the rewrite does not by itself make our search descend
the way kissat's does after the same rewrite (kissat's 21.5× knockout on
worker_550 is real, but our factored trajectories at fresh seeds sit in
the unfactored distribution).  The remaining distance lives in the
search×factored-structure interaction — kissat's fresh-variable queue
placement, its branching on the factored hubs, or components we have not
isolated — not in the transformation.  Recorded as the next hypothesis,
with the seed protocol attached: any future "descent" claim on this
class requires the 10-seed P(descent) comparison, not a default-seed
conflict ratio.

## 12. Sixth follow-up (same day): the queue-front hypothesis falsified; what remains is volume or search

Two cheap tests of "decide the fresh factored variables first" (kissat's
literal queue-front, the most visible search-side difference after the
rewrite):

* `domain_priority` (exact decide-first semantics): **O(|priority|) per
  decision** — 3 543 fresh vars × 195 k decisions alone exceeds a 180 s
  cap on worker_550 (the run produced no verdict at all).  The mechanism
  is unusable at this scale; recorded as a wall hazard of the knob.
* Dominant VSIDS activity (`NIXIE_FACTOR_BUMPN=5000`, O(1) per decision):
  worker_550 factored — default seed 46 863 (7× worse than the unpriorized
  6 679), seed 1 TO (vs 15 745 unpriorized), seed 2 2 796 (vs 22 289).
  Mixed across seeds — no reliable descent.

Even the best factored descent (29 decisions per conflict) is 8× more
conflicty than kissat's (227), and kissat rewrites **51 466 variables vs
our 3 543** — the honest un-ported piece is chain refinement
(multi-factor quotient chains, `factor.c`'s core loop), which is where
kissat's volume comes from.  Whether our search would descend on a
fully-factored worker the way kissat's does remains open — the P(descent)
protocol of §11 applies to that claim whenever it is made.

## 13. Seventh follow-up (same day): the volume ceiling is budget × scan-rate

Why our compounding stops at 3 543 introductions where kissat reaches
51 466 on the same file: round telemetry showed round 2 exiting at its
*first* candidate — round 1 exhausts the 400 M edge-visit budget, and
`budget_hit` persists across rounds (an earlier env-override test of a
8 B budget was void: the override did not reach one of the two budget
checks).  With the override actually wired, an 8 B-budget run times out
at 590 s: the `Vec<Vec<(Lit, ClauseId)>>` BIG adjacency chases pointers
at roughly 20× kissat's per-tick cost (kissat scans compact watch lists;
283 M factor ticks on this file are seconds for it, ~20 s for our 400 M
visits).

**Consequence:** raising the volume to kissat's level needs both (a) a
compact pass-local adjacency (CSR snapshot with tombstoned deletions and
an append region for new quotients) so the counting scans run at memory
bandwidth, and (b) the chain refinement for matching quality (§12).
Both are named, self-contained pieces; the `NIXIE_FACTOR_BUDGET` knob
(now actually wired) exists for their A/Bs.  The landed default stays
400 M / 3 543 introductions / worker default-seed 6 679 conflicts —
and per §11, volume claims go through the 10-seed P(descent) protocol,
not default-seed conflict ratios.

## 14. Eighth follow-up (same day): scan-rate fixed; volume measured NON-MONOTONE — the lever family closes

The per-entry `clauses.get(cid)` liveness dereferences were removed from
all three scan sites (the pass maintains the BIG-live invariant itself:
parse-time registration + incremental purge), making the counting loops
pointer-chase-free (worker 400 M visits: 26 s → 23 s; the arena lookups
were real but not the dominant cost at this scale).

With the budget actually scalable, the volume experiment answers the
§13 question **negatively**: 2 B edge visits on worker_550 introduce
**20 370** variables (5.7× the default's 3 543, occurrence reduction
5.3 M) and the default-seed conflicts get **worse** — 31 895 vs 6 679.
Rewrite volume is non-monotone in trajectory quality for our search:
the CSR adjacency + chain-refinement port is *necessary-but-insufficient*
for the descent question.  Combined with §12 (queue-front falsified both
ways) and §11 (the default-seed collapses were lottery draws), the
factoring lever family closes as: **sound landed infrastructure, real
kissat-side knockout evidence, no measurable path from the rewrite alone
to reliable descents in our search**.  The distance to kissat on the
descent class is in the search stack, not the preprocessing.

Final campaign ledger (14 sections): one real bug fixed (ELS no-op), one
sound port landed behind a flag (factoring), two seductive default-seed
claims falsified by their pre-registered protocols (ELS placement,
factoring collapses), three gate hypotheses killed at telemetry
(online observables, gate counts, binary density), and the standing-gap
decomposition corrected (two P(descent)-lottery files + a ~1.08×
residue).  Every claim in this file carries its falsification protocol.

## 15. Ninth follow-up (same day): oracle-phase collapse verified genuine; worker-class improvements are re-rolls

Before building a phase-source campaign on the §11.3 measurements, the
collapse was audited for oracle leaks (suggested in review):

* **Mechanism**: `set_phase_hint` writes only the saved/target/best phase
  arrays — no trail assignments, no units, no propagation.  A pure
  polarity preference.
* **The 0-conflict x9-09054 run**: 39 decisions, 450 propagations, 0
  conflicts — a pure descent; the returned model validates externally
  (4 052 clauses, 0 violated); verdict matches ground truth.
* **Corrupted-hint gradient (the leak test — a leak collapses
  regardless of hint content)**: true oracle 0 → 10 % flipped 398 308 →
  50 % flipped 1 287 746 → scrambled 1 662 168 (base 249 455).
  Monotone degradation: genuine phase information, no leak.

The same gradient on worker_550 **refines the class claim**: 1 % flipped
36 634, 10 % flipped **6 004**, 50 % flipped 6 894 — *corrupted hints
beat the true oracle* (18 985).  Worker-class "oracle improvements" are
substantially trajectory re-rolls (§6), not phase information; the
cleanly phase-bound file in the measured set is x9-09054 (and the
monotone gradient is the signature to demand of any future claim).

`NIXIE_PREWALK=<flips>` (the §8-open "one-shot pre-search phase
initialisation": `warmup()` + bounded `walk_round`, best assignment into
saved phases) lands as the candidate-source knob.  First datapoint: on
x9-09054 the walk's local optimum does not reach the oracle basin
(10 k flips 240 735 ≈ base; 100 k flips 622 750, worse) — ProbSAT
closeness is not automatically phase-transferable, exactly the
§11.3 "screening, not a result" caveat.

## 16. Tenth follow-up (same day): the phase-source screen closes — walk phases cannot reach XOR-crafted basins

`NIXIE_PREWALK` diagnostics (best broken-count of the walk's final
assignment, x9-09054, 450 vars / 4 052 clauses): 1 k ticks → 326 broken,
10 k → 133, 100 k → 42, 1 M → 32; mid-search walks plateau at 18–22.
The walk never approaches a model — x9 is XOR-crafted, and ProbSAT-style
local search is structurally blind to parity (no gradient toward
satisfying a parity constraint).  This closes the loop opened in §15:
the files whose oracle-phase gains are *genuine* (x9-class) are exactly
the files where cheap phase sources cannot operate, and the files where
a walk could in principle operate (worker-class) are re-roll-dominated.
The §8-open "one-shot pre-search phase initialisation" is now measured
from both ends: **no cheap phase source reaches the oracle basins that
matter.**  Reaching the x9-class basins requires parity structure
(XOR/Gauss reasoning) — a different solver component, priced far above
this campaign.  The knob stays as infrastructure with its diagnostic
(`prewalk: best_broken=…`).

## 17. Eleventh follow-up (same day): XOR phase seeding — measured neutral-to-negative; the real lever is the dormant propagator

Corpus telemetry (strict parity-class scan): **22 files carry XOR
structure** — simon ×13 (2–3k groups each), g2-ak128booth (99k groups /
181k vars), summle ×3, mp1-Nb7T42 (25k groups / 52k vars), g2-slp,
pb_300, and **mdp-28-14 — one of the four standing unsolved files (373
groups over 401 of its 792 vars)**.  A theoretical anchor corrected
along the way: *any* model as phases gives a 0-conflict descent (unit
propagation never conflicts under model-consistent decisions), so the
oracle-phase residuals measured earlier (qwh 20k, worker 19k) were
`random_polarity_prob` noise, and x9-09054's clean 0 was luck (39
decisions ≈ 45 % chance of zero random flips) — x9 has **no** XOR
structure at all (its 720 var-pairs are duplicate clauses), so the
"parity-blind walk" story of §16 was a misattribution.

**Slice landed** (`solver/xor.rs` + `enable_xor_reasoning` /
`NIXIE_XOR=1`, default off): detection **delegates to the crate's
existing `XorDetector`** (discovered dormant in `src/xor.rs` — GF2 rows,
detector with correct `rhs = (negation-parity == 0)` semantics, and an
unwired `XorPropagator` with watched literals and CDCL conflict
reasons); on top of it a GF(2) Gaussian elimination and **phase seeding
only** — no verdicts (an inconsistent system is traced, not answered,
pending a proof story).  Tests: strict-rejection (implication pairs and
duplicates are not constraints), both parity classes, GE
satisfies-every-constraint + inconsistency detection, and an end-to-end
model-descent (0 conflicts under seeded phases with random polarity
off).  The author's own first `rhs` derivation was parity-flipped and
the test anchors caught it — the anchors are the `(¬a∨b)∧(a∨¬b) = a↔b`
identities.

**Measured (single binary, 54 files, verdict-checked, 0 mismatches)**:
off-arm identity **1.0000**; on-arm **1.0438** with only two files
changed — both summle, both *worse* (1.41×, 2.07×).  Two properties
explain the near-nothing: most detected systems are satisfied by the
all-`false` default phases (GE returns the default; the trajectory is
bit-identical — mp1-Nb7T42 with 25 480 constraints is unchanged), and
where the GE solution does differ it is one arbitrary solution of the
subsystem, uncorrelated with the non-XOR structure (the summle
regressions).  An earlier build of the slice measured summle_X4044 at
0.27× — a detector-variant lottery draw (7 constraints differ →
different free-variable resolution), falsified by the clean rerun.
mdp-28-14 still TOs (51 % var coverage; the non-XOR half remains).

**What survives as the real lever**: the dormant `XorPropagator` —
in-search propagation of linear consequences with conflict reasons
(CryptoMiniSat's architecture) — is the way XOR structure pays; phase
seeding provably cannot (this section).  That integration is a
campaign of its own; the detector, the GF(2) core, and the wiring point
now exist and are tested.

## 18. Twelfth follow-up (same day): XOR-aware probing — landed with a real perf fix, measured flat-to-negative

The tractable slice toward in-search propagation: `xor_probe`
(`NIXIE_XORPROBE=1`, default off) — build the GF(2) matrix, force
add-time-pinned units at level 0 (with CNF-propagation interleaved to a
fixpoint), then probe both polarities of every matrix variable at a
decision level with CNF propagate + matrix folding; a failed polarity
forces its opposite at level 0 (the `probe_round` pattern — probe-level
assignments are self-contained, so no CDCL reason plumbing is needed).
Fold discipline per `GF2Matrix::propagate`'s contract: every trail
literal during a probe is folded in trail order and undone in exact
reverse; level-0 folds are permanent.  No verdicts beyond the level-0
unit path every probing pass already uses.  Test:
`xor_probe_forces_pinned_units` (the row difference `a⊕b=1`,
`a⊕b⊕c=0` pins `c=1` end-to-end).

**The bug this found in the dormant module is the landing's real value**:
`GF2Row::xor_with` extended its `sources` list on every reduce step, and
through Gaussian chains the accumulated lists grow
**Fibonacci-exponentially** — measured on mdp-28-14's 373 constraints:
12 ms at constraint 150, 7.8 s at 250 (the row bit-ops are nanoseconds).
Any future consumer of `add_constraint` would have hit this; the lists
are now capped (`SOURCE_CAP = 64`) with the reason-consumer caveat in
the comment.

**Measured (quiet, deterministic counters)**: the probing derives units
(summle 154, g2-slp 57, crypto1 14) but the corpus effect is
flat-to-negative — summle_X4044 62 927 → 124 584 (2×), pb_300
29 101 → 92 621 (3.2×), mp1 112 030 (1.05×), g2-slp 336 934 (0.98×),
mdp-28-14 still TO with 0 units (its system is underdetermined and
single-var probes do not conflict).  0 verdict mismatches.  The honest
limitation: this probing only *fires* when a row becomes single-var or
falsified under a level-1 probe; CryptoMiniSat's leverage comes from
folding every assignment during search with conflict clauses fed back
into CDCL — the integration that remains the recorded multi-session
lever.  Default stays off; `NIXIE_XORPROBE` joins the infrastructure.

## 19. Thirteenth follow-up (same day): the full in-search integration lands — CryptoMiniSat shape, honest neutral verdict

`NIXIE_XORSEARCH=1` (default off): the GF(2) matrix lives on the Solver
through search; every assigned trail literal folds into it (occurrence-
indexed — the first version scanned all rows per fold and made summle/mp1
wall-bound with *fewer* conflicts than baseline); a row that becomes
single-var derives its last variable as a **propagated literal with a
materialized entailed reason clause** (the negated folded literals plus
the implied literal — full CDCL participation: analyze resolves against
it, learned clauses are entailed); a falsified row surfaces exactly like
a CNF conflict through `propagate().or_else(xor_search_step)`.  Backtracks
roll the folds back through the central backtrack functions (fold
indices are strictly increasing → exact LIFO restore).  Proof-gated
(parity reasoning is not RUP; entailed ≠ UP-derivable).

Mechanism tests: mid-search parity cascade with rollback-and-rederive
(a=b=true ⇒ c=true — the test's first expectation had the parity
backwards and the *implementation* was right), and a 200-trial
random differential (verdicts identical, models validate).

**Corpus A/B (54 files, 0 mismatches, off-arm identity 1.0000)**:
on-arm **1.0169** — inside the neutrality band, bimodal per file (mp1
0.20×, summle_X4053 0.83×, pb_300 0.37× quiet, g2-slp 0.94× vs
summle_X11112 7.7×, j3037 TO, and per-fold wall overhead that turns
near-cap files into TOs under load).  Two sound orderings of unit
emission (full row scan vs occurrence order) measured 562 k vs 21.5 k
conflicts on mp1 — the familiar trajectory lottery between valid
variants, noted for the record.

**Campaign close**: the XOR lever now exists end-to-end — detection
(delegated), GF(2) core (perf-fixed), phase seeding, probing, and the
full in-search propagation with CDCL feedback — every piece sound,
tested, env-gated, and measured.  The corpus verdict at this fidelity is
neutral-band; the remaining distance to CryptoMiniSat-class XOR wins
(adding XOR-aware learned-clause treatment, matrix reduction schedules,
dedicated XOR conflict analysis) is recorded as future work with the
P(descent)/verdict-checked protocols attached.
