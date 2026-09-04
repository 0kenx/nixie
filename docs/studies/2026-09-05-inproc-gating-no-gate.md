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

`OXIZ_INPROC_TRACE=1` (landed with this study) prints per scheduled round:
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
6s167-opt (545 k) than oxiz with inprocessing off (118 k).  Note what
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

Instrumenting why our structural numbers are so much weaker (oxiz on
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
