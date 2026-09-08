# Handover: Kitten Sweep Port (Equivalence-Content Deficit on the Tail Class)

## Context

The 2026-09-07 throughput campaign closed its T3 thread with a precise
negative: **equivalence substitution's win/loss is not predictable from any
observable** — four gating studies falsified every candidate (online round
signals, congruence-gate density, one-shot-vs-fixpoint placement, and
parse-time binary-SCC mass; the last two *inverted*: every anchor-winner has
zero surface structure, the biggest losers have the most). The SCC study's
closing line is this port's mandate:

> Any future ELS work must … build the missing kissat simplification-fixpoint
> *content* (kitten sweep — reference-priced at ~1 % corpus geomean for
> kissat itself, `--sweep=0` 2026-09-05 §8), not a gate.

The evidence that content is what's missing:

| file | nixie default | nixie ELS one-shot | cadical | note |
|---|---|---|---|---|
| 6s167-opt | 62 241 | 42 681 (0.69×) | **16 654** | cadical substitutes **12.5 % of all variables** there; we substitute 0 by default |
| FmlaEquivChain_4_6_6 | TO at 60 s | **solves** (311 k conflicts via the ELS arm) | solves | an equivalence chain by construction — folds only under pass content |
| x9-09054 | — | **0.26×** under `ELS_PRE` | — | pre-arm anchor winner |
| stable-300 | — | 0.47× | — | pre-arm anchor winner |

Our ELS (`nixie-sat/src/els.rs` + `solver/equiv.rs`, ~950 lines) finds
equivalences via congruence closure over AND-gate structure plus binary-SCC
— a *static* approximation. kissat's sweep **proves equivalences with an
embedded SAT solver** over a bounded simulation environment, finds backbone
literals, refines partitions, and applies representatives through a budgeted
substitution pass. It is the reference mechanism for exactly the class where
our static version wins big, and it is **unclaimed** — no study or branch in
the repo touches `sweep.c`/`kitten.c`.

## What Must Be Ported (from `../temp/kissat/src/`)

### 1. `kitten.c` (2 877 lines) — the embedded solver

A self-contained small CDCL solver with its own watch lists, phases and tick
accounting. API surface (`kitten.h`) is the port contract:

- lifecycle: `init / clear (reset trail, keep clauses) / release`
- problem: `unit / binary / clause / clause_with_id_and_exception`
  (the id+exception form is how the sweeper maps kitten antecedents back to
  main-solver clauses), `assume`
- budget: `set_ticks_limit / no_ticks_limit` — **ticks, never wall**
- solve/status/value/fixed — `solve` returns 10/20/0 under the tick budget
- phase control: `flip_phases / randomize_phases / shuffle_clauses`
- `track_antecedents` — required by backbone/sweep paths

Port notes: it is deliberately *not* our main solver — no arena, no
inprocessing, no proofs. A faithful minimal Rust CDCL (~1 500 lines expected;
we have all the primitives: `Trail`, heap VSIDS, watch lists) beats trying to
subclass `Solver`. Keep it in a new module (`nixie-sat/src/kitten.rs`) with
its own tick counter summed into `SolverStats` (kissat: `kitten_ticks`) —
the effort scheduler needs it.

### 2. `sweep.c` (1 724 lines) — the sweeper

Classic SAT sweeping with kissat's budget shape:

- **environment**: for each candidate variable, the clauses of its depth-≤2
  cone, capped (`sweepclauses = 1024` env clauses, `sweepmaxclauses = 32 768`
  total, `sweepdepth = 2`); encoded into kitten once per round
  (`sweep_clause` / encoded counter).
- **candidates**: literal pairs (a, ¬b) queued by rank; per candidate,
  `kitten_assume(¬(a≡b))`-shaped test solves under the **shared**
  round tick budget (`sweepeffort = 100 per mille` of the round's effort
  budget); SAT witness ⇒ flip-driven partition refinement
  (`sweepfliprounds = 1`), UNSAT ⇒ equivalence proved.
- **backbone** literals (`sweep_backbone_candidate`) and **partition/core**
  refinement rides the same solves.
- `sweepcomplete = 0` by default: one pass per round, not a fixpoint.

The candidate *ranking* is the semantic core — that is what the matched null
must scramble (below).

### 3. `substitute.c` (617 lines) — applying representatives

Units (assign + propagate + inconsistent ⇒ UNSAT with empty-clause proof),
clause rewriting through `repr[]`, weakening, and **proof emission**
(`CHECK_AND_ADD` / deletions). **Do not rewrite this layer**: nixie already
has a sound substitution application in `solver/equiv.rs` (assertion-level
ledgers, BIG edge purge on retraction, DRAT deletes, arena-safe rewrites —
hardened through the 0.3.x soundness sweeps). Route sweep output into the
existing application path; port only what is missing (backbone units,
partition classes).

### 4. Integration point: the effort-scheduled inprocessing rounds

kissat runs the sweep inside its reduce/inprocess cycle under
`sweepeffort` per-mille budgets — **nixie already has that machinery,
default ON** (`docs/studies/2026-09-07-inproc-effort-schedule.md`: round
budgets are a fixed per-mille of search work since the last round,
log-growing interval). Add `sweep` as a budgeted round component next to
subsume/vivify/BVE; `NIXIE_SWEEP=0|1` env arm for A/B, default off until
the gates below pass. Pre-search variant (`preprocesssweep = 1` in kissat)
maps to the existing pre-search pass slot.

## Reproduce These Numbers First (calibration, ~half a day)

All with `precompile/<latest>/cnf_solve` (cores 10–19, counters never wall):

1. 6s167-opt: default 62 241 conflicts; `ELS=1` 42 681; cadical 16 654 with
   `substituted: 582 (12.54 %)`. The port's target is the 42.7k→16.7k span.
2. FmlaEquivChain: default TO at 60 s; the ELS content solves it. Sweep
   should fold it *inside the default config*.
3. kissat's own price: `../temp/kissat/build/kissat --statistics` on the
   corpus sample — `sweep_ticks`, `kitten_ticks`, substitution counts. The
   ~1 % corpus-geomean reference price is the budget calibration envelope:
   if the port costs materially more than kissat's, stop and find out why
   before any A/B.
4. `NIXIE_INPROC_TRACE=1` rounds telemetry — where sweep rounds will sit.

## Methodology (non-negotiable, all paid-for lessons)

- **Matched null**: identical kitten work — same environment, same number of
  test solves, same tick consumption — with the candidate *ranking*
  scrambled (deterministic hash order instead of cone-rank). The semantic
  content under test is candidate selection + proved equivalences; the null
  keeps the machinery and cost. (Null-arm lesson on record: verify the null
  actually fires — compare kitten solve counts between arms — before
  trusting any treatment/null ratio.)
- **Gates**: ≥5 seeds, conflicts-to-verdict on the anchor set above, AND the
  54-file × 5-seed 60 s standing screen (solved-at-cap, **0 verdict
  disagreements**). The 2026-09-04 bundle lost 50→42 standing while winning
  the tail 2–6× — the sweep must clear both, or land effort-gated below the
  regression threshold. Landing bar follows `docs/BENCHMARKING.md` §
  enablement rule verbatim.
- **Never instructions as the primary metric** (PGO: −7 % instructions,
  0 % cycles). Ticks/conflicts/solved-at-cap only; wall is a sanity check.
- **Two-direction identity protocol**: `NIXIE_SWEEP` off must be
  trajectory-identical to base (corpus sweep, not one file), and
  ON(a) ≢ ON(b) on a real counter (kitten solve counts) — the inert-knob
  and fake-SEED incidents are both on record.
- **Soundness**: substitution retraction must ride the existing
  assertion-level ledgers (see `check_hyper_binary_resolution`'s two-ledger
  comment for the pattern); proofs must emit the substitution derivations;
  a SAT-core change is an SMT-path change — ship with a fresh full
  differential and `./bench/z3_parity/run_parity.sh` (the trie-vivify
  lesson).
- **Git protocol** (the tracking incident is on record): check
  `git branch --show-current` == `main` before *every* commit/merge in the
  shared checkout; after landing, verify
  `git merge-base --is-ancestor <sha> main` **before** removing any
  worktree or branch. Worktrees vanish on this box — commit early, in the
  worktree.

## Expected Outcome and Kill Criteria

Realistic target: 6s167 toward cadical's 16.7k (close half the 42.7k→16.7k
span), FmlaEquivChain-class files folded by the default config, corpus
standing not worse, total price ≈ kissat's ~1 % envelope.

**Kill criteria** (pre-registered): if a faithful port at kissat's budgets
measures corpus-negative while tail-bimodal — the same shape as the ELS
one-shot and the preset-ablation arms — then record and stop: the
conclusion would be that per-file bimodality is intrinsic to substitution
*content* on this corpus, the remaining conversion path is trajectory
diversity (already measured: plain seeds dominate every within-cap
portfolio), and the tail class should be handed to per-class config
selection instead.

## Key Files

- Reference: `../temp/kissat/src/{kitten.c,kitten.h,sweep.c,substitute.c}`,
  options in `options.h` (`sweep*`, `preprocesssweep`), integration cadence
  in `internal.c` (where `kissat_sweep` is called from reduce/inprocess).
- Ours to reuse: `nixie-sat/src/solver/equiv.rs` (substitution application,
  soundness-hardened), `nixie-sat/src/els.rs` (current static ELS),
  `solver/learn.rs` effort-schedule rounds, `big.rs` CSR (environment
  structure), gate congruence (`detected_gate_count`, GATE_COUNT=1 knob).
- Study lineage: `docs/studies/2026-09-05-inproc-gating-no-gate.md`,
  `2026-09-06-els-gate-density-study.md`, `2026-09-07-els-scc-gate.md`,
  `2026-09-04-inprocessing-standing-corpus.md`, and the campaign doc
  `2026-09-07-throughput-campaign.md` (T3 sections + harness notes).
- Corpus: `precompile/corpus-sc24f/` (54-file standing; the anchor files'
  hashes are in the campaign doc), binaries convention in
  `./precompile/<sha>/`, results store `bench/suite/scripts/benchstore.py`.

---

## Status: CLOSED — ported, landed default-on, calibrated (2026-09-08)

Outcome (full record: `docs/studies/2026-09-08-kitten-sweep-port-calibration.md`,
commits `47d090c`…`c9cfe71`):

- **Port complete**: `kitten.rs` (embedded CDCL, full `kitten.h` API) +
  `solver/sweep.rs`; application rides the existing ELS substitution
  round as this handover mandated.
- **Landed default-on** via the enablement rule. Standing corpus
  (54 × 10 seeds, 60 s, 0 verdict disagreements at every step):
  base 316 → sweep@100 ‰ 351 → **sweep@400 ‰ + yield-delay 363**
  solved-at-cap (final config).
- **Anchors**: 6s167-opt 65 873 → **33 561** conflicts (10-seed gm; the
  half-span target ≈ 29.7 k — nearly closed; kissat 19 164, cadical
  16 654). FmlaEquivChain 2/10 → **8/10** solved (reference parity on
  cost). x9-09054 remains cap-boundary.
- **Price**: matched to kissat's absolute envelope where productive
  (400 ‰ ≈ 2.5–3 M kitten ticks on 6s167 vs kissat's 3.5 M), and
  *below* the initial default where inert (yield-delay feedback:
  kissat `delays.sweep` port).
- **Kill criteria note**: Part 1's "corpus-negative" verdict was a
  load-biased 5-seed screen (the armed arm pays ~2 % instructions and
  lost borderline cells under a concurrent build); the quiet 10-seed
  re-measure reversed the sign. The pre-registered bimodality finding
  stands: the faithful cone-ranking vs its matched scramble is
  corpus-neutral (1.017) and per-family bimodal — the ranking-variant
  question is the recorded open follow-up.
- **SMT path**: structurally sweep-free (embedded-solver opt-outs +
  sticky theory gate) after the landing differential caught a real
  wrong-unsat (pr30) in the first wiring — the fix chain is the
  addendum in the study doc.
- **Remaining gap lever**: the one un-ported deviation — kissat's
  immediate per-equivalence application (`substitute_connected_clauses`)
  vs our round-end fold. On 6s167 kissat folds 14 % of variables; we
  prove ~94/round. That is the next mechanism-level lever if the 33 k →
  19 k span is to close further.
