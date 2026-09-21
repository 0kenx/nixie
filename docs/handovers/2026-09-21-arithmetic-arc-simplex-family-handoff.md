# Handoff: the arithmetic arc — the fresh-seed map, the J5-blocking route, and the i504 regression; the simplex family is the next campaign (2026-09-21)

**Read `AGENTS.md` first — it is canonical.** This handoff succeeds
`docs/handovers/2026-09-20-arithmetic-arc-item96-handoff.md` (read its
defect-class list — every class there stays closed). The arc's memory is
`docs/studies/2026-09-13-lia-wide-literal-arithmetic.md` (items 1–96)
plus `docs/studies/2026-09-20-lia-branch-lemma-channel.md` (the branch
channel, the flip campaign, and the J5/i504 closures with their
addenda). Where they disagree, the studies win.

## What this stretch was

Three sessions emptying the post-flip residual:

1. **J5-(a)** (`a64738ff`): the MBQI certifier declines mixed Int/Real
   goals *without evaluating them* (a fragment refusal); the big-const
   gate discarded z3-valid models. The gate falls back to
   `model_certifies_assertions`.  37 members recovered, all models
   z3-validated.
2. **J5-(b2)** (`1c71f4d9`): `Div`/`Mod` had **no case** in the shared
   evaluator (opaque-leaf → `Undetermined`), and `combine_eq`'s
   collision-conservatism (correct for the refutation gates) blocked the
   certificate's positive `=`.  Exact Euclidean div/mod + the
   `EqCertify` mode.  16 more members recovered, all validated.
3. **i504** (`286f63bd`): the certificate was evaluating the LIVE
   tableau while gating the PUBLISHED model (item 90's popped-state
   divergence on the certificate side).  Model-first published-value
   reads, δ₀ instantiation (`certify_delta0`), and
   `CmpStrictCertify` with read provenance.  The fixed seeds fell to
   **1 member**.
4. **The fresh-seed hunt + the J5-blocking** (`82ad3417`): fresh seeds
   20262600–02 found 8 members (2 J5 + 6 simplex); the J5 gate now
   block-and-retries REFUTED candidates (the certificate's tri-state —
   declines are never blocked); both J5 members recovered.  AND the
   landing **restores the i504 regression**: the fold experiment's merge
   (`b010117f`'s ancestry) had silently dropped the functional half of
   `286f63bd` — the δ₀/strict-certify/provenance pieces — leaving i504
   `unknown` on main.  Measured, restored verbatim, re-verified.

The wrong-verdict ledger stayed empty the whole stretch: every
recovery's model was z3-validated by binding it as `define-fun`s and
re-solving the negation (`unsat`).

## The verdict map (measure before believing)

* **Fixed seeds 20261000–02 × 600**: **1 member** — `i129` (the simplex
  resource-limit tail; reproducer at
  `docs/studies/assets/2026-09-21/simplex-tail-i129.smt2`).
* **Fresh seeds 20262600–02 × 600**: **6 members — ALL the simplex
  pivot-cap / resource-limit family** (`smx-rl:make_feasible`,
  `smx-rl:check`, one with a branch request fired mid-decline).
  The arc's cumulative fixed-seed run: 150 → 110 → 91 → 79 → 75 → 73 →
  78 → 76 → 18 → 2 → **1**.

## Open items, in priority order

1. **The simplex pivot-cap / resource-limit family (6 fresh members +
   i129)** — the only named class left.  Entry points: the pivot cap in
   `make_feasible` (`smx-rl:make_feasible:L3183`), the check-level
   resource limit (`smx-rl:check:L3015`), and the interplay with the
   branch channel's reset-restart rounds (one member fires a branch
   request inside the decline).  Classify first: how many are the pivot
   CAP (a budget), how many are NOCOL-style eligibility, how many are
   wide-row repair — the probe recipe below tags them.
2. **The J5-(b1) root** (the dive-leaf divergence): the blocking route
   now converts refuted candidates into retries, but the SEARCH still
   produces violating candidates first.  Item 89's map (the div/mod
   axiom feeds loose at the dive's leaf) owns the root; the certifier's
   `[cert-refuse]` probe (the conjunct + outcome) is the decode tool.
3. **The regression audit discipline** (see the trap below): after any
   parallel landing touching `model_eval.rs` / `solver/mod.rs`, re-run
   the NAMED MEMBERS (i142, i116, i504, i393, i566 — the pins and the
   study list them) on the landed tree.  Two silent drops have now
   happened via merges of stale restyles.

## The instrument set (recipes)

* **`bench/differential/gap_survey.py`** (landed): fixed seeds
  attribute, fresh seeds hunt.  The stderr capture is live; the probe
  TAGS are session-local — rebuild from the inserter script recorded in
  the study (auto `fn:line` tags at every statement-position Unknown
  return + `resource_limit` write, in the arith solver, the simplex, and
  `solver/mod.rs`; hand tags: `lia:bnb-depth-budget`,
  `lia:bnb-node-budget`).
* **The certificate probes**: `NIXIE_DEBUG_QROUNDS=1` (the gate's
  prints — now includes the block-retry rounds);
  `model_certificate_status` is tri-state — probe the refusing conjunct
  by printing `other` in its match arm (**before** the mode restore —
  probes read after a restore report the restored state; this misled two
  decodes).
* **Model validation**: get-model → bind as `define-fun`s → assert the
  negated conjunction → z3 `unsat`.  The scripts are in the study's run
  logs (Python, ~20 lines); every recovery MUST be validated.
* Standing: `NIXIE_LIA_BRANCH_LEMMA=0` (the channel's opt-out),
  `NIXIE_LEAF_TRIPWIRE`, `NIXIE_BOUND_TRIPWIRE`, the atom-row canary.

## Traps that fired this stretch (do not repeat)

* **Parallel merges silently drop landed hunks.**  The fold experiment's
  merge dropped the functional half of `286f63bd` (only orphaned field
  declarations survived — it still COMPILED, and the pins that mattered
  weren't re-run on the landed tree).  After landing through a raced
  main: re-run the named members, not just the suite.
* **A blocked ff** (another session's uncommitted edits in your files):
  preserve their diff on a snapshot branch (`warm-start-restyle-snapshot`
  is the precedent — nothing discarded), free the tree, rebase, land.
  `git stash` is forbidden; `git push . HEAD:main` still requires a
  clean tree.
* **/media/data hits 100% mid-battery** (three times this stretch, twice
  killing a suite and a doc run with corrupt writes — "invalid template:
  should have a newline" is ENOSSC corruption, not a doc bug).  Keep a
  root-disk `CARGO_TARGET_DIR` for the doc gate; clean the worktree
  `target2/debug` aggressively; battery logs and binaries live in the
  worktree (`artifacts/`) or `precompile/`, never `/tmp` (age-wiped).
* **Probe placement**: probes read after a state restore report garbage;
  instrumentals must print before the mutation they observe.
* Main raced 4+ times per session; rebase late, ff fast, verify the
  landed tree (not the pre-rebase battery) when the race touches your
  files.

## Where things live

* The arc's memory: the two studies above (each addendum records its own
  probe recipes and measured deltas).
* Regressions: `nixie-solver/tests/arith_wide_literal_regressions.rs`
  (the branch-channel pin, the strict-stranding pair),
  `nixie-solver/src/solver/model_eval.rs` tests (the Euclidean table,
  the fail-closed classes, the collision/provenance semantics).
* Binaries: `precompile/82ad3417/` (the current tip's);
  `precompile/286f63bd/` (the i504 landing, for regression bisects).
* The residual reproducers: `docs/studies/assets/2026-09-21/` (i129);
  the fresh-seed members regenerate from seeds 20262600–02 (the survey
  is seed-deterministic).

The one-sentence version: **the fixed-seed survey is down to one member
and the fresh-seed six are a single named family — the simplex
pivot-cap/resource-limit class — with the instruments wired, the ledger
empty, and the one process rule that matters being to re-run the named
members after any raced landing in the evaluator files.**

## Regression audit executed (2026-09-21, evening) — the tree holds

Per this handoff's discipline (item 3), after the six parallel landings
that followed the tree-health validation (`c5e8026a`/`45a2c742` the
integer tableau Phase 1, `ac7f5404` the fused tokenizer, `4ca9a0e6`
the subsumption volume guard, `7d4adf4f` the UF-walk gating,
`fa30412c` the graph witness repair — several touching
`solver`/`simplex` surfaces), the named-member audit ran on
`precompile/fa30412c`:

* **Fixed seeds 20261000–02 × 600: exactly 1 gap member —
  `i129`** (`gap_s20261000_i129`, z3 `sat`), the documented simplex-tail
  cell, unchanged.
* **Fresh seeds 20262600–02 × 600: exactly 6 gap members** — the
  simplex resource-limit family, unchanged in count.
* **The named recovered members are all absent from both gap lists** —
  i504 (the twice-silently-dropped one), i142, i116, i393, i566 held
  through the churn.

No third silent drop.  The full battery context (suite, parity, gate,
differentials) is in `2026-09-21-tree-health-validation.md` at
`af07e5ad`; this audit extends it to `fa30412c`.
