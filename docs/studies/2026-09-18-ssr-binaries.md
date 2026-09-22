# The SSR-binaries cascade, fold parity — and the search gap finally isolated (2026-09-18)

Continuation of `2026-09-18-ite-gate-congruence.md`. Two questions were
open there: (1) is the fold trigger the bottleneck (the study's next-slice
1), and (2) where does the remaining 31× to kissat live on `bv_ILA`? Both
now have measured answers, and the second one changed shape completely.

## 1. The fold-trigger slice is refuted (measured, do not retry)

`NIXIE_ELS_FORCE=1` on the landed 1fd5b96f build (fold armed every
inprocessing round): bv_ILA **292,272** conflicts vs the default's
**302,978** — noise. The default sweep-triggered rounds already capture the
fold value; arming more rounds buys nothing on the winner and re-extracts
the known tax on the losers (circuit_48in64: 232,092 forced vs 133,085
default, the 2026-09-05 study reproducing). The density-gate idea was
already falsified pre-ITE (`2026-09-06-els-gate-density-study.md`, inverted
separation). **Closing this thread entirely.**

## 2. Where kissat's remaining advantage actually lives (knockouts)

| kissat config | conflicts on bv_ILA |
|---|---|
| full | 9,465 |
| `--preprocessprobe=0` | 9,456 (probe irrelevant) |
| `--congruenceonce=1` | 9,305 (mid-search re-runs irrelevant) |
| `--congruencebinaries=0` | 790,230 (**83×**) |
| `--congruenceites=0` | 871,519 (92×) |
| `--congruence=0` | 1,213,731 (128×) |
| nixie 1fd5b96f (default) | 302,978 |

We already beat every single knockout arm. The two big carriers (ITE gates,
landed; `extract_binaries`, missing) compose multiplicatively. Note the
leverage: kissat's `extract_binaries` derives only **312** binaries in its
first round on this file — 312 clauses carrying 83× — because they complete
partial gate patterns that then cascade through the closure.

## 3. The prototype (env-gated, default off)

- **`extract_binary_resolvents`** (kissat `extract_binaries`): one bounded
  pass of ternary×binary self-subsuming resolution — `(a∨b∨c) ∧ (¬a∨b) ⊢
  (b∨c)` — adding each resolvent as a learned binary with the
  `clause_hyper` provenance flag (transred exemption, the hyper-binary
  precedent) and BIG registration at attach. Runs inside
  `substitute_equivalent_literals_round` before gate detection
  (`NIXIE_SSR_BIN=1`).
- **Pre-search fixpoint arm**: one bounded (≤8 rounds, fixpoint-exit) ELS
  loop before the conflict-scheduled elimination — kissat's preprocess
  order (congruence+substitute first, elimination after)
  (`NIXIE_ELS_PRESEARCH=1`).

Measured cascade on bv_ILA (armed): pre-search SSR extracts **7,906**
resolvent binaries (vs kissat's 312 — our BIG includes probing's
hyper-binaries, so more SSR partners exist), gate count grows
129,722 → **161,708** (99,776 → 133,238 ITE), and the fixpoint converges to
**79,306 cumulative substitutions — exceeding kissat's 50,931 merges**.
The XOR arm's zero on this file is correct (0 complete 4-clause patterns in
the raw file; kissat's 7,530 XOR gates emerge during its closure from
merge-added binaries).

## 4. The headline measurement: preprocessing parity, search gap isolated

With the arms armed, dump the residual at elimination entry (the
`NIXIE_DUMP_ELIM_ENTRY` hook) and solve it with kissat:

| solver | conflicts on the SAME residual file |
|---|---|
| kissat | **9,430** |
| nixie (search on its own residual, in-place) | 340,486–354,947 |
| nixie + `NIXIE_SAT_BVE=0` | 155,417–172,203 |

**Our congruence fold now produces a residual kissat solves in 9.4K
conflicts — statistically identical to kissat's own full pipeline (9,465).
The preprocessing collapse is at parity. What remains is a pure
search-quality gap of 16–36× on the identical formula**, plus a measured
BVE interaction: our conflict-scheduled elimination *destroys* the collapse
(355K with BVE vs 172K without on the folded formula — the 36M-resolution
phase re-entangles what the fold untangled; kissat's eliminate barely fires
on this file because substitute already did the work).

This is the controlled experiment the search-quality arc was missing: a
fixed 366K-clause / 131K-var formula where kissat needs 9.4K conflicts and
we need 155–355K. Every knob (phase quality, restart shaping, chrono,
trail reuse, clause learning) can now be probed on it without
preprocessing interactions. The file is reproducible from
`NIXIE_DUMP_ELIM_ENTRY` + the two arms.

## 5. Why this lands default-off

The composition is net-negative *today* on the target family: bv_ILA
354,947 armed vs 302,978 default — because the BVE elimination runs right
after the fold and undoes it. Making the composition win needs the
BVE-after-fold policy (skip or budget elimination when the pre-search fold
collapsed the formula; the `eliminating_presearch` fixpoint is the natural
gate). That is the next slice, and it needs the powered-experiment
discipline (the BVE-averse families from the fold study are the risk).

Both arms land env-gated, default off, with test-knob overrides for the
unit tests (`test_knobs::set_ssr_binaries` / `set_els_presearch`) —
bit-identical default trajectories verified on the five-instance gate
corpus band.

## Soundness

4 unit tests (resolvent derivation + idempotence, unsat/sat soundness with
the level-0-skip documented, no-op on partner-free formulas, the armed
end-to-end fold with model validation and a forced-inequality refutation).
1,700 structured differential fuzz instances with both arms armed against
the landed base + kissat tiebreak: **0 verdict disagreements**. The
resolvent addition is a resolution consequence of two live clauses (RUP via
its parents — the same proof shape the hyper-binary path emits).

---

## Addendum (2026-09-21, fourth session): the search-quality gap is CLOSED — and the study's kissat number drifts

Re-run of §4's controlled experiment on today's tree (same instance,
same `NIXIE_DUMP_ELIM_ENTRY` machinery, the fold stack armed to freeze
the residual):

| solver | conflicts |
|---|---|
| kissat on OUR residual (identical bytes) | **7,645** |
| nixie default on OUR residual | **7,787** (deterministic ×3) |

**Search quality on the frozen formula is at parity** (within 2%) —
the §4 "pure search-quality gap of 16–36×" no longer exists; the
intervening landings (the branch-channel default, everything else)
closed it.  The residual experiment remains the cleanest probe surface
in the repo, now with no gap to chase on this anatomy.

**A provenance correction (caught in review)**: this study's §2 table
quotes kissat full-pipeline at 9,465 conflicts on bv_ILA; tonight's
clean run of the same `../temp/kissat` build (binary dated Sep 6,
predating the study) on the same instance reads **8,399**.  The 9,465
is unreconciled — most plausibly a non-default option row leaked into
the "full" line of the knockout table.  Treat 8,399 as the reference
number.  Tonight's end-to-end, apples-to-apples:

| arm | conflicts |
|---|---|
| kissat (defaults) | 8,399 |
| nixie default | 16,023 (1.91× behind) |
| nixie fold stack (opt-in: `NIXIE_SSR_BIN=1 NIXIE_ELS_PRESEARCH=1`) | **8,098** (3.6% ahead) |

The composed-stack flip decision (refused earlier today on the Carry
family band) is unchanged by this — but the prize is now stated
correctly: **the opt-in stack is at parity-or-better with kissat
end-to-end on this anatomy**, and the default's 1.91× is the cost of
that refusal.
