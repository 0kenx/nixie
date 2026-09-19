# Handoff: the 2026-09-19 queue executed to completion — fold, stamps-item, assert, caps; the TLA+ front end's bags slice

**Date:** 2026-09-19 (final session of the arc; supersedes the open-items
lists of `2026-09-19-next-session.md`, `2026-09-19-bags-fold.md` and
`2026-09-19-tla-bags.md`)

## The queue from `904c366b`, item by item — all closed

| # | item | landed | state |
|---|---|---|---|
| 1 | `bag.fold` | `aaf3074a` | done: ground-multiset unroll + exchange-law gate + declined-fold model certification; CVC5 differential 4 seeds 0 mismatches |
| 2 | delta-propagation invariant | `aaf3074a` | item 85 in the wide-literal study: invariant mapped, boundary argument written, `NIXIE_DELTA_VERIFY` canary release-runnable and self-healing; open as a *proof* obligation only |
| 3 | bag deep-shape perf | — | **closed as not-worth-it with evidence**: the gate ("only if a corpus ever grows bags") is now *proven absent* — the TLA+ corpus study found 7 bag files (1 with a BMC triple, blocked on PlusCal), bag usage flows through the function encoding, and no other corpus has a bag surface. The fuzz timeout share is synthetic-shape cost. Reopen only if a real bag corpus appears. |
| 4 | `(assert x)` non-Bool | `aaf3074a` | parse-level rejection (Z3/CVC5 parity) |
| 5 | cap re-measurement | `9fa55909` | **done, verdict: keep every cap** (`docs/studies/2026-09-19-cap-survey.md`) — the gate condition (TLA+ green) was verified, the survey ran, 0 corpus verdicts lost to any firing; caps now observable (`NIXIE_DEBUG_CAPS`) and overridable (`NIXIE_CAPS`) for any future re-check |

## The TLA+ arc (`eb6ce2da` + this session's fix)

The `Bags` vocabulary is end to end (TLC-exact evaluator, typed,
desugared lowering, BMC for ground construction + symbolic reads); both
TLA+ parity gates are green and the corpus question is answered: TLA+ is
not a bag-theory workload today, and the `Bag`-sort bridge is the named
next step *if* that ever changes. The `--help` trap that made the corpus
look absent is fixed in both `run_parity.sh` scripts (usage printed,
exit 0 — the next session won't repeat the misdiagnosis).

## What is genuinely open, in value order

1. **The PlusCal wall** — the one bag-adjacent corpus spec with a BMC
   triple (`Nano.tla`) is blocked on PlusCal lowering, not bags. PlusCal
   translation is the single biggest coverage lever on the TLA+ side
   (many `tlaplus-examples` specs are `.tla` + PCal bodies).
2. **The delta-propagation proof obligation** (study item 85) — the
   boundary argument is written, not mechanized; the canary is the
   standing tripwire.
3. **The lambda-shaped function encoding or `Bag`-sort bridge** — the
   two honest declines in TLA+ bag BMC (state-bag updates,
   `DOMAIN`-quantifiers). Design-sized; only worth it with a workload.
4. **`structurally_equal`/`alpha_equivalent` conservatively return
   `false` for two `BagMap`/`BagFilter` terms** (noted in the fold
   handover; `BagFold` has a correct dedicated arm). Optimization-loss
   only, never unsound — a tidy small fix if someone is in those files.
5. **Bag deep-shape perf** — stays closed (see item 3 above) unless a
   corpus appears.

## Environment notes carried forward

- The disk on `/media/data` oscillates 93–100%; all builds this arc ran
  under `CARGO_TARGET_DIR=/tmp/…` (deleted after each landing), and both
  TLA parity scripts now honor `CARGO_TARGET_DIR` themselves.
- `run_eval_parity.sh`/`run_parity.sh` answer `--help` with usage now.
- The `scope_rebase` ledger test remains load-sensitive: 180 s nextest
  cap under multi-agent load, ~92 s standalone. Re-run before believing
  a failure.
- Precompile entries for this arc: `aaf3074a` (solver), `eb6ce2da`
  (nixie-tla), `9fa55909` (solver).
