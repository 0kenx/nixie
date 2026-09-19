# Pre-search factoring: the oddball 125× is one landing away from default (2026-09-18)

Continuation of the congruence arc (`2026-09-18-{ite-gate-congruence,
ssr-binaries,xor-congruence}.md`).  With bv_ILA at parity, the remaining
standing-table gap concentrated in `oddball` (still 16.8× after the XOR
landing: 1,718,696 vs kissat's 102,396 conflicts).

## The anatomy (kissat profile on oddball)

Shallow search (1.81 dec/conf — no deep diving), congruence irrelevant
(62 merged vars), but **factored: 2,353 = 21% of variables** and vivify
66%-of-checks.  Our `factor.rs` port exists, is kissat-faithful
(`2026-09-07-factor-port.md`), and was measured **NO-GO as a default**
on the sc24f corpus (1.060× geomean, solved 50→48) — with the mid-search
rounds included in that arm.

`NIXIE_FACTOR=1` on oddball: 1,718,696 → 17,865 conflicts (96×).  But
the powered re-run on the current 30-instance corpus showed the old
verdict's other half intact: **b21 and b22 flip 10/10 solved → 0/10**
under full factor.

## Where the b21/b22 damage lives — and the discriminator

b21 under factor: 198,393 conflicts (only 1.15× more than default's
172,092) at **60× the wall** — and `bva_n=0` in every round: the
mid-search factor rounds introduce NOTHING on b21; the damage is the
rounds themselves (per-round `FactorState` allocations over `2·V` codes
and the ~1M-slot `qmark`/`dead` vectors + the chain scans, a growing
25–75 ms/round slot cost, and a trajectory shift with zero yield).

Meanwhile the winners' introductions all land **pre-search**: oddball
1,398, Break_t 144, x9 368; **b21/b22 introduce zero pre-search** — the
pre-search one-shot is inert-by-construction there.

`NIXIE_FACTOR=1 NIXIE_FACTOR_PRE=1` (mid-search suppressed) is exactly
that split — and it measured:

- b21 @seeds 1–3: **bit-identical** to default (161,615 = 161,615,
  192,761 = 192,761, 173,688 = 173,688).
- oddball: 11,920 conflicts / 0.6 s — better than full factor (the
  mid-search rounds were net-harmful there too).

## The powered experiment (10 seeds × 30 instances, correct arms)

| | default | factor+PRE |
|---|---|---|
| conflicts geomean (paired) | 1.0 | **0.6317** |
| solved-at-cap | 268 | **268** (no losses; b21/b22 10/10) |
| verdict mismatches | — | **0** |

Per-family: oddball **0.008×**, Break_t 0.067×, x9 0.658×; the inert
band exactly 1.000 (b21, b22, circuit, bv_ILA, s38584, nla, Carry);
worst cells Break_12_30 1.392 and Iter22 1.120 — every cell solved, and
dwarfed by the wins.  (A first harness run recorded b21/b22 as 0/10 —
both arms pointed at the shared `target/release` binary, so the "PRE"
arm ran full factor.  The rerun pinned BASE to the `570d8ad5`
precompile and CAND to the worktree build.  Also: corpus tests in
worktrees need the `ln -s` corpus symlinks — the `nixie-testcorpus`
header's warned failure mode sent this session on its own short bisect.)

## Landing

`cadical_config.enable_factoring: true` (the CLI fast-path default;
`SolverConfig::default()` — the SMT path — stays off) and the mid-search
factor rounds gated off by default (`factor_mid_rounds_enabled`, opt-in
`NIXIE_FACTOR_MID=1` for the full kissat shape).  The pre-search pass is
self-gating: zero-introduction formulas keep bit-identical trajectories
(measured on b21 across seeds).

## Session standing after this landing

The handover's gap table, re-measured: bv_ILA 27× better than session
start (below kissat's conflict count), oddball 16.8× → ~0.6 s,
GP_190/normalised families now solve at 0 conflicts, 5447072093nw 3.2×,
nla-digbench 0/10 → 10/10.  Remaining named slices: gate-based
subsumption + post-fold dedup, the armed-congruence composition
re-measure, n-ary gates, and the Break_12_30 1.39× cell as the next
factor-schedule tuning candidate.
