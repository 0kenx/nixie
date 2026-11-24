# Theory assertion path — two equivalent-work landings (2026-11-24)

Execution of the first two items of
[`2026-11-24-kissat-z3-opportunity-audit.md`](2026-11-24-kissat-z3-opportunity-audit.md)
(A3 "O(1) arithmetic atom assertion" and C "hot-path env probes"), under the
audit's suggested order. Both are **equivalent-work**: the search trajectory
is bit-identical (conflicts / decisions / propagations / theory_props on every
probe cell), only the instruction count moves.

## Method

`perf stat -x, -e cpu_core/instructions/u` works on this box (the scan #1 note
that `perf_event_open` was blocked no longer holds: `cpu_core/instructions/u`
counts; only the `cpu_atom` sibling reads `<not counted>`). Instruction counts
are reproducible to ~2·10⁻⁷ across repeats of the same binary (wisa `xs_8_13`:
15 786 844 590 / 15 786 841 004), so a paired cand/base ratio is an exact cost
measurement despite the box load (24–61 on 20 cores during this session — wall
is printed for context only and is not used).

Corpus: 17 SMT cells under `smt-lib/non-incremental/` — QF_AUFLIA (storecomm, Rodin, `dlx-pc` at
`--conflict-limit 2000`), QF_LIA (CAV 25/40-vars, slacks, dillig), QF_NIA,
QF_UF (PEQ), QF_ANIA (one plain, one budget cell), QF_UFLIA (wisas `xs_8_13`,
Wisa `xs-10-18-2-2-5-3`, wisas `xs_10_20`), QF_UFIDL (`vlsat3_f30` at 3000
conflicts), QF_IDL (`vlsat3_c60` at 3000). Budget cells print `; stats:` on
the budget path; a cell that hits the `-t` time cap prints nothing and is
nondeterministic (dillig `25-28` was dropped for that reason).

The harness is now checked in as
[`bench/perf_gate/smt_probe_ab.sh`](../../bench/perf_gate/smt_probe_ab.sh) +
[`smt_probe_cells.txt`](../../bench/perf_gate/smt_probe_cells.txt): the
theory-path counterpart of `paired_instructions.sh` (whose corpus is pure CNF,
where no theory code executes). It fails on any verdict or counter mismatch.

Baseline: `target/release/nixie` rebuilt from `61fbec68` before any edit
(cargo confirmed up to date; the two later HEAD commits were docs-only).
Candidate arms were rebuilt in place (`cargo build --release -p nixie-cli`,
LTO, 3–4.5 min each).

## Landing 1 — `c02e2f4d`: per-call `getenv` on the bound writers

Seven `std::env::var_os("NIXIE_TRACE_TWRITES")` probes sat on
`assert_{le,ge,lt,gt}` / `record_prop_bound` / `prop_set_{lower,upper}`;
`NIXIE_S6_NDIR2` / `NIXIE_S6_PINNED` on every `propagate_bounds_in` pass;
`NIXIE_NO_RESTART_RESYNC` on every backtrack to level 0. Each `std::env::var`
takes the environment lock and walks `environ`. Read once per process now
(`OnceLock`), the fix the SAT kernel already received for the same reason
(`nixie_sat::env_flags`, the 2026-09-15 env-probe regression).

| cell | instructions cand/base |
|---|---:|
| dlx-pc (QF_AUFLIA, budget) | **0.4875** |
| vlsat3_f30 (QF_UFIDL, budget) | 0.9224 |
| wisas xs_8_13 | 0.9445 |
| Wisa xs-10-18-2-2-5-3 | 0.9536 |
| wisas xs_10_20 | 0.9653 |
| 10-13.slack | 0.9793 |
| avg20 (QF_ANIA) | 0.9872 |
| the other 11 cells | 0.9995–1.0005 |
| geomean (18 cells incl. the dropped noisy one) | 0.9485 |

`dlx-pc` spends half its instructions on those probes: it is a
theory-propagation-heavy AUFLIA goal whose every check runs the slice-6 pass.

## Landing 2 — `3f6f83b9`: the atom-slack memo

`assert_{le,ge,lt,gt}` rebuilt `row_key` (Vec + sorted inserts + gcd), a fresh
`LinExpr` through `add_term`'s linear scans, the canonicalization, a sort and a
**second** `row_key`, then hashed `(RowKey, TermId)` — on every re-assertion,
before `atom_rows` could answer. The z3 reference computes the bound once at
internalization (`theory_lra.cpp:1849 mk_bound` → `api_bound` in `m_bounds[v]`).

The memo `(reason term, bound kind) → {slack, lhs, rhs, single}` replays the
resolution; a hit requires an equal `(lhs, rhs)` request and a live row, which
is precisely the slow path's own `atom_rows` hit.

**The fork it exposed (recorded in the code).** The first cut was not
counter-identical on the wisa cells (conflicts 3357 → 3531). A per-assertion
trace diff located the first divergence: the same atom resolved to slack 547
(slow path) versus 352 (memo). Cause: `rehome_stranded_row_bounds` re-interns
recorded forms **directly through `cached_row_slack`**, never via `assert_*`,
so `atom_rows` moved to the fresh slack while the memo still named the
consumed one — and a consumed slack can *return to the basis* in a later
pivot, at which point the memo hit with the old row while the slow path used
the fresh one: two valid, different LP states. Fix: every `atom_rows` rewrite
drops the whole reason from the memo (`atom_slack_drop_reason`); a debug
oracle asserts hit ≡ `atom_rows` hit. `NIXIE_ATOM_SLACK_MEMO=0` restores the
slow path (`nonstrict` / `strict` select a half, for bisecting).

| cell | vs baseline (C + memo) | memo alone (vs C) |
|---|---:|---:|
| dlx-pc | **0.4304** | 0.883 |
| vlsat3_f30 | 0.9092 | 0.986 |
| wisas xs_8_13 | 0.9157 | 0.970 |
| Wisa xs-10-18-2-2-5-3 | 0.9244 | 0.969 |
| wisas xs_10_20 | 0.9486 | 0.983 |
| geomean vs baseline | 0.9375 (18 cells) | |

`arith_assert_parsed` also borrows the parsed terms now (it collected a `Vec`
per assertion); no cell moved.

## Bar (run on the final tree, both landings)

* `cargo fmt --all -- --check`; `cargo clippy --release --all-features
  --all-targets -p nixie-theories -p nixie-solver -- -D warnings` clean.
* `cargo nextest run --release -p nixie-theories -p nixie-solver
  --all-features`: **5291 passed**, 14 skipped, 0 failed, with the two
  documented pre-existing HEAD failures excluded
  (`choose_of_ite_picks_the_taken_branch`,
  `rejected_set_synthesis_cannot_publish_identical_choices` — the tla line's).
* `bench/z3_parity/run_parity.sh`: **171 Correct / 0 Wrong / 6 Inconclusive**
  (z3 4.16.0) — the standing result.
* `bench/perf_gate/run_gate.sh`: **PASS**, conflicts 1.000 / decisions 1.000
  (pure-SAT corpus: neither landing executes there).
* Binary cached: `precompile/3f6f83b9/nixie`.

## Traps recorded

* **`cargo nextest` fails fast**: one pre-existing failure cancelled 3 233
  pending tests on the first run (`2060/5293`); always pass the documented
  exclusion filter at this HEAD.
* **Debug-assertions builds of `nixie-solver` do not compile at HEAD**:
  `solver/trail.rs`'s exhaustive field audit (`debug_assert_scope_restored`)
  is missing the four fields today's BV commits added (`blastable_memo`,
  `constraint_sweep_pending`, `constraint_sweep_cursor`, `array_free_memo`).
  Release and release-test profiles are unaffected (`cfg(debug_assertions)`),
  so the dev-profile test run — where the simplex canaries and the new memo
  oracle live — was unavailable; the release suite plus counter identity
  carried the verification. Not touched here (the BV arc owns the fields).
* **A cache beside a cache must share its invalidation set.** The memo was
  correct for every `assert_*` path and still forked, because a third writer
  (`cached_row_slack` from the re-homing sweep) updated only the old cache.
  Any secondary index on solver state needs its drop hook at *every* writer
  of the primary, and a dev oracle that asserts the two agree.
* `/tmp/nixie-probe` held this session's harness and binaries; `/tmp` is
  age-cleaned on this box (trap from the 2026-09-20 handoff) — the harness
  now lives in `bench/perf_gate/`.
