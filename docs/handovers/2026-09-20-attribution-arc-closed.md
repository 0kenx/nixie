# Handoff: the attribution/perf-gap arc closed — the ledger, the live repair on main, and the campaign map the next sessions inherit (2026-09-20)

**Read `AGENTS.md` first — it is canonical.** This closes the arc that
started at `docs/handovers/2026-09-19-wide-lp-post-landing.md`: every
item now carries an explicit verdict in the **closure ledger** at the
tail of `docs/handovers/2026-09-19-attribution-session.md` — read that
ledger before re-opening anything it names. Companion close-outs by the
other owners: `2026-09-20-smt-perf-arc-executed.md` (the perf table),
`2026-09-20-arithmetic-arc-item96-handoff.md` (the arith campaign).
Where they disagree, the owning study wins.

## URGENT, for the SAT owner: your flip had a landed panic; the unblock repair is on main

The slack-CSR flip (`032b687f`) panicked **hard on the standing
`pete_5s` fixture, release included** — `nixie-sat/watched.rs`
`scan_split`'s `end − start` underflowed (debug) and the wrapped length
tripped `split_at_mut` (release; the CLI aborted; the pre-flip binary
answers the correct `unsat`).  Root cause: `span_start`/`prim_end`
`.unwrap_or(0)` defaults are independent — a code present in one table
and absent from the other (they resize at different times) computed
`start > 0, end = 0`.  **`9bd34785`** (verified: both worlds `unsat`,
the both-present invariant now `debug_assert`ed and silent on the
fixture, full bar green) implements the doc comment's own degenerate
contract: missing `prim_end` ⇒ empty span.  A `csr-revert` branch and a
`/var/tmp/nixie-pete` worktree exist as of this writing — **check
whether the revert predates the repair before reverting over it**; the
repair is the smaller fix and the gate passes through it.  Also swept
into that landing (called out in its message): mechanical `cargo fmt`
repairs of `63cae24b`'s branch-channel code, which landed fmt-dirty.

## Where the tree stands

Main at `6f86a697`; gate BASELINE re-pinned to `3d271157` (the fourth
pin this arc — re-check `bench/perf_gate/BASELINE` before any gate
run).  Binary `precompile/65852b45/`.  The wrong-verdict ledger is
empty; the last full validation at `b49b9242` recorded 7 differential
seeds, the panic sweep, and a **399-pair stratified SMT-LIB verdict
screen vs z3 (0 disagreements)** in the attribution-session handoff.

This arc's landings (all full-bar): the B&B-leaf re-scan (a live false
`sat` closed at the root), the Hermite widening (gap survey 150 → 104;
the UNSAT-side parity class retired), `eval_linear` exact, the
`RealConst`/model-entry spellings, `bag.map`/`bag.filter` shape
equality, the audible delta-verify canary + the 1 917-file sweep, the
let-sharing printer, `ctx_simplify` + its context-restricted memo,
`Command::Unsupported`.

## Open items, by owner, in their value order

1. **Arith (in-flight, worktree `nixie-wt-r3`): rung 3** — the
   default-flip campaign for `NIXIE_LIA_BRANCH_LEMMA` (≥10 seeds,
   per-family, benchstore per `docs/BENCHMARKING.md`; the 16-recovery
   vs 6-slow-flip decision).  Then **J5** (51 members; items 89/91's
   map, the `[cert-false]`/`INTERP` probes).  Their handoff owns the
   details.
2. **SAT**: post-flip fallout (the repair-vs-revert decision above);
   the pivot-storm study's LP-cost layer (fraction-free rows) is the
   named prerequisite for the CAV family.
3. **The `solve_eqs` pre-pass** (handed off with complete diagnosis in
   the perf-gap study's addenda): the nec-smt member's residual is a
   self-referential priority-select; the memo proved the cost is the
   case splits, not sharing.  Entry points: guard-equality elimination
   before the walk, or split ordering.  Time-box it — it is the third
   probe into the same 9 wall-time members.
4. **ndir2 re-measurement** — still gated on a stable baseline.
5. TLA's PlusCal wall; the delta-propagation mechanized proof — their
   owners' standing items.

## The instruments (all landed, all one-command)

* `NIXIE_GAP_PROBE=1` + `gap_survey.py` (stderr capture landed) — the
  gap attribution table in one run.
* `NIXIE_DELTA_VERIFY=1` — the audible canary (a reconciliation prints
  `[delta-verify reconcile …]`).
* `NIXIE_BOUND_TRIPWIRE=1`, `NIXIE_DEBUG_CAPS`/`NIXIE_CAPS`,
  `NIXIE_LIA_BRANCH_LEMMA`/`_NULL`, `NIXIE_CSR_B=0` (the legacy-world
  escape hatch).
* The boundary-literal SHAPES live in `wide_fuzz.py`/`mixed_fuzz.py` —
  extend shapes, not seeds.

## Process notes — the trap list this arc actually hit

* **A piped command masks its exit status**: `git merge --ff-only | tail`
  reported success while the merge failed; the branch was deleted
  before the miss was noticed (recovered from the object store by sha).
  Pipe to a file, or check `${PIPESTATUS[0]}`.
* **Worktrees need the corpus symlinks** (`smt-lib satcomp2024
  satcomp2025 satlib`) or the corpus tests fail as `[corpus-missing]` —
  environment, not code; hit twice this arc.
* **Never symlink `precompile` into a worktree** — a dir-only
  `.gitignore` misses symlinks and a landing once replaced the cache
  with a broken self-symlink.  Both forms are ignored now; the
  convention is `cp` into `precompile/<sha8>/`.
* **Disk**: both disks oscillated to 100 %; debug-info builds are the
  multi-GB offenders (`CARGO_PROFILE_DEV_DEBUG=0` keeps debug
  assertions at a fraction of the size); don't build debug in `/tmp`;
  a disk-full build can be silently wrong — never trust a verdict from
  a binary built under pressure.
* **Load flakes**: `scope_rebase` (the ledger test) times out at
  nextest's 180 s cap under multi-agent load (~92 s standalone) —
  re-run suspects at `-j1` before believing red.
* **Test-goal generation traps** (measured, in the perf-gap study):
  let-bindings in scope order (never inside-out), never a command in
  term position (`(let … (check-sat))` is now answered `unsupported`),
  never embed a string accumulator twice per level (exponential text).
* `main` moves hourly during campaigns: merge in your worktree,
  re-verify at each merge, ff from the primary only when clean and
  disjoint; `git status` twice before staging, and stage by file, not
  `add -A` (the fmt sweep of another owner's fmt-dirty landing rode an
  `add -A` into a commit — precedented, but say so in the message).

The one-sentence version: **the arc is closed with every item
verdicted, the ledger is empty of wrong verdicts, the live panic on
main is repaired (check that before any csr-revert), and the campaigns
that remain are owned — coordinate before touching solver core,
simplex, or nixie-sat.**
