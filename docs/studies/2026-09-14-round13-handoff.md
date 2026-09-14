# SAT performance program — round-13 handoff (2026-09-14 close)

> Supersedes `2026-09-14-round12-handoff.md` (whose items all closed;
> its addenda are folded in here).  Entry points:
> `docs/studies/2026-09-14-csr-dual-write-scan.md` — **19 sections**,
> the CSR program's complete lab notebook (designs, measurements, five
> commit-B investigation sections, re-apply recipes);
> `docs/studies/2026-09-14-amplitude-trajectory-answer.md` (closed);
> `docs/studies/2026-09-14-metric-decision.md` (closed).

## Program state in one paragraph

The CSR-watches migration stands at **flip A landed and certified**: the
CSR is the primary watch representation on the default path
(`c77ddf76`, Z3-parity clean, trajectories bit-identical corpus-wide),
with the `Vec` lists retained one commit longer as the verification
shadow.  **Commit B (the deletion) is one root-cause question away**:
five attempts narrowed its divergence from "six mystery clauses" to
**the exact two entries and the exact mechanism** — a dedup-suppressed
repair pair on literal 8440 — with the single remaining question
narrowed to one cleaning-path asymmetry.  Everything needed to finish
is landed: the re-apply recipe (~1 h mechanical from the study), the
probe tools, and the certified A/B binaries.

## The one question (commit B's completion)

**Which cleaning path dropped the same-ref entries from flip-A's `Vec`
but left them in the roundtrip's CSR between two scans of literal
8440?**  (Full context: the study's fifth commit-B section.)  The
divergence: repairs re-register a clause's watched pair under 8440;
the roundtrip's `push_watch_unique` dedup suppresses the re-push
because the CSR still holds same-ref (stale) entries the `Vec` had
already dropped — the clause then runs unwatched until the next
rebuild.  Candidates: the `Vec`'s lazy dead-entry removal at *other*
literals' scans interacting with the mirror's segment bookkeeping; the
relocate's ref rewrites desyncing a `remove_clause(lit, r_old)` from
the entry's current `r`; span-tail visibility.  **The instrument**:
a per-ref mutation log (when did ref 1077664's entry under 8440 leave
A's `Vec` vs B's CSR) — one env, two runs, diff.

**The re-apply recipe** (study sections 4-8, in order): CSR-only `add`;
`take_combined`/`put_back_combined` on `CsrWatchLists` (TAKE semantics
— empties the live segments, matching `mem::take`); the session
driver's roundtrip (split-borrow `csr_dest`); `list_kernel`
destinations = `&mut CsrWatchLists` with the notification branches
stripped; the non-session take/put-back via
`take_combined_vec`/`put_back_combined_vec`; the rebuild's
unconditional adopt (the counting-sort build IS the rebuild); ghost
debt recorded in the CSR relocation pass.  Gates: trajectory identity
(6s167 33 028), all four driver configs, tests, parity.

## What the CSR program has proven (all landed, default-off or
unconditional-but-validated)

1. **Dual-write scan** (`0e005231`): the mirror maintains the CSR
   through all three scan bodies and every cold path; drift
   `mismatched=0` corpus-wide.
2. **Position index** (`b2beb461`): ref → watched-literals, exact
   through real drift (0/351 k).  Two bug classes caught by the nets
   (relocate's dead-ref panic, HashMap-Debug nondeterminism).
3. **ELS surgery correctness** (`c31cf26c`): the contract oracle
   (live long ⟺ exactly two watchers) green end-to-end; the scan-free
   window discipline established.
4. **Surgery economics** (`ab5bc6ee`): batched-by-literal removal —
   **46× win on sparse rounds, wash on mass rewrites**; spans verified
   sorted-by-ref (100 %).
5. **Swapped-dual scan** (`16fecd9d`): the CSR-scanned, Vec-mirrored
   session kernel — bit-identical, drift 100 % zero.
6. **Reader gate** (`41ea003f`): production readers on the combined
   view; the surface is **four sites** (not the kickoff's estimate).
7. **FLIP A** (`c77ddf76`): CSR primary unconditionally; **Z3 parity
   4.16.0 clean, trajectories bit-identical on 4 classes, drift 100 %**
   — the arc's landed frontier.

Closed research threads (round-11 items 2-3): the amplitude→trajectory
answer (carried-phase-state collapse — `e4a72db5`) and the metric
decision (survivorship bias exposed; the 60 s gate stays —
`8d0f52e8`).

## Instrumentation landed (all env-gated, zero default cost)

- `NIXIE_CSR_SHADOW=1` — the drift oracle + rebuild diagnostics
  (flip-A: on by construction; the flag adds the prints).
- `NIXIE_CSR_SCAN=1`, `NIXIE_CSR_READ=1` — the swapped-scan and
  reader gates (now folded into flip A; the flags remain for bisection).
- `NIXIE_ELIM_CSR_SURGERY=1` — the ELS rewatching surgery + contract
  oracle + economics counters (visits/nanos vs the two-sweep build).
- `NIXIE_CSR_CHARGE_TRACE=1` — every session tick charge
  `(charge, stable, len, bins, ghosts, code)`.
- `NIXIE_CSR_CONTENT_TRACE=<code>` — the scanned scratch's entries at
  every scan of one literal (the tool that pinned the divergence).
- `NIXIE_CSR_MUT_TRACE=<code>` — per-literal CSR mutation log
  (push/remove).
- `NIXIE_DUMP_WATCHES=<prefix>` — the CSR's combined view per literal
  at every rebuild (the cross-binary state comparator).
- `NIXIE_DUMP_ELIM_PHASE=<n>`, `NIXIE_ELIM_RESET_PHASES=<n>` — the
  amplitude study's dump/probe pair.
- `NIXIE_LOG_ELIM` / `NIXIE_LOG_ELIMDTL` — the elimination phase/round
  and per-variable traces (round-10 inheritance).

## Precompile map (this program's entries)

- `c77ddf76` — **flip A** (the certified CSR-primary default path).
- `cea69d4b` — flip A + the full probe family (the A-side binary for
  commit-B bisection).
- `107b7868` — the standing default baseline (pre-CSR, bit-identical
  default through `c77ddf76`).
- `3e9b2b51`, `bd06ae67`, `b2beb461`, `ab5bc6ee`, `41ea003f`,
  `16fecd9d` — the intermediate certified steps (screen/bisect use).
- Runners: `outputs/csr_slice2_corpus_check.py` (three-arm corpus +
  drift), `outputs/csr_slice2_ab_serial.py` (serial wall A/B),
  `docs/studies/assets/amp-traj-2026-09-14/` (the censored-reanalysis
  and multi-seed runners).

## Traps (accumulated; the round-12 list + this session's)

1. **Both-decided aggregates lie about censored arms** — use the
   censored score (`docs/studies/assets/amp-traj-2026-09-14/`).
2. `smt-lib/` absent from this machine — the workspace suite's
   corpus-missing failures are environmental (all-failures-are-
   corpus-missing is the gate read).
3. Concurrent agents break clippy/doc on main intermittently — grep
   the output for *your* crate's paths; verify from a worktree.
4. /tmp and the disk fill under load — `TMPDIR=` private, delete
   private target dirs once binaries are in `precompile/`.
5. **The python-anchor trap** (cost this session repeatedly): the
   edit scripts' `str.replace` anchors silently no-op on fmt-reshaped
   text — always `grep` that the edit landed before building.
6. **Stale-binary trap**: `cargo build` failing after a grep-pipe means
   the previous binary ran — check the build's error count is from a
   clean invocation.
7. The A/B bisection discipline that cracked commit B: MAXC-ladder
   decision/propagation comparison against a certified binary, then
   per-literal charge/content/mutation traces, diffed — the tool family
   is landed and the pattern is reusable.

## Standing methodology notes

- The flip's safety net is gone by design (the drift oracle retires
  with the `Vec`); commit B's gates are the standard suite + trajectory
  identity + parity.
- The ELS surgery's payoff path: after commit B, wire the batched
  surgery into the sparse-mutator rebuilds (subsume/BVA/BVE — the 46×
  regime); the counting-sort rebuild stays for mass rewrites (ELS).
- The `Vec`'s memory (~2.6 M headers on si2-class) is commit B's
  direct win; the instruction economics are neutral (measured).
