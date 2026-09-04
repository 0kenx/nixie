# Eliminate resolvent-marking vector removal: pre-registration (2026-09-01)

Next slice after the chunk-summary landing (`36e72b4`). Fresh profile on
g2-slp (`/tmp/sc24f`, `MAXC=20000`, no-LTO symbols build): `eliminate_phase`
**59.7 %** of instructions, and inside it the inclusive tree is
`elim_round → try_scheduled_elimination → elim_try_variable →
elim_resolvents_bounded (45 %) → elim_resolve_clauses (43.4 %)` with
**`Vec::push` alone at 14 %** of the whole run. The resolvent buffer is
already Eliminator-scoped scratch (pooled in the marking-phase rewrite;
the capacity-pooling study closed the *allocation* question), so the
remaining cost is **push volume** — how many literals get pushed per
resolution.

## The target: a bookkeeping vector that exists only to unmark

`elim_resolve_clauses` marks each unassigned non-pivot literal of `c`
with `mark[lit] = 1; mark[¬lit] = -1`, pushes it into `ctx.res_marked`
*and* into `ctx.res_resolvent`, and after the d-scan iterates
`res_marked` to clear the marks. The d-scan never writes marks (it only
reads them) — so the marked set is exactly c's marked prefix. CaDiCaL's
`resolve_clauses` (`src/elim.cpp`, `unmark (c)`) keeps no bookkeeping
vector: it re-derives the set from the clause.

**The cut**: the marked literals are *already* in
`res_resolvent[0..marked_n]` — capture `marked_n =
res_resolvent.len()` between the c-scan and the d-scan (zero per-literal
cost) and unmark from that prefix. Delete `res_marked` entirely: its
per-c-literal push (capacity check + store + len write), its per-call
`clear()`, its cache footprint, and the second pass over it.

Per resolution this removes ~|c| pushes of ~3 (res_marked +
res_resolvent + shared d-side) push sites — roughly a third of the
resolution push volume on elimination-heavy instances (~4-5 % of
g2-slp's total instructions, estimated).

**Path-preserving by construction**: identical marks are set and cleared
(the prefix is exactly the marked set — appends after `marked_n` never
displace it), identical resolvents, identical order, identical
schedule. No behaviour difference is representable.

Also audited against the reference: cadical has **no early-abort** on
resolvent size inside `resolve_clauses` (the `elimclslim` check is in
the caller, exactly like our `ELIM_CLS_LIMIT` in
`elim_resolvents_bounded`) — no port gap there; the swap-to-smaller-c
trick cadical uses changes resolution order/roles and is therefore out
of scope for an identity-gated engineering change.

The second mark site (`backward` candidate matching, ~line 1246) uses a
separate scratch struct and a different algorithm — untouched.

## Go / no-go (pre-registered BEFORE measuring)

Base arm: `precompile/36e72b4` (the chunk-summary landing).

1. **Gate 1 — trajectory identity**: 54-file `/tmp/sc24f`, `stats_solve`,
   `MAXC=60000`, default seed: counters + verdict bit-identical on every
   file.
2. **Gate 2 — instructions** (`cpu_core/instructions/`, P-core pinned, 3
   reps, `MAXC=40000`): **g2-slp ≥ 1.02** (the eliminate-dominant file);
   controls {worker_550, circuit_64in, noL-11-14, frb45-21-2} in
   **0.99–1.01**; 54-file corpus geomean ≥ 1.00.  Class 1.00–1.02 →
   neutral, revert and record.
3. **Gate 3 — soundness** (if landed): workspace suite, clippy/fmt/doc,
   `diff_equiv` ≥ 100 k, corpus verdict sweep 0 mismatches, SMT
   differential 0 disagreements, z3 parity clean.

## Results — LANDED (all gates green)

**Baseline incident (disclosed):** the first Gate 2 run showed
implausible ratios (worker 1.11, frb45 1.106) because
`precompile/36e72b4/stats_solve` had been copied from a **stale
shared-target artifact** (`target/release/examples/stats_solve`, built
00:05 by an earlier session; the landing session rebuilt only
`cnf_solve` into the shared target, so the example binary predating the
chunk-summary code was cached). It reproduced 167.9 G on worker — a
value matching no recorded number — deterministically. The entry was
rebuilt from a clean worktree of `36e72b4` (verifying 151.354 G,
matching the landing study's 151.361 G) and every gate below was re-run
against the corrected base. Lesson recorded: a precompile entry is only
trustworthy if its binary reproduces a known measurement; "too good"
ratios are a broken-comparison smell, not a win.

**Gate 1 — trajectory identity: PASSED** — 54/54 files bit-identical
vs the corrected `precompile/36e72b4` (`MAXC=60000`, `stats_solve`).

**Gate 2 — instructions** (`cpu_core/instructions/`, P-core pinned, 3
reps, `MAXC=40000`):

| file | old | new | old/new | bar | |
|---|---|---|---|---|---|
| g2-slp | 47.153 G | 45.348 G | **1.0398** | ≥ 1.02 | pass |
| worker_550 | 151.354 G | 151.279 G | 1.0005 | 0.99–1.01 | pass |
| circuit_64in | 16.359 G | 16.359 G | 1.0000 | 0.99–1.01 | pass |
| noL-11-14 | 4.940 G | 4.937 G | 1.0006 | 0.99–1.01 | pass |
| frb45-21-2 | 8.880 G | 8.860 G | 1.0022 | 0.99–1.01 | pass |
| **54-file corpus geomean** | | | **1.0036** | ≥ 1.00 | pass |

0 verdict mismatches over the corpus run. The effect is exactly where
predicted: the eliminate-dominant file gains 4 %, everything else is
flat — the cut touches only the resolution marking path, which
non-eliminating instances never execute.

**Gate 3 — soundness (all green)**: workspace `cargo nextest run
--workspace --all-features` **10 418 / 10 418**; clippy `-D warnings`,
`cargo fmt --check`, `cargo doc -D warnings` clean; `diff_equiv`
**100 000** iterations (66 993 sat): **0 mismatches, 0 invalid models**;
corpus verdict sweep 54/54 identical; SMT differential **160 solved /
160 agree / 0 disagreements** (par2 2311.67 — a fresh `nixie` CLI build
was required; the shared-target one had gone stale again, scoring 0 —
see the baseline incident above); z3 parity **169 Correct / 1
Inconclusive / 0 disagreements**.

### Cumulative arc on g2-slp

`d3261a6` → `36e72b4` → this landing: eliminate-phase share of g2-slp
instructions 59.7 % at the profile cap, with the resolution marking
overhead now cut by the pooled-buffer rewrite (earlier), the
`res_marked` removal (this), leaving the pair-loop and backward
subsumption as the remaining measured costs. The round-2+ economics
(schedule gating) remains the recorded heuristic-class lever.
