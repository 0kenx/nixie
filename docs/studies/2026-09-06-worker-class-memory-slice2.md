# Worker-class memory, slice 2: walk-on-BIG, arena slack trims, streamed BVE scans (2026-09-06)

Follow-up to `2026-09-05-worker-class-memory-landing.md` (slice 1: 965 →
810 MB on worker_550, identity-gated). This slice closes the two blockers
that study named: the walk round's per-round occurrence CSR + true-count
arrays (~120 MB on worker), and the arena/heap floors around them.

## The changes (all trajectory-neutral, identity-gated)

| # | change | where | mechanism |
|---|---|---|---|
| G | **walk-on-BIG**: the walk's binary occurrence lists are the BIG itself, merged by clause id with a small CSR over only non-binary participants | `solver/walk.rs` | every binary clause (a ∨ b) already holds exactly one BIG edge per literal under the trigger of that literal's negation, and per-literal BIG lists are clause-id ascending at all times (rebuilds iterate ids ascending; incremental edges append strictly larger ids — ids are append-only; removals `retain`), so a by-id merge reproduces the packed CSR's per-literal order **exactly**. Binary true-counts are never stored: true_count == 1 ⟺ exactly one of x,y true, which the flip conditions derive from `values`. A 1-bit-per-id participation bitset filters learned/deleted/sentinel/fixed-literal edges lazily. Per-round transient on worker_550: ~124 MB (occ CSR 82 + per-id true-counts 42) → ~13 MB (bitset 1.3 + non-binary CSR ~10 + dense true-counts ~1.2; worker is 97 % binaries). A debug-only per-literal parity check (`bin_expect`) turns any duplicate/stale/mis-keyed BIG edge — states propagation tolerates but the walk's identity contract does not — into a loud failure |
| H | arena **growth-slack trim**: `ClauseArena::trim_slack` reallocs the buffer to `used + used/8` when slack ≥ max(16 MiB, used/2); wired into the reduce round (where `should_compact` is checked), solve start, and walk entry (cadical garbage-collects before its walk rounds) | `memory.rs`, `clause.rs`, `solver/mod.rs`, `solver/walk.rs` | the `Vec` doubling overshoot is paid by RSS, not by clauses: worker_550 ended a run at 537 MB capacity vs 317 MB live with waste under the compaction gate the whole time. Capacity-only; ids/bytes/orders untouched |
| I | **BVE snapshot-free scans**: `forward_subsumption` and the variable-elimination scan collected full `Vec<ClauseId>` snapshots (41 MB + growth slack each on 10.3 M-clause instances, two alive at once, freed pages resident) | `solver/bve.rs` | replaced by bounded index loops `0..num_slots()` recorded at pass entry — identical semantics (ids are append-only, so the bound *is* the snapshot; start-deleted ids are filtered by the same `!c.deleted` checks), zero allocation |

## Why walk-on-BIG is identity-preserving (the argument, then the gate)

The occurrence order is the trajectory contract: the broken-list push order
feeds the RNG-indexed picker. The merged stream is (a) BIG list at
`code(¬L)` filtered to participants — ascending by id because every BIG
mutation preserves or appends ascending order — merged by id with (b) the
non-binary CSR for `L` — ascending by construction. Two ascending disjoint
streams merge to the packed CSR's exact per-literal sequence; the flip
conditions' derivations (`true_count==1 ⟺ target literal false` for
binaries) reproduce the stored values by definition. Ticks count entries
during iteration, matching the old `occ_of(..).len()`.

## Memory result (per-child VmHWM, 100 s cap, quiet machine, canonical corpus)

All eight files' conflict counts bit-match the stored records — the whole
memory set is trajectory-identical to the baseline.

| file | slice 1 | slice 2 | Δ | kissat | nixie/kissat |
|---|---|---|---|---|---|
| noL-11-14 | 33 MB | 28.9 MB | −12 % | 21 | 1.38× |
| frb65-12-2 | 22 | 22.1 | 0 | 12 | 1.84× |
| FmlaEquivChain | 85 | 83.5 | −2 % | 52 | 1.61× |
| mrpp_4x4 | 16 | 15.2 | −5 % | 12 | 1.27× |
| g2-slp | 159 | 162.4 | +2 % | 72 | 2.26× |
| **worker_550** | **810** | **736.5** | **−9.1 %** | 282 | **2.61×** |
| si2-b03m | 108 | 110.7 | +2 % | 103 | 1.07× |
| shuffling-2 | 498 | 491.8 | −1 % | 269 | 1.83× |

Cumulative on worker_550 vs the KR1.1 baseline: 965 → 736.5 MB
(**−23.7 %**); worst nixie/kissat ratio across the set 3.42× → 2.61×.
The KR2 targets (−25 %, ≤ 2.5×) are *not* fully met — the honest residual:

- The peak now sits in the **pre-search elimination phase** (t ≈ 3 s):
  standing heap ≈ 293 MB (BIG 165 live + per-var + bins) + arena 252 +
  the BVE occurrence CSR. The BVE phases' occurrence primaries are
  64–80 MiB mmaps (16.7–21 M u32 entries) — inherent to the pass under
  trajectory-neutrality (`NO_BVE=1` measures the peak at 681.8 MB,
  −55 MB, but that arm changes the search).
- The walk no longer contributes to the peak at all (its transient
  collapsed from ~124 MB to ~13 MB); the search-time plateau is
  ~710 → the last walk round coexists with ~26 MB of it.
- The structural 2× vs kissat remains the binary representation
  (44 B/binary + BIG edges vs kissat's tiered 16–24 B) — the named
  lever for a future slice.

## Wall neutrality

**Identity gate (gate:identity): 54/54 files, verdict AND conflict counts
bit-identical** old (`cb9f05c`) vs this tree — the port, the trims and the
streamed BVE scans change no trajectory. Identical trajectories cannot
cost search work; the paired wall confirms it: over the 49 files decisive
in both this run and the stored `cb9f05c` 4-arm records, the paired geomean
wall new/old is **0.988×** (new slightly faster; the sub-0.05 s simon
noise files swing ±70 % of nothing and average out). A sequential-arm
standing pass (each arm alone on its pinned core) reads nixie/kissat =
1.58× — but that layout gives the reference arms uncontended memory
bandwidth the baseline's concurrent layout did not; the
baseline-comparable concurrent re-run is recorded below.
