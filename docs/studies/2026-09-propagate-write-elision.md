# Propagate write-elision + branchless other-watch: pre-registration + results (2026-09-01)

Follow-up to the landed BIG-authoritative study
(`2026-09-big-authoritative-bcp.md`) — its closing "remaining lever" list:
the large-clause visit itself. This study takes the two lowest-risk cuts
from that list; Gent's saved-position scan (needs a header field) stays
deferred behind the 12-byte-header pin per the closed arena study.

## The visit shape being cut (measured in the BIG study's histogram)

On `circuit_64in` at 40 k conflicts: 222 M visits, 84.8 % blocker hits,
15.2 % large misses; miss sub-paths: satrepl 53 %, moved 36 %,
firsttrue 11 %, unit+conflict <1 %. Every kept watcher is written back
with a full 12-byte store (`watches[write] = watcher` / the
`Watcher { blocker, .. }` rebuild), and every miss visit runs the
"make the false literal position 1" conditional swap (2 arena stores)
*before* deciding it did not need them (satisfied/satrepl paths never
write positions).

## The cuts

**(e) kept-watcher write elision.** The two-pointer compaction only
differs from the read pointer after the first dropped watcher; while
`write == read` a kept watcher's write-back is a pure self-write. Branch
on it: blocker-hit path writes nothing while `write == read`; refresh
paths (firsttrue/satrepl/unit) write only the `blocker` word (1 store
instead of 3). Final memory state identical in all cases — this cut is
state-identical by construction.

**(a) branchless other-watch (cadical `lits[0] ^ lits[1] ^ lit`) with
on-demand normalization.** `first` is computed as the XOR of the three
codes (no branch, no arena write). The arena position invariant
("`lits[0]` is the asserting literal of a *reason* clause") is preserved
by writing positions only where needed:

* satisfied-first / satrepl paths: **no position writes** (a non-reason
  clause's position order is unobservable — audited: every other
  `lits[0]`/`lits[1]` consumer reads the pair order-insensitively
  (detach, rebuild, BIG build, ELS, transred, probing), and a *reason*
  clause can never be re-visited on a writing path while it is a reason
  — its propagated literal is true, so every visit of its watchers
  short-circuits satisfied);
* move path: write `(0)=first, (1)=l, (j)=¬lit` — 3 stores vs the
  current swap-pair's 4;
* unit path (the clause becomes a reason **now**): normalize
  `(0)=first, (1)=¬lit` before `assign_propagation` — this is the one
  site the invariant is actually created, and it is the same writes the
  old top-swap did;
* conflict path: normalize the same way (rare; keeps any downstream
  lits[0] reader honest).

The unit path's normalization is exactly what today's unconditional
top-swap guaranteed; the difference is that satisfied/satrepl visits
leave the two watched literals in whichever order they found them.

## Change class

Path-preserving: final watch-list state identical (e); arena literal
*order* differs only on non-reason clauses whose last visit was a
satisfied/satrepl visit — argued unobservable above, and Gate 1
(trajectory identity) is the empirical proof for both cuts.

## Go / no-go (pre-registered BEFORE measuring)

1. **Gate 1 — trajectory identity**: 54-file `/tmp/sc24f`,
   `stats_solve`, `MAXC=60000`, default seed, vs `precompile/49ec6b1`
   (the BIG-authoritative landing): counters + verdict bit-identical.
2. **Gate 2 — instructions** (`cpu_core/instructions`, pinned, private
   target dir): fixed `MAXC=40000` on the miss-path class
   {circuit_64in, si2-b03m, noL-11-14} — geomean ≥ **1.02**; frb45-21-2
   (post-BIG also blocker-hit-dominated) expected ≥ 1.00 and counted
   separately; the binary-heavy class {ITC2021_Early_3, qwh.50.1250,
   shuffling-2} as should-not-regress (≥ 0.99). Both-solve corpus
   geomean ≥ 1.00. 1.00–1.05 on the miss-path class = neutral, below
   the bar → revert and record.
3. **Soundness** (if landed): workspace suite, clippy/fmt/doc,
   `diff_equiv` ≥ 100 k + debug batch (invariants active), corpus
   verdict sweep 0 mismatches, SMT differential 0 disagreements, z3
   parity.

## Results — LANDED (slice e only; slice a reverted on Gate 1)

**Slice (a) — branchless other-watch with on-demand normalization —
FAILED Gate 1 and was reverted before any measurement.** 34/54 corpus
trajectories diverged. Root cause: leaving the watched pair in visit
order on satisfied/satrepl paths *is* observable — not through the
direct `lits[0]` readers the audit covered (all order-insensitive), but
through **order-sensitive consumers**: `watch_rank`'s first-wins
selection in `remove_literal_and_rewatch`-style re-attach, first-wins
scans in vivify/probe/els, tie-breaking anywhere positions meet a
comparator. Stored literal order is part of the observable state, full
stop. The unconditional top-swap stays (2 arena stores per miss
visit), with a comment recording why. A retry would have to normalize
positions without the stores on exactly the paths that need them —
which is what the failed pilot did — or eliminate the order-sensitive
consumers; neither is worth the tail risk at ~0.4 % projected gain.

**Slice (e) — kept-watcher write elision — passed everything and
landed** (`49ec6b1` → this commit):

- **Gate 1**: 54/54 bit-identical vs `precompile/49ec6b1` (old sha
  `50fe131e…`, new `957b1189…`) — the cut is state-identical by
  construction, confirmed.
- **Gate 2** (fixed `MAXC=40000`, 3 reps, pinned):

  | file | old | new | old/new |
  |---|---|---|---|
  | circuit_64in | 17.228 G | 16.423 G | **1.0490** |
  | noL-11-14 | 5.044 G | 4.936 G | 1.0218 |
  | si2-b03m | 16.002 G | 15.764 G | 1.0151 |
  | **miss-path geomean** | | | **1.0285** (bar 1.02) |
  | frb45-21-2 (extra) | 9.155 G | 8.834 G | 1.0363 |
  | binary-heavy ctrl | | | 1.0054 (band ≥ 0.99) |

- **Gate 2b**: both-solve corpus geomean **1.0054**, 0 verdict
  mismatches (the both-solve cells are the easy tail where propagate is
  a small share; the fixed-cap class carries the effect).
- **Gate 3**: `nixie-sat` 879/879, workspace 10 418/10 418,
  clippy/fmt/doc clean, `diff_equiv` 200 k iterations 0/0, corpus
  verdict sweep 54/54 **0 mismatches** (one new-only 60 s solve — pure
  speed, identical trajectories), SMT differential **160/0** (par2
  2 316.9), z3 parity **169/1/0**.

The two-store saving lands where predicted: kept watchers (65–85 % of
all visits) no longer write back 12 unchanged bytes while the
compaction pointers coincide; refresh paths write the blocker word
only. Cumulative with the BIG landing on this session's chain:
circuit-class files are now ~1.08× fewer instructions to the same
conflict count than the session start.

## Hazards (recorded for the next agent)

The unit-path normalization omission is the one soundness-relevant
risk of slice (a) — moot after the revert; slice (e) writes the same
final state as before, just fewer redundant stores.
