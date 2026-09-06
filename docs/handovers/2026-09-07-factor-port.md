# Handover: Full Kissat Factor Port (Worker-Class Conflicts Gap)

## Context

Worker-class instances (worker_550 et al.) show a **12.75× conflicts gap** vs kissat — the largest single-file residue in the 1.12× corpus geomean. The calibration is precise: kissat refutes worker_550 in **2 003 conflicts** with **51 466 factor introductions** (55% of its 93 713 variables), **0 BVE eliminations**, and **227 decisions per conflict**. Our best is ~15 000 conflicts. The gap is pure formula restructuring through factoring.

Every simplified rewrite rule we've tried has been **measured negative or chaotic** on this class. The full mechanism — kissat's quotient-chain construction with incremental delivery — is the only remaining path. This document specifies the port.

## What Must Be Ported (from `../temp/kissat/src/factor.c`)

### The Core Data Structure: Quotient Lists

kissat does NOT pre-compute pairs and intersect their co-occurrence sets (our approach). It builds **quotient chains** incrementally:

```
quotient {
    factor: unsigned,       // the pivot literal
    clauses: statches,      // watch-list snapshot of clauses containing this pivot
    matches: sizes,         // per-clause index into the PREVIOUS quotient's clause list
    matched: size_t,        // count of matched clauses
}
```

A chain `q1 → q2 → ... → qm` is built one pivot at a time. Each new pivot's clauses are matched against the current chain tail's clauses. Only matched clauses survive to the next link.

### The Algorithm (simplified from factor.c)

1. **First pivot**: pick a literal `x1` (by degree/scoring), collect all clauses containing it from the watch list.
2. **Chain extension**: for each candidate next pivot `x2`, check which of `x1`'s clauses have a corresponding clause for `x2` sharing all non-pivot literals. The **matched** subset becomes the chain's clause set.
3. **Apply**: introduce fresh `t`, add dividers `(t ∨ x_i)` for each chain link, add quotients `(¬t ∨ A_j)` for each matched clause's non-pivot literals, delete all originals.
4. **Update**: the fresh variable's score/queue position is set to make it the next decision candidate (kissat pushes it to the front of the VMTF queue).

### What Makes It Different From Our AND-Gate

| aspect | our AND-gate (measured negative) | kissat factor |
|---|---|---|
| pair finding | pre-computed intersection of co-occurrence sets | incremental chain, one pivot at a time |
| tail set | ALL shared tails at once (344 on worker) | only the matched subset (grows organically) |
| delivery | one mega-round (all introductions at once) | spread across many rounds during search |
| variable schedule | new vars enter VMTF at default position | new vars pushed to FRONT of queue (immediate decisions) |
| scoring | degree ranking | `distinct_paths` (optional, default off in kissat) or `watches_score` (degree) |
| occurrence source | BIG CSR edges (our BIG) | kissat's dense watch lists |
| retirement | `remove_clause` / raw remove | `eagerly_remove_watch` (O(1) from the watch list) |

The **variable-schedule push** (kissat's `adjust_scores_and_phases_of_fresh_variables`) is critical: the fresh hub variable is dequeued from VMTF and pushed to the FRONT of the queue, making it the next decision. This means the search immediately explores the restructured region — not after thousands of conflicts of delay.

## The Port Plan

### Phase 1: Infrastructure (days 1-2)

1. **Read the source**: `../temp/kissat/src/factor.c` lines 1-900. The key functions are `init_factoring`, `next_factor`, `match_quotient`, `apply_factoring`, `flush_unmatched_clauses`, `adjust_scores_and_phases_of_fresh_variables`.

2. **Quotient chain builder**: replace our pairwise intersection with an incremental chain. For each first pivot, extend the chain by one pivot at a time, keeping only matched clauses. The match test: two clauses match if they share all non-pivot literals.

3. **Watch-list occurrence source**: our BIG CSR gives binary co-occurrences, but kissat's factor works on ALL clauses (not just binaries). The quotient clauses include non-binary clauses containing the pivot. Use the watch lists (`self.watches`) for non-binary + the BIG for binary.

4. **Eager retirement**: `eagerly_remove_watch` removes a clause from the watch list in O(1) by swapping with the last element. Our `remove_clause` does full BIG purge + watcher removal + DRAT. For factor-internal retirement, use raw removal (the caller rebuilds after the pass) — this is already what our tombstone mode does.

### Phase 2: Variable Schedule (day 2)

5. **Fresh variable push**: after introducing `t`, dequeue it from VMTF and push to the front of the queue. This requires access to the VMTF queue structure. In our solver: `self.vmtf` (see `nixie-sat/src/solver/decide.rs` for how the queue works). The push makes `t` the next decision variable — the search immediately explores the hub.

6. **Score adjustment**: kissat sets the new variable's score to 0 (unbumped). In our solver, the activity/VSIDS/LRB scores need to be initialized for the new variable (our `new_var()` already handles this).

### Phase 3: Integration & Budgeting (day 3)

7. **Schedule**: kissat runs factor inside its `eliminate` rounds. Our equivalent is the `inprocess()` round. Wire the chain-based factor as a pass in `inprocess()`, replacing the current `and_gate_factoring_mid()` call when `NIXIE_FACTOR=1` (new knob).

8. **Budget**: `factor_effort` per-mille of search work (kissat default 50‰ = 5%). Reuse `InprocBudgets` for window-relative bounding.

9. **Round cadence**: kissat's factor runs every `eliminateint` rounds (500 × nlog²n conflicts). Our equivalent: run in every `inprocess()` round but with the effort budget bounding the work.

### Phase 4: Verification (day 4)

10. **Soundness fuzz**: differential (factor on/off, 20k random CNFs). The rewrite is equisatisfiable and model-preserving (same argument as our AND-gate — the Tseitin encoding is the same).

11. **Worker screen**: 5-seed on worker_550. Success criterion: median conflicts ≤ 5000 (kissat is 2003, our current best is ~15000).

12. **Corpus A/B**: 5-seed on the 54-file corpus. Go bar: conflicts geomean ≤ 0.95 vs off AND solved-at-cap not lower.

## Key Technical Details From the Source

### Chain Matching (from `match_quotient`)

For each clause `c` in the previous quotient's list, find a clause in the new pivot's list that matches. For binary clauses: match if the same other-literal exists in the new pivot's watch list. For large clauses: match if all non-pivot literals coincide.

```c
// From factor.c, simplified:
for each clause c in last_quotient->clauses:
    for each literal q in c (q != last_pivot):
        if new_pivot's watch list contains a clause with q:
            // this clause matches — keep it in the chain
```

### Divider and Quotient Clauses (from `apply_factoring`)

For a chain `q1 → q2 → ... → qm` with matched clause sets:
- Add `(t ∨ x_1)`, `(t ∨ x_2)`, ..., `(t ∨ x_m)` — one divider per chain link
- For the LAST quotient's matched clauses `(x_m ∨ A_j)`: add `(¬t ∨ A_j)` — one quotient per clause
- Delete all chain clauses

The rewrite for a 2-chain (our AND-gate pair) is the special case.

### Fresh Variable Push (from `adjust_scores_and_phases_of_fresh_variables`)

```c
// Dequeue from VMTF and push to front
kissat_dequeue_links(idx, links, queue);
// ... relink at queue.first ...
queue.search.idx = queue.last;  // next decision is the new variable
```

Our equivalent: manipulate `self.vmtf` to put the new variable at the search pointer.

## What NOT To Do (Measured Negatives)

- **Bulk all-shared-tails intersection**: our BIG-based pair mode finds 344-tail pairs on worker but over-consolidates. Measured negative.
- **Tail capping**: `NIXIE_ANDGATE_MAXT` (5/10/20/40) doesn't fix the regression — the hub introduction itself disrupts search, not just over-consolidation.
- **Degree-based TOP=256 hub ranking**: finds the wrong hubs on worker. kissat's default uses degree too (`watches_score`), but the chain construction is what makes the right pairs.
- **Mega-round delivery**: introducing 10k+ hubs in one round bloats the DB. Incremental delivery across many rounds is essential.

## Existing Infrastructure You Can Reuse

- `nixie-sat/src/solver/bva.rs` — the AND-gate pair-mode has the BIG-based construction (fast), the soundness argument, the reason hygiene, the tombstone retirement, and the `mark_elim_vars` integration. The rewrite rule is the same; only the pair-finding and delivery change.
- `nixie-sat/src/solver/learn.rs` — `InprocBudgets` for effort bounding, the round-site integration point.
- `nixie-sat/src/watched.rs` — watch lists for non-binary clause occurrence lookup.
- `nixie-sat/src/solver/mod.rs` — the BIG CSR structure (`binary_graph.get(lit)` → `BigList<(Lit, ClauseId)>`).
- The fuzz harnesses in `nixie-sat/tests/mid_bva_soundness.rs` and `mid_andgate_pair_mode` — extend with the chain variant.

## Calibration Data (for verifying you're on track)

| metric | kissat on worker_550 | our current |
|---|---|---|
| conflicts | 2 003 | ~15 000 |
| factor introductions | 51 466 | 0 (default off) |
| BVE eliminations | 0 | — |
| decisions per conflict | 227 | ~4 |
| props per decision | ~40 | ~35 |
| factor_ticks / total | 284M / 402M (71%) | 0 |

**The 227 decisions per conflict is the signature**: kissat's factored formula is so restructured that each conflict consumes 227 decisions of descent. If your port doesn't produce dramatically deeper decision chains, the restructuring isn't deep enough.

## Expected Outcome

If the port delivers kissat's worker-class factor faithfully:
- worker_550 conflicts: ~15 000 → 2 000-5 000
- Corpus conflicts geomean: 1.12× → ~1.05× (worker is one file but a huge outlier)
- New mechanism: the only known way to close the worker-class gap

If it doesn't (per-file chaos like the AND-gate):
- Document with per-seed data; the worker gap is then accepted as requiring a fundamentally different search paradigm on that class
