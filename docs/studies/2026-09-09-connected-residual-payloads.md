# Connected residual payloads for forward subsumption

The [last candidate profile](2026-09-09-packed-watch-live-view.md) places
36.39% of subsumption self-cycle attribution in occurrence-ID/ref/header
lookup and validation (6.91% of the whole original-circuit profile).
Membership scanning accounts for another 32.14% / 6.10%. The previous
watch-copy/live-view combination did not pass its wall gate. This follow-up
changes the work represented by the subsumption index rather than adding
another filter in front of the same database lookup.

## Algorithm and lifetime contract

After a scheduled clause has survived its own deletion/strengthening step,
copy its literals into a compact, round-owned word pool. Store its stable
database ID for promotion and current proof-ID lookup. Occurrence entries
remain four bytes, now offsets into records of
`[residual_length, database_id, residual_literal_codes...]`.

Omit exactly one occurrence of the connection literal. The query bucket's
key supplies that literal's signed mark once. For a positive key mark, the
remaining literals decide the same subset/SSR test. For a negative mark,
seed the one allowed complementary literal with the key; any second negative
still rejects. An absent key rejects while retaining the same clause-check
count. This also handles the scalar test's negative/absent-key cases without
assuming a positive mark to elide work. Residual literal order is preserved.

No arena pointers, proof IDs, tags, truncated literal codes or unsafe casts
are stored. Pool offsets and lengths have checked conversions; record slices
remain bounds checked. Connection policy, sorting, candidate order, binary
edge liveness checks, clause-check budgets and dirty/random scheduling are
unchanged. This is a representation/algorithm engineering comparison under
identical trajectories, not a new heuristic or a matched-null claim.

The semantic reference is local CaDiCaL `src/subsume.cpp`: process a candidate,
then connect it for later candidates. The relevant Nixie mutation audit is:

- The schedule contains each ID once. Only the current candidate can be
  retired or strengthened; it is copied after that decision and after watch
  reordering, including a ternary-to-binary transition.
- Later queries may promote an already-connected subsumer's learned flag,
  but cannot mutate its payload. Proof emission resolves the current proof
  ID from its stable database ID rather than caching a proof ID.
- `remove_literal_opts` changes the candidate and resets the propagation
  head; it does not propagate or collect during the round. `retire_clause`
  purges only that candidate's edges/reasons and sets its deleted flag.
- Every processed candidate is unmarked before a normal/budget exit. Clear
  occurrence and payload contents before the round returns. Retain only
  their allocation capacity, fixing the old normal-exit scratch-drop defect.
  Empty buffers cannot supply stale evidence after push/pop or compaction.

Debug builds compare every cached residual against the live database.
A test-only database-index oracle retains the old lookup/deletion checks and
old normal-exit scratch lifetime. Independent signed-set tests guard the
shared membership helper. Paired round/search tests must compare clauses,
metadata/activity bits, trail, watches, BIG, counters, dirty state and proof
transcripts. Cover promotion, strengthening, budgets, repeated rounds, spilled
lists, scopes, collection and exact SAT models/independent LRAT checks.

## Pre-measurement cost obligations

Inspect the ordinary optimized binary before executing a screen: connected
queries must use the pool rather than resolving through the clause database.
Include bounds checks, key-mark seeding, copy preparation and retained memory
in the cost. Record construction copies each connected residual once and
removes one literal per record; this is not free when a record has few future
queries. Reuse capacity and avoid both a clear-at-return and redundant full
clear-at-entry pass. The iterator/lookup representation may be repaired before
measurement if the generated code fails these obligations.

## Registration: at most five new solver invocations

The preceding wall screen used historical controls. Its broadly increased
cycle attribution did not isolate a local source regression, despite an
identical trajectory and fewer instructions. Here original circuit uses
**fresh seed 1** so control, candidate and Kissat are new cells run in the
same time window. Inspection found no existing CPU-15/original-circuit/seed-1
cell for qualified compact control `02cc03c` or Kissat `8af8e56`. Do not repeat
any cell if one appears before execution.

Use the cached qualified compact control `02cc03c` (`d1290db` equivalent
production source), pinned Rust 1.96.0 / LLVM 22.1.2 and lock SHA-256
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`.
Candidate starts from main `8cf8850`; its additional inherited SAT change is
an inactive terminal CNF-dump environment check from `ac13904`. Record exact
immutable source/binary hashes. Portable release/perf profiles, no native
flags, PGO or RUSTFLAGS override. A prototype is not a production landing.

CPU 15 (atom), MAXC=10000000, `NIXIE_SWEEP=0`, CaDiCaL preset, printed model
and 300-second emergency cap. Clear other study variables. Warm input and
executable reads, GNU time covering the complete target, anonymous tmpfs
output and <=10% off-CPU fraction; confirm no competing constrained userspace
thread includes CPU 15. Every start/completion is recorded immediately and
once, with full output and a checked model. Wall is primary per the user's
instruction, never a solver policy input.

1. Original-circuit control at seed 1.
2. Original-circuit candidate at seed 1. Require complete output identity
   with the control, a checked model and timing quality. Stop on a failed
   correctness or timing-quality check; no retiming.
3. Mode-matched Kissat 4.0.4 at seed 1, using exactly
   `--probe=0 --preprocess=0 --factor=0 --substitute=0 --sweep=0 --vivify=0
   --transitive=0 --backbone=0 --congruence=0`, plus statistics and the same
   seed/conflict cap. Check its model and timing quality.
4. If circuit quality/identity passes, one candidate circuit LBR diagnostic
   at seed 1 regardless of win/failure. Fixed atom cycle period 10472903,
   grouped user cycles/instructions, sample-read/running-time data, explicit
   CPU samples, LBR and 128 pages. Require zero loss/throttle/unthrottle,
   >=99.9% scheduling coverage, >=1000 samples and <=0.1% unresolved self
   attribution. Print terminal memory; remove only that line for output
   comparison. Failed profiles remain failed; profile time is diagnostic.
5. Only if candidate/control circuit wall <=0.95 and the profile qualifies,
   candidate original-si2 seed 0. Reuse control record `68494a8004e0cdca`
   (2.02 s) and Kissat `c3bb0064cbaa9d2d` (1.22 s), rather than rerunning
   them. Require identical Nixie output, checked model, timing quality and
   candidate/control <=1.03. This guard retains the historical-window caveat.

A positive source landing requires circuit wall <=0.95, the conditional si2
guard and two-input geometric mean <=0.95, plus every required repository
correctness gate. Report per-input wall/Kissat and wall/conflict, exact
outputs and solved-at-cap. This is a bounded two-input engineering screen,
not a population speedup or a superadditive interaction measurement. A
negative result must retain its candidate flamegraph and identify introduced
work, an opportunity limit or a concrete repair before abandoning it. No
sweeps, seed matrices or configuration tuning are registered.
