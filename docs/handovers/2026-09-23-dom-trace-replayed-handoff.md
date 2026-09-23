# Handoff: the `$dom` arc closed — the "decoder recipe" was three stacked solver bugs, the two-array trace replays, and what remains of the TLA+ map (2026-09-23)

**From:** the session that took
`docs/handovers/2026-09-22-dom-pair-budget-handoff.md`'s item 1 —
"don't-care completion in the trace decoder" — as its brief. Read
`AGENTS.md` first, then the 2026-09-22 handoffs (array-alias soundness,
dom-pair budget); this document assumes both.

## The headline: the recipe's premise was wrong, and digging past it found a false `sat`

The handoff's recipe said: fix `trace.rs`'s array arm to walk the
model-assigned store chain. The session verified the premise at solver
level first — and the model the decoder was reading was **incoherent**:
the pipeline's j=4 query committed *jointly contradictory* array
equalities (`x@1 = x@2` true AND `x@2 = store(x@1,1,1)` true AND
`x@1 = init-chain` true — extensionality forces 1 = 0), the theory never
refuted them, the model builder recorded an arbitrary subset of the
contradictory chains, and no decoder completion could have replayed.

Minimized, both shapes were **false `sat` on UNSAT formulas** (Z3
4.16.0: `unsat`):

```scheme
;; A                                          ;; B (the BMC shape)
(assert (= f (store b1 1 1)))                 (assert (= x1 x2))
(assert (= f g))                              (assert (= x2 (store x1 1 1)))
(assert (= g (store b2 1 2)))                 (assert (= x1 (store (store b 1 0) 2 0)))
```

Root cause: every family in the lazy array-axiom engine was gated on
something *observed* (a select term, a read index, a separated pair), and
an equality-only contradiction observes nothing. **The fix is Z3's eager
axiom 1** (`assert_store_axiom1_core`, cross-checked against CVC5):
one unconditional unit `select(store(b,i,v), i) = v` per store term. The
self-reads pin the written values into the E-graph, EUF congruence closes
over the merged arrays' self-reads, and colliding writes surface as an
ordinary congruence conflict. `build_store_self_reads` in
`array_axioms.rs`; pinned by `store_self_read_tests` (two unsat shapes,
two sat controls).

The full causal stack and the layers-examined record is
`docs/studies/2026-09-23-equality-only-array-false-sat.md`. In brief,
below the theory fix sat two more defects the decoder symptom had been
papering over:

- **`model_builder.rs`**: the EUF-reconcile pass installed occurs-check-
  violating entries (`x@0 -> store(x@0,1,1)`, on which `Model::eval`
  ping-pongs — now occurs-guarded), and array *aliases* (`x@2 = x@1`)
  were never recorded (now a second pass after the store pass, resolved
  through existing entries, with an end-of-build dereference pass so
  `f -> g` prints as `g`'s chain; self-referential shapes keep the raw
  name, which the walk follows one hop later).
- **`select_in` (`solver/types.rs`)**: an alias assignment broke the
  chain walk — the minted select matched nothing and the point read back
  unconstrained. The walk now follows aliases (cycle-guarded). This is
  the handoff recipe's walk, implemented where the semantics lives so
  `get-value` and the decoder share one walk.

With all three fixed, `trace.rs`'s don't-care completion needed **no
algorithmic change** — the minted select now routes through a coherent
chain+alias walk, the sort default stays the last resort, and the replay
has the final word. (The stale "Model::eval has no case for the array
theory" comments — false since the 2026-09-14 fix — are corrected.)

## The success criterion, met

`a_two_array_pluscal_spec_never_answers_a_false_clean` now pins era four
of its contract: `Violation { step: 4 }` AND `Replayed` (was
`NotReplayed`). The decoded trace shows `x` taking the taken branch's
value at every state (`<<0,0>> → <<0,2>> → <<1,2>> → …`), the *second*
counterexample (after `block_counterexample`) replays too, and
DiningPhilosophers `ExclusiveAccess` NP=2 completes clean through depth 6
(TLC agrees the property holds) with depths 7–8 still the standing
capacity wall; a deliberately false DP invariant decodes a 0-step
counterexample with the documented honest `ASSUME`-`Nat` replay decline.

## Verification bar (all green on the landed tree)

12,353 workspace tests; Z3 parity 100 %, 0 decisive mismatches (z3
4.16.0); perf gate PASS (conflicts 1.000, decisions 1.000, wall 1.00,
baseline `28e82c65`); `tla_bmc` full corpus — **verdicts and replay tally
byte-identical** before/after (318 specs: 68 clean / 21 violations — 19
replayed, 1 not decodable, 1 decoded-not-replayed / 4 undecided; the
corpus never reaches the new code paths, which is why nothing moved);
clippy `-D warnings`, fmt, doc clean. A one-line drive-by was needed to
make the clippy bar pass *at all* on clean HEAD: `nixie-sat`'s
`check_fixpoint` env probe was `debug_assertions`-gated at its only call
site but unconditionally defined — release clippy saw it dead (its own
commit).

Binaries cached at `precompile/<sha>/` (`nixie`, `nixie-tla`) for the
landed commit.

## Where this leaves the TLA+ map

1. **`Bag`-sort bridge / lambda-shaped function encoding** — now the
   named next step, unchanged from the earlier handoffs; design note
   first. The multiprocess workload (35 PlusCal files) now has a working
   counterexample path end to end, which the bag work can build on.
2. **Delta-propagation proof obligation** (study item 85) — still
   waiting, not urgent.
3. **DP depths 7–8** — pure capacity (query size), not correctness;
   relevant only if the unrolling encoding is ever reworked.

## Traps (new this session; the standing ones still stand)

- **The model builder's reconcile/repair passes can install values the
  recording pass would have declined.** Any pass that writes model
  entries must repeat the occurs check; "the recording loop already
  checks" is false the moment a second writer exists. Same lesson as the
  peek-then-pop `expect`: every writer re-validates.
- **A pinned `NotReplayed`/`Unknown` can be masking a solver bug.** The
  honest-decline machinery worked exactly as designed — but "the reader
  fell short" was the wrong layer; the model itself was impossible. When
  a replay rejects, dump the committed equality set before touching the
  decoder (`[modelarr]`-style logging was the lever; `brancharr` /
  `execute_script` probes at solver level are the template).
- **Z3 answers `sat` on `f = store(base,1,1) ∧ f = base`** — it is
  satisfiable (`base[1] = 1` makes the write a no-op). The unsat shape
  needs *different* write values at the *same* index, or an alias plus an
  init chain. Verify every probe against Z3 before believing it.
- The `/media/data` 100 %-during-builds and main-contention traps from
  the previous handoffs both fired again this session; the retry-push
  loop and worktree discipline still apply.
