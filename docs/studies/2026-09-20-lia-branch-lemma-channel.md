# The CDCL-visible LIA branch channel — item 96's implementation, pre-registered (2026-09-20)

> **Coordination:** a parallel session built the same channel
> independently (`364c9c90`), measured it, and **reverted theirs in favor
> of this implementation** (`e2b45aaf` + the study
> `2026-09-20-lia-branch-channel-built-gated.md`).  Their measurements
> are inherited as prior evidence; the pre-registration below was written
> BEFORE any armed run of THIS implementation.

## The design (this implementation)

The pure-addition variant: the channel ADDS the CDCL dimension and
changes nothing else.

* **Theory** (`ArithSolver`): at the internal integrality search's budget
  decline (`lia_cuts_then_bnb`'s `LIA_MAX_DEPTH`/`LIA_MAX_NODES` return —
  item 96's ray signature), record one `LiaBranchRequest` (the fractional
  var's recorded form + `k = ceil(exact)`) — a REQUEST, not a constraint;
  the verdict of the declining check is `Unknown` either way.  Armed by
  `NIXIE_LIA_BRANCH_LEMMA=1`; unarmed = the request list stays empty.
* **Solver** (`check_core_solving`'s `resource_exhausted` Sat arm): only
  when the exhaustion is a PURE arith abstention (`abstention_exhausted`,
  a new precise flag set only at the arith-`Unknown` arm — never at
  dropped-conflict/error arms, which must stay sticky through any
  rebuild), drain the requests, mint `(>= form rhs+k)` as a fresh atom
  (`encode_depth(.., 0)`, phase-hinted true, memoized on the hash-consed
  term), and re-solve (the int-case-split reset-restart shape; SAT keeps
  its learned clauses).  Round cap 64.
* No internal budget is cut (the parallel session's armed variant cut the
  internal budget to a pivot cap and REGRESSED `v20_problem__019`
  `sat→timeout` — the exact trade this variant cannot make: instances the
  internal search solves never decline, never request, never round).

## Prior evidence inherited (the parallel session's measurements)

* Default-off is bit-identical on the standing LIA cells (32/32, conflicts
  equal) — the bar this landing must reproduce with its own code.
* The CAV family's per-LP churn (~2 s per post-cut re-feasibilization)
  starves round-trips entirely — the channel is not expected to move CAV
  until the fraction-free rows layer lands.
* The ray family (item 96's 24 members) is the predicted immediate
  beneficiary: z3 decides every one through CDCL-visible branching.

## PRE-REGISTRATION (written before the armed runs)

* **Go bar (telemetry rung)**: ≥5 of the ray-class members (the ~24
  fixed-seed survey members whose unarmed exit tag is
  `lia:bnb-depth-budget`) recover — nixie decisive, verdict agreeing with
  z3, every published model validated by binding + negation — with zero
  wrong verdicts anywhere (the wrong-verdict ledger stays empty), AND
  default-off verified trajectory-inert (bit-identical counters on the
  gate corpus + parity clean).
* **Falsification**: ≤2 ray members recovered; or the armed survey delta
  is dominated by members OUTSIDE the ray class (reshuffle, not
  mechanism); or any verdict disagreement or refuted model; or
  default-off moves any counter.
* **Cost side**: no unarmed-visible change; armed timeouts on the fixed
  seeds recorded as-is (the channel's price is part of the treatment).
* **Matched null** (required only if the go bar passes, before any
  default flip): the same minting machinery, same decline cadence, same
  cap, with k scrambled to a semantically useless-but-valid split (k = 0
  — a valid dichotomy for any int form, carrying no LP-point
  information).  Treatment must beat the null on the ray set; a null that
  recovers as many means the recovery is the minting perturbation, not
  the branch semantics.
* **Escalation**: telemetry (this rung) → armed A/B with the null →
  default flip only with the full §2/§5 machinery (≥10 seeds, per-family
  breakdowns, benchstore records).

## Run log

(filled below as runs complete)

## Run log (the telemetry rung, 2026-09-20)

**Binaries**: unarmed = `precompile/8f21f9e5/nixie` (behaviorally identical
to the worktree base — the parallel session's default-off bit-identity bar);
armed = the worktree build.  z3 4.16.0.  Fixed seeds 20261000–02 × 600.

**Default-off trajectory-inertness**: perf gate vs the pinned baseline —
**PASS, conflicts/decisions bit-identical 1.000/1.000** (n=9, wall 0.91).
The pre-registered inertness bar holds for this implementation's own code.

**Armed survey**: 77 → **55 members** (22 left the unarmed manifest, 0
newly-unknown).  Validated member-by-member (armed verdict vs z3, then
model binding + negation in z3):

* **16 genuine recoveries** — armed `sat`, z3 `sat`, and every published
  model z3-validates by binding the `define-fun`s and re-solving the
  negated conjunction (`unsat`).  **Zero false models; the wrong-verdict
  ledger stays empty.**
* **6 timeout-class flips** — the armed searches on these members run
  21 s – >120 s (the survey's 10 s cap times them out; at 60–120 s they
  answer honest `unknown`).  The channel's cost side, recorded as-is:
  arming makes some searches SLOWER (the split round-trips replace
  internal-search progress — the same trade the parallel session measured
  on `v20_problem__019` for budget cuts; here it appears on 6 of 1800
  instances).

**Matched null** (same minting machinery, same decline cadence, `k`
scrambled to 0 — a valid but LP-point-free dichotomy; env
`NIXIE_LIA_BRANCH_NULL=1`):

| arm | members | recovered | decisive+agree | slow-flips | wrong |
|---|---|---|---|---|---|
| unarmed | 77 | — | — | — | 0 |
| treatment (armed) | 55 | 22 | 16 (all models validated) | 6 | 0 |
| matched null | 65 | 12 | 11 | 1 | 0 |

**Treatment-only recoveries: 10; null-only: 0** — clean dominance.  The
branch-point semantics own 10 members the minting perturbation cannot
reach; the other 12 recoveries are perturbation-class (trajectory
reshuffle landing well — §11.1's "gains must concentrate" check: they
concentrate on the same capacity family, and the null bounds them).

**Pre-registered verdict: GO BAR PASSED** (≥5 ray-class validated
recoveries — i142/i113/i139/i187/i46 are ray-tagged and validated; zero
wrong verdicts; default-off bit-identical; the falsification criteria did
not fire).  The escalation ladder's next rung (default flip) still needs
the full §2/§5 machinery: ≥10 seeds, per-family breakdowns, benchstore
records — and the armed differentials below are the standing screen.

**Where the first armed decode went** (the debugging trail, recorded
because it maps the plumbing): the channel initially minted nothing —
(1) the ray forms are WIDE (`exact: true`, beyond-i64 branch points), so
the rung-1 i64/exact gates skipped exactly the target class — widened to
`BigInt` (`mk_int` takes it natively); (2) the abstention flag landed on
the fixpoint-loop's arith arm while the ray members flow through
`final_check`'s OWN arith-Unknown arm (`theory_manager.rs`, the
`TheoryCheckResult::Unknown` match) — flagged there too.  After both:
request → abstention gate → mint → reset-restart round, end to end.
The first recovered member decoded (i116) moved ray → J5-certify (the
armed search reaches a candidate that fails the big-const certification —
the channel exposes the J5 class as the next blocker IN SERIES on that
member); the 16 recoveries are members whose armed searches find
certifiable models.

**Armed unit/e2e pins landed**: the queue contract + default-off
inertness (theory), and the armed-verdict regression on the recovered
i142 instance (solver e2e, ~12 s — above the survey's 10 s cap, the cost
side in miniature).

## The landing battery (default-off code, final tree)

* Workspace suite **12 061 passed / 15 failed — every failure the
  documented corpus-missing-in-worktree class** (known_unsound ×8,
  model_soundness ×2, qfidl ×5 — re-verified against pristine e2b45aaf:
  pass in the primary checkout); `si2_b03m` is the same class (the SAT
  corpus file).
* clippy (`-D warnings`) / fmt / `RUSTDOCFLAGS="-D warnings" cargo doc`:
  clean (one doc-link de-link for the crate-private `LiaBranchRequest`).
* Parity **176/177 Correct, 0 wrong** (z3 4.16.0).
* Perf gate default-off: **PASS, counters bit-identical 1.000/1.000**.
* Differentials: 3×400 mixed + 3×300 wide at DEFAULT, and — the armed
  soundness screen — 3×400 mixed + 3×300 wide with
  `NIXIE_LIA_BRANCH_LEMMA=1` (seeds 20262330-32/40-42 default,
  20262350-52/60-62 armed): **twelve runs, zero verdict disagreements,
  zero refuted models.**
* Pins: the queue/default-off/reset contract (theory, unit) and the
  armed-verdict regression on the recovered i142 instance (e2e, ~13 s).

## Traps recorded (do not repeat)

* **String surgery on test files is corpus corruption waiting to
  happen**: an `index("    );\n}\n")` splice for inserting a test matched
  a `);` + `}` in the MIDDLE of the file and replaced 88 lines of
  unrelated regressions with the generated block — surfacing as a
  default-off "regression" (`empty_row_with_fractional_constant_is_refuted`
  `unknown` instead of `sat`) that bisected to FILE CORRUPTION, not the
  channel (pristine-base + restored-file control).  Append at EOF or edit
  with unique anchors; verify with `git diff --stat` before running.
* **`cfg(test)`-gated statics read by production code do not exist in
  release** — the channel's force-flag static must be always-present.
* The abstention flag has TWO arith-Unknown arms (the fixpoint loop's and
  `final_check`'s own) — the ray members flow through `final_check`'s;
  flag both or the gate never opens.

## Where this leaves the ladder

Rung 2 (flag-gated A/B with the matched null) is DONE — go bar passed,
null dominance measured, ledger empty.  Rung 3 (default flip) requires
the full §5 machinery: ≥10 seeds per arm, per-family breakdowns,
benchstore records, and a cost decision on the 6 slow flips (the 10 s-cap
class; two members exceed 120 s armed).  The armed differentials are the
standing soundness screen either way.  The channel stays default-off
until that campaign runs.

## PRE-REGISTRATION — rung 3, the default-flip campaign (written before the runs)

**Binary**: `precompile/9ff377ff/nixie` (current main: the branch channel
plus the SAT-side CSR flip, which reshuffles trajectories — the campaign
re-baselines everything on THIS tree).  One binary, three env arms —
perfect common-random-numbers pairing:

* **A0 unarmed** (the landed default),
* **A1 treatment** (`NIXIE_LIA_BRANCH_LEMMA=1`),
* **A2 matched null** (`NIXIE_LIA_BRANCH_LEMMA=1 NIXIE_LIA_BRANCH_NULL=1`).

**Cells**: 12 seeds × 600 instances × 3 arms (the standing 20261000–02 for
continuity with every prior attribution, plus fresh 20262400–20262408).
z3 4.16.0 decides every instance in every arm (the generator is
seed-deterministic; CRN holds by construction).

**Go bar for the default flip** (ALL must hold):
1. **Consistency**: A1 recovers members over A0 on ≥10 of the 12 seeds
   (net recoveries > 0 per seed), and A0 recovers over A1 on NO seed
   (no verdict-loss seed).
2. **Ledger**: zero wrong verdicts anywhere; every A1-recovered member
   validated (armed verdict == z3, model binding + negation `unsat` in
   z3); no member DECISIVE in A0 becomes non-decisive in A1 (a verdict
   loss — timeouts on formerly-decisive members are an automatic no-go).
3. **Cost**: A1's timeout count ≤ A0's + 3 per seed on average, and the
   slow-flip class (unknown→slower-unknown) does not exceed the recovery
   count net.
4. **Null dominance holds at scale**: A1's recoveries exceed A2's pooled
   over the 12 seeds (the fixed-seed point estimate was 22 vs 12).
5. **Fresh-seed armed differentials clean** (3×400 mixed + 3×300 wide,
   zero disagreements).

**No-go**: any criterion failing → the channel stays default-off; the
measurements land as the record.

**Decision**: if go, the flip lands under the enablement rule (the
soundness argument is structural — the minted dichotomy is a theory
tautology, the abstention-only guard, the memo/caps — plus the screening
above), with the full battery at the new default and the perf gate
re-run (the gate corpus is pure SAT; the channel cannot fire there).

## Run log — rung 3, the default-flip campaign (results)

**All five pre-registered criteria PASSED; the flip landed.**

* **Consistency**: A1 genuine recoveries on **11/12 seeds** (seed 20262402:
  zero recoveries, zero losses).  Manifest-diff candidates 59; the honest
  split (sequential quiet-machine validation — the manifest diff
  conflates recoveries with timeout-under-load flips in BOTH directions;
  9-parallel survey load pushes 6-15 s runs past the 10 s cap):
  **42 genuine (40 sat + 2 unsat), 18 slow-class** (14 unknown + 4 >150 s).
  Determinism re-verified: zero verdict flaps across repeat runs.
* **Ledger**: zero wrong verdicts anywhere; **all 40 sat models
  z3-validated by binding + negation** (`unsat`), zero false models; the
  single "lost" candidate decoded as a timeout↔unknown boundary flip on
  an instance A0 was never decisive on (honest `unknown` at 10 s and
  60 s, z3 `sat`).
* **Cost**: survey timeouts 95 → 119 (**+2.0/seed**, bound +3); the null
  sits between (104) — even the perturbation costs timeouts.
* **Null dominance at scale**: genuine A1 42 vs genuine A2 28
  (A1-only ≈ 18).  The fixed-seed point estimate (22 vs 12) held.
* **Fresh-seed armed differentials**: 3×400 mixed (20262420-22) + 3×300
  wide (20262430-32) — zero disagreements, zero refuted models.

**The flip** (`NIXIE_LIA_BRANCH_LEMMA` default armed; `=0` restores the
unarmed search — the SAT CSR flip's opt-out shape): landed with the full
battery at the new default — suite 12 063 passed (the 15 failures are the
documented corpus-missing class; 5 first-run timeouts were load
artifacts, all passing on the re-run), clippy/fmt/rustdoc clean (fixing a
landed graph-tests clippy breakage in passing), parity **176/177 Correct
0 wrong** (z3 4.16.0), perf gate PASS (pure-SAT corpus, counters
identical — the channel cannot fire there), 3×400 mixed (20262470-72) +
3×300 wide (20262480-82) fresh differentials at the DEFAULT clean, panic
sweep recorded below.

**Traps recorded**: (1) **/tmp is age-cleaned mid-session** — the battery
lost binaries, targets and logs to a tmpfiles sweep; session artifacts
now live in the worktree (`artifacts/`), never /tmp.  (2) The manifest
diff's "recoveries" are load-contaminated in both directions — the honest
count needs sequential direct validation (the 12-seed campaign's 59
candidates contained 18 timeout flips).  (3) Parallel-machine ENOSPC
killed two battery attempts (target2/target3 on a shared 100%-full
disk); serialize on ONE target dir and clean aggressively.

## Addendum — the J5-(a) class closed: the certificate fallback (same day, next session)

The post-flip re-attribution (55 members: 51 J5 / 3 ray→J5 / 1 smx) made
the J5-certify class 100% of the actionable gap.  Decoded on i116 (the
ray member the channel had moved into J5):

* The candidate model is **z3-VALID** (binding + negation `unsat`) — the
  armed search finds genuine models.
* `certify_quantified_sat` **declines without evaluating**: mixed
  Int/Real goals are refused by BOTH MBQI certifier engines (the real
  engine rejects integer-sorted symbols, the integer engine reals) — a
  FRAGMENT decline, not a refutation.  The gate then discarded the valid
  model.

**The fix** (15 lines): the J5 gate falls back to
[`Solver::model_certifies_assertions`] — the value-only exact certificate
(the pure-BV dispatch's Sat contract): it evaluates the ORIGINAL
assertions under the model with the true big constants, fails closed on
anything undecided, and never consults the SAT core's polarities.  A
pass is a positive verification — exactly what the gate demands of the
big-const abstraction.

**Measured**: the fixed-seed post-flip survey **55 → 18 members** (37
recovered); all 37 verdicts agree with z3; **all 37 models validated by
binding + negation** (`unsat`), zero false models.  The residual 18: the
J5-(b) class (candidates the certificate genuinely REFUTES — item 89's
dive-leaf divergence, still open) plus the ray/smx tails.

Battery: workspace suite 12 078 passed (15 = documented corpus-missing
class; one load-artifact timeout passed on re-run); clippy/fmt/rustdoc
clean; parity **176/177 Correct 0 wrong** (z3 4.16.0); perf gate PASS;
3×400 mixed (20262500-02) + 3×300 wide (20262510-12) + a clean-build
1×400 (20262520) fresh differentials — zero disagreements, zero refuted
models; debug panic sweep 177/177.

## Addendum 2 — J5-(b2) closed: the certificate learns div/mod and equality (same day)

The residual 18 (post-J5-(a)) re-attributed on the current tree (with the
parallel sessions' assert-fold landing: 6+9+3 across the fixed seeds,
same count): 17 J5 / 1 simplex-rl.  Decoded on i31: the certificate
returned `Undetermined` — **`Div`/`Mod` terms had NO case in the shared
evaluator** (they fell to the opaque-leaf catch-all; a div/mod term is
never in the model assignments), and after that fix the remaining blocker
was **`combine_eq`'s designed collision-conservativeness**: the model
makes the disjunct `(= lhs -2)` TRUE by an exact collision (`-2 = -2`),
but the shared `=` returns `Undetermined` on equal numerics — correct for
the REFUTATION gates (a collision must never veto a `not (= ..)`
candidate) and over-conservative for the CERTIFICATE's positive
direction.

**The fixes**:
* `EagerKind::IntDiv`/`IntMod` + `combine_int_div_mod`: EXACT Euclidean
  div/mod on `BigInt` operands (`a = b·q + r, 0 ≤ r < |b|`), fail-closed
  on a zero divisor (SMT-LIB leaves it uninterpreted) and on non-integral
  operand values.
* `EagerKind::EqCertify` + `combine_eq_certify`, selected by the
  evaluation-local `eq_collision_verifies` mode `model_certifies_assertions`
  sets around its evaluations: an exact collision VERIFIES the equality
  (it holds under the assignment), distinct falsifies (narrow and big,
  mixed via `to_big`); the refutation gates keep `combine_eq` untouched.
  In certificate mode `not (= ..)` over a collision now correctly
  REFUSES (the candidate violates its own assertion) — the asymmetry the
  two gates always needed.

**Measured**: the fixed-seed survey **18 → 2 members** (16 recovered);
all 16 verdicts z3-agreeing; **all 16 models z3-validated by binding +
negation**; zero false models; the ledger empty.  The residual 2: i504
(another `Undetermined` source — a linear-arithmetic one, no div/mod in
the tree; the next decode) and i129 (the simplex resource-limit tail).

Unit pins: the Euclidean sign table, the fail-closed classes, and the
collision-semantics asymmetry (both directions of both gates).

Battery: workspace suite 12 096 passed (15 = the documented
corpus-missing class); clippy/fmt/rustdoc clean; parity 176/177 Correct
0 wrong (z3 4.16.0); perf gate PASS; 3×400 mixed (20262530-32) + 3×300
wide (20262540-42) fresh differentials clean; debug panic sweep 177/177.

## Addendum 3 — i504 closed: the certificate verifies the PUBLISHED model (δ-instantiated); 18 → 1

The last J5 member (i504) decoded layer by layer (a session of probe
traps: manual re-evaluations outside the certificate mode and probes read
after the mode's RESTORE are both misleading — probe before the restore):

* The refusing conjunct is `not (or ..)`: three disjuncts false, the last
  a MIXED `Mul(real·int) > 4` whose operands read exactly `4 > 4` — the
  strict-at-boundary soften.
* The candidate's model is **z3-VALID** (forced-certification + binding +
  negation) — the certificate was evaluating a DIFFERENT point than the
  model it publishes (live tableau reads vs the published snapshot —
  item 90's popped-state divergence, now on the certificate side).

**The fixes** (three pieces, all fail-closed):
1. **Certificate-mode user-var reads are MODEL-FIRST**: the value the
   model PUBLISHES (including compound constant spellings — evaluated
   exactly through the same evaluator) wins over the live tableau; the
   certificate verifies what `get-model` will print.
2. **δ-instantiation for live real reads** (`certify_delta0`, computed
   once per certificate from `ArithSolver::delta_instantiation_exact`,
   now exposed): a live real var reads `real + δ₀·delta` — concrete, so
   strict comparisons at the boundary DECIDE.  `None` (no valid δ₀)
   keeps the honest soften.
3. **`CmpStrictCertify` with read provenance** (a thread-local
   live-read flag, reset per conjunct): strict-at-equality is decisively
   FALSE when every contributing read was concrete (published or
   δ₀-instantiated — `a > a` is false under the published point); a live
   read may have dropped a positive delta, where equality stays
   ambiguous (the soften, as ever).

**Measured**: i504 answers `sat` (model z3-validated by binding +
negation); the fixed-seed survey residual is now **1 member** (i129, the
simplex resource-limit tail — a different class entirely).  Unit pin:
the concrete-strict-at-equality semantics and the provenance govern.

Battery: workspace suite 12 097 passed (15 = the documented
corpus-missing class); clippy/fmt/rustdoc clean; parity 176/177 Correct
0 wrong (z3 4.16.0); perf gate PASS; 3×400 mixed (20262550-52) + 3×300
wide (20262560-62) fresh differentials clean; debug panic sweep 177/177.

The arc's cumulative fixed-seed survey run: 150 → … → 18 → 2 → **1**.

## Addendum 4 — the fresh-seed hunt: 8 members, the J5-blocking route closes 2, the simplex family (6) named

Fresh seeds 20262600–02 × 600 on `precompile/286f63bd/nixie` (the fixed
seeds exhausted at 1): **8 members (~2.7/seed — the arc's fixes
generalize)**.  Attribution: **2 J5-certify + 6 simplex resource-limit
family** (`smx-rl:make_feasible`/`smx-rl:check`, one with a branch
request fired).

The 2 J5 members decoded: the certificate now **REFUTES** both
(`Bool(false)`) — the genuinely-bad-candidate class at last (item 89's
dive-leaf divergence).  The routing fix: a REFUTED candidate is
**blocked-and-retried** (the J17 route the J5 gate always bypassed —
item 88 mapped this years-of-items ago): the certificate's tri-state
(`Pass`/`Refuted`/`Undecided` — declines are never blocked; excluding an
undecided region can discard the good model), a bounded retry (8 rounds)
through `block_refuted_model_and_rebase` + re-solve.  **Both members
recovered with z3-validated models; the 6 simplex members unchanged**
(their class is elsewhere).  Fresh-seed residual: **6 members, all the
simplex pivot-cap/resource-limit family** — the next campaign's target
(the entry points: `make_feasible`'s pivot cap, `check`'s resource limit,
and the interplay with the branch channel's rounds).

Battery: workspace suite 12 098 passed (15 = the documented
corpus-missing class; the scope_rebase timeouts are load artifacts —
9/9 pass in isolation); clippy/fmt/rustdoc clean (the doc run needed a
root-disk target — /media/data hit 100% mid-battery again); parity
176/177 Correct 0 wrong (z3 4.16.0); perf gate PASS; 3×400 mixed
(20262610-12) + 3×300 wide (20262620-22) fresh differentials clean;
panic sweep 177/177.

The arc's survey ledger: fixed seeds at 1 (i129, the simplex tail — the
same family as the fresh-seed 6); fresh seeds at 6.
