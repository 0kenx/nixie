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
