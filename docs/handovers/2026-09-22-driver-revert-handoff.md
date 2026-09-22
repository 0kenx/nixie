# Handoff: the driver revert — the mis-attribution owned, the arc's simplex story closed (2026-09-22, third session)

**Read `AGENTS.md` first — it is canonical.**  This executes the CAV
audit's open item to completion.  Studies:
`docs/studies/2026-09-22-driver-revert-attribution.md` (this landing —
the study wins), `2026-09-22-cav-regression-attribution.md` (the
audit + piece-level bisect), `2026-09-22-simplex-unified-feasibility-driver.md`
(the corrected campaign), `2026-09-22-lia-request-cadence.md` (the
cadence, still standing).

## What this landing is (`01dd9ca6`, binary at `precompile/01dd9ca6/nixie`)

The unified wide driver REVERTED (three pieces, verbatim to
`7687dc39`'s shapes): `find_violating` narrows again, `make_feasible`'s
wide-leaving branch is gone, `check`'s interleaved one-wide-repair loop
is restored.  **KEPT**: the preserve pair (S1-innocent, pinned by the
`rederivation_preserves_*` tests) and the request cadence
(`LIA_REQUEST_NODES = 64` — re-dosed on the reverted architecture:
231s walk vs 80s request on the fixed-seed corpus).

**The correction**: the driver campaign's "4 recoveries" were measured
against the stale entry base while the parallel integer-tableau
landings recovered those members underneath; the driver actually
REGRESSED i202/i445 (sat → timeout/unknown) and the CAV cells (S2).
The member matrix (all six sat on plain `7687dc39`) completed the
audit's picture.  On this tree: members 9–32 ms, CAV 011/025/034 sat
at pre-driver times, suite **12,138 passed / 0 failed** (the
`known_unsound` trio passes again), parity 176/177 0 wrong, gate PASS,
differentials clean.  Surveys: conflict-limit + J5 residual only.

## If this commit is on `driver-revert-landing` and not yet on main

The fsm certification session held main dirty in
`nixie-wt-fsmcert` when this landing was ready.  The commit is
battery-complete and binary-cached; fast-forward main when their tree
frees: `git merge --ff-only driver-revert-landing` from a clean main
checkout (or `git push . driver-revert-landing:main` once no worktree
holds main dirty).  Then delete the branch.

## The residual map (unchanged in kind)

1. **The conflict-limit class** (`check_core_solving`'s dropped-conflict
   arm): the dominant survey family.  Search capacity.
2. **`i551`:** the J5-`Undecided` certificate class.

## Traps this session (do not repeat)

* **Stale-base measurement**: a campaign that rebases mid-flight MUST
  re-run its baseline members on the CURRENT base before crediting
  recoveries to its own change — main racing underneath can recover
  them for you.  (This is the root of the driver mis-attribution.)
* **Member-regeneration scripts**: a missing seed in the loop leaves a
  stale file under the target name — a phantom verdict flip.  md5-
  verify regenerated members against a fresh single-seed generation
  (the "i566 false unsat" was exactly this).
* **`git checkout -- <file>` and worktree ops fail on a full /media/data**
  ("unable to write index.lock") — verify byte counts and grep state
  after every failure; the FS also flickers directories in and out of
  visibility transiently.
* **Never push a refspec with an empty source**: `git push . "$(cmd)":main`
  with a FAILING `cmd` becomes `:main` — a branch DELETION.  (Happened
  once; recovered via `git branch main <sha>` + ff.  Always quote-check
  the refspec expands non-empty.)

The one-sentence version: **the driver's recoveries were the tableau
session's, measured against a stale base — the revert restores every
cell to its best recorded state while keeping the two sound residues
(the preserve contract and the cadence), and the arc's simplex story
closes with the conflict-limit and J5 classes as the named residual.**
