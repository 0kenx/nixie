# Handoff: the PlusCal wall — the TLA+ side's single biggest coverage lever, handed to its next owner (2026-09-21, night)

**From:** the gap-filling session that closed the attribution arc's
unowned items (snapshot, tree-health validation, ndir2, the deep-split
deletion) — PlusCal was the one standing item whose owner never
picked it up across three handoff generations
(`2026-09-19-arc-closed.md` item 1 → the attribution-arc close-out →
today).  **Read `AGENTS.md` first** (the reference-first rule decides
the whole route below).  Successor context:
`docs/handovers/2026-09-19-tla-bags.md` (the TLA+ front end's state,
the parity gates, the bag vocabulary) — read it before touching
`nixie-tla*`.

## Where the wall is (verified this session, current tree)

* The TLA+ front end is in strong shape: **both parity gates green**
  (syntax+levels 4 970 definitions, 0 mismatches; semantics 1 111
  evaluated, 0 mismatches vs TLC 1.7.4), the bag vocabulary landed
  end to end, BMC honest-decline contracts documented in
  `bench/tla_bmc/METHODOLOGY.md`.
* **PlusCal bodies are TLA+ COMMENTS** (`(* --algorithm … *)`).  The
  current parser therefore *accepts* every PlusCal spec and silently
  ignores the algorithm — the parity gates run green over these files
  because only the surrounding plain-TLA+ definitions are ever seen.
  Nothing is broken; a whole specification layer is simply absent.
* **The corpus surface (measured, not estimated)**:
  `../temp/tlaplus-examples` holds **424 `.tla` files; 7 carry
  PlusCal bodies** — `KVsnap`, `Slush`, `QueensPluscal` (+ a
  `.toolbox` duplicate — skip it), `MultiPaxos`, `Sailfish`,
  `DiningPhilosophers`.  All use the single-`--algorithm` form;
  three have `process` blocks; none use `procedure`.
* **A correction to the record**: `Nano.tla` — named in two handoffs
  as "blocked on PlusCal" — has **no PlusCal body** (verified: no
  `--algorithm` marker; it is plain TLA+ with Init/Next and the
  `MC*.cfg` models in its toolbox).  Its actual blockers are the two
  documented bag-BMC declines (state-bag updates, `DOMAIN`
  quantifiers — the lambda-shaped function encoding / `Bag`-sort
  bridge, `2026-09-19-arc-closed.md` item 3).  The PlusCal value
  claim stands on the 7 real PCal specs, not on Nano.

## The reference (AGENTS.md rule: read it before writing any of this)

The normative PlusCal translator is **tla2tools' `pcal` package**
(92 classes in the oracle jar).  Verified working, this session:

```
JAR=/nix/store/1gvxsv5mxv2jknqbb6f2nrlmpw1x7nqi-tlaplus-1.7.4/share/java/tla2tools.jar
java -cp "$JAR" pcal.trans DiningPhilosophers.tla
# -> translated .tla (Init/Next/vars + one action per process) + .cfg + .old backup
```

`pcal.trans` is the standalone entry (`pcal/Translator` the API);
SANY also auto-translates on parse.  The output shape verified on
DiningPhilosophers: `vars == <<…>>`, `Init == …`, and
`Next == \E self \in ProcSet : Action(self)` — one labeled statement
cluster per atomic step.  **The route is golden-output parity**, not
reimplementation-from-memory: translate all 7 corpus files with
`pcal.trans` FIRST, and build our translator against those outputs
(parse+level parity on the translated defs, eval parity on the
translated Init/successor states vs TLC — the existing harnesses
extend directly).  The PCal grammar subset the corpus actually uses
(assign, await, if, while, with, either, call→macro-free, skip,
labels, process sets, `define` blocks) is small; the *semantics* live
in label placement — see the traps.

## The route, in order

1. **Extract** the `(* --algorithm … *)` / `--process` bodies from
   the comment stream (nested `(* *)`/paren balancing is a real
   lexer concern — the bodies contain full TLA+ expressions).
2. **Parse** the PCal grammar (corpus-sized subset above; the full
   grammar is `pcal/`'s parser classes — read them, don't guess).
3. **Translate** to plain TLA+ text/AST: the process-set
   instantiation (`self`), `Init`, `Next` as the disjunction over
   processes × labels, the `vars` tuple, macro expansion.  Emit
   **without fairness** first (`pcal.trans -nofairness` is the
   matching reference flag) — `lower.rs` currently *declines*
   `WF_`/`SF_` (`ExprKind::Fairness`, ~L2527), and pcal's default
   emits `WF_vars(Next)` per process; a default-fairness translation
   would land straight on that decline.  Fairness is a follow-up,
   not a first slice.
4. **Feed the existing pipeline unchanged** — the translation's
   output is ordinary TLA+; `nixie-tla` parse → levels → lower →
   eval, and `nixie-tla-check` BMC, all run on it as-is.  BMC smoke
   targets: DiningPhilosophers (the classic), QueensPluscal, KVsnap.

## The verification bar

* `nixie-tla`/`nixie-tla-check`/`nixie-tla-syntax` suites green; the
  two parity gates stay green AND widen: translated-def parse/level
  parity against the pcal golden outputs, translated-state eval
  parity vs TLC (the `tla_eval` harness already drives TLC per-file).
* BMC on the translated specs: honest `Violation`/`NoViolationWithin`
  verdicts with independent trace replays (the standing
  `METHODOLOGY.md` contract); declines name their wall.
* clippy/fmt clean; the workspace bar for anything touching shared
  crates.

## Traps (this session's, plus the standing ones)

* **Labels are the semantics**: a statement cluster between labels is
  one atomic step; getting label placement wrong yields specs that
  parse, typecheck, and answer wrongly.  The eval-parity gate is the
  catcher — never trust parse-parity alone.
* `pcal.trans` rewrites the input file in place (keeps `.old`) — run
  it in a scratch copy, never on the corpus in place.
* The `.toolbox` duplicate (QueensPluscal) is a model-instance copy —
  one file, not two data points.
* `pcal`'s translation of `await` inside a label cluster is a
  conjunct guard (no step), not a block — mirror it exactly.
* Process sets can be expressions (`1..NP`), not just named
  CONSTANTSs; `self` is universally quantified in `Next`.
* Standing environment traps: `/media/data` swings to 100 % (build
  under a root-fs `CARGO_TARGET_DIR`); `/tmp` is wiped mid-session
  (scratch under `~/.cache/nixie-scratch/`); the TLA parity scripts
  already honor `CARGO_TARGET_DIR` (keep it that way).

## Sizing

The corpus subset is genuinely small (no `procedure`, no `either`
nests beyond one level in most files, three `process` users).  The
work is a session-scale extractor+parser+translator plus the parity
wiring — **provided** the golden outputs are built first and the
label semantics are treated as the correctness core, not a detail.
The payoff: 7 corpus specs × their toolboxes currently invisible to
the whole TLA+ path, and the "PlusCal wall" line finally comes off
three handoffs' open lists.

## Where this leaves the TLA+ open map

1. PlusCal (this handoff).
2. The `Bag`-sort bridge / lambda-shaped function encoding (the two
   bag-BMC declines — design-sized, workload-gated).
3. The delta-propagation proof obligation (study item 85 — the
   boundary argument written, the canary standing).
