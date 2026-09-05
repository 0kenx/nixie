# bench/obligation — certificate-carrying obligation-grammar fuzzer

A grammar fuzzer samples the syntactic space of SMT-LIB and mostly
produces trivially-solvable formulas. This tool instead generates
**reasoning obligations**: constraint networks whose difficulty is a
mathematical property of the construction, each shipped with an
independently checkable **certificate** for its expected answer.

```
Problem := ObligationProduction × TheoryRealization × RepresentationStress × QueryHistory
```

## Obligation productions

| Family      | Why it is hard                                                                 | Certificate |
|-------------|--------------------------------------------------------------------------------|-------------|
| `parity`    | Graph-parity obstruction: every proper subset of equations is satisfiable; the contradiction requires all of them (minimal global obstruction). | Charge-counting argument; GF(2)-elimination witness for the even case. |
| `capacity`  | Objects compete for insufficient resources (Hall deficit), with overlap/symmetry controls. | Planted injection (SAT) / deficient subset S with union(allowed) ⊂ R', |R'| < \|S\| (UNSAT). |
| `gap`       | Rational-feasible but integer-infeasible linear system — LP relaxation cannot see the conflict. | Integer row combination u: every entry of u·(2A) divisible by g, u·(2b) not; x = 1/2 satisfies every row exactly. |
| `reconverge`| Two provably equivalent computations with different structure asserted to differ (Shannon tree vs ANF; extract/concat permutation round-trips). | Exhaustive 2^k-input check / permutation composition; near-miss variants flip exactly one point (needle SAT). |
| `memory`    | Alias-ambiguous array write histories (storecomm-shaped); distinctness asserted, implied by arithmetic, or aliased. | Permutation invariance of non-overlapping writes (simulated); alias simulation for the SAT variant. |
| `boundary`  | Exact Euclidean div/mod distinctions that truncating rewrites erase. | Algebraic identities + exhaustive numeric verification in the generator. |

## Theory realizations

The *same* obstruction is emitted through different solver machinery:

- `parity`: mixed Bool+LIA in one instance (edge values linked across
  sorts — the obstruction must be reconciled across theories), width-1 BV
  XOR chains, Tseitin CNF, an exact div/mod-linked variant
  (`boundary` joined in), and a push/pop charge-toggle history.
- `capacity`: Bool exactly-one, LIA 0/1 sums, bounded UF with pairwise
  distinct applications (congruence meets arithmetic), CNF, incremental.
- `gap`: QF_LIA UNSAT with a QF_LRA SAT twin over the identical system —
  a differential pair that isolates integrality handling. `scale_log10`
  multiplies all constants by 10^k (exact) for numeral stress.
- `reconverge`: nested `ite`/`and`/`xor` trees vs nested
  `extract`/`concat` networks with `let` sharing.
- `memory`: `(Array Int Int)` fold chains under three alias regimes.

## Representation stress

`--stress mild|heavy` inserts tautologies over fresh variables *before
the first check-sat*: a d-deep `not` chain (`(not^d sdb) = sdb`, d even)
and a d-deep constant `+` chain with its exact sum — semantics-preserving
by construction, but they stress parsing, simplification, hash-consing
and stack discipline (deep input is a known bug class). For CNF, clauses
are duplicated (`dup` never changes satisfiability) and the header is
repaired.

## Query histories

Incremental instances interleave `push`/`pop` with `check-sat`s whose
expected answers are derived from the construction (e.g. parity charge
toggles: sat → unsat → sat). The runner compares the **full answer
vector**, not just the final query.

## Usage

```bash
cargo build --release                       # in bench/obligation

# generate a corpus to disk (deterministic: family x seed x size)
../target/release/obligation-gen --seeds 5 --size medium --out corpus/

# check the solver against the certificates (repo root):
../target/release/obligation-run --seeds 3 --size medium \
    --nixie target/release/nixie \
    --z3 z3 --cadical ../temp/cadical/build/cadical \
    --timeout-ms 10000

# stress sweep
../target/release/obligation-run --seeds 2 --size small --stress heavy ...
```

Or via the wrapper: `./run_smoke.sh` (from this directory).

## Oracles and verdicts

- **PASS**: solver answers match the certificate vector exactly.
- **FAIL**: a decided answer disagrees with the certificate.
- **CRASH**: nonzero exit or `(error ...)` output.
- **UNKNOWN / TIMEOUT**: inconclusive — reported, not counted as failure
  (`--strict` promotes them).
- **GENFAIL**: Z3 (or CaDiCaL, for CNF) disagrees with the certificate —
  the *generator* is suspect; investigated separately from solver bugs.

Artifacts (exact input, expected answers, certificate, nixie version) are
written to `obligation-artifacts/` on FAIL/CRASH/GENFAIL and never
auto-deleted. Timeouts use a poll/kill/reap loop — the solver process is
always reaped.

## Findings from the first campaigns (nixie 0.3.2, 2026-09-05)

Zero wrong answers across ~200 generated instances (small/medium/large,
plain and heavily stressed). The findings below are all *honest*
`unknown`/timeout/capability results, each with a z3 cross-check agreeing
with the certificate:

1. **Cross-theory parity undecided at ~26 vertices**
   (`parity-mixedboolint-*`, medium): nixie decides the pure-BV and
   pure-CNF realizations of the same obstruction but returns `unknown` on
   the mixed Bool+LIA encoding, in *both* polarities, and on the base
   `sat` query of the incremental history. Reconciling the XOR equations
   with the `sum(i_e) = c_v + 2*k_v` LIA equations across the
   `ite`-linked edge variables is where it stalls.
2. **Exact div/mod links block the refutation entirely**
   (`parity-mixedboundary-unsat-*`, all sizes): when the Bool→Int edge
   link is `i_e = (mod (div (ite b_e C1 C0) D) 2)` (exact on both
   constants), nixie answers `unknown`; z3 answers `unsat`.
3. **Deep right-nested binary `+` yields `unknown` on a foldable
   tautology** (`--stress heavy`): a 5000-deep
   `(+ c (+ c ... 0))` chain asserted equal to its exact sum is not
   decided; wide n-ary sums with 5000 terms *are* decided, and 5000-deep
   `not` chains are fine, so the gap is specific to right-nested binary
   arithmetic (also reproduces with deep `bvxor` chains). z3: `sat`.
   Minimal repro: `/tmp`-style two-liner — see `stress::apply_smt2`.
4. **Parser leniency** (observation, not an issue): nixie accepts `(_ extract
   i i x)` application syntax and top-level `(let ...)` commands; both are
   rejected by z3. Direction of divergence is safe — accepting a superset
   with correct semantics cannot wrong-answer — and the real defect was
   this generator emitting non-standard syntax (fixed; the z3 cross-check
   caught it in one run). No action intended on the parser.
5. **Scaling boundary** (`large`): 50-write offset-implied array
   histories and 60-vertex parity graphs exceed a 30s budget (timeouts,
   not wrong answers); an 11-variable `gap` system scaled by 10^9
   returns `unknown` where z3 decides `unsat`.

## What this is not

- Not a performance benchmark: no wall-clock comparisons (see
  `docs/BENCHMARKING.md` for that discipline). Difficulty knobs exist to
  reach *deeper into the reasoning*, not to race.
- Not coverage-guided yet: mechanism observability (did this instance
  actually trigger array lemmas / congruence merges / ...) is roadmap.

## Roadmap

- FP halfway/subnormal/rounding-mode boundary productions; string
  split-ambiguity productions; quantifier closure-growth (trigger chains,
  multi-patterns); CHC/PDR reachability ladders.
- Corpus mutation mode: type- and semantics-preserving rewrites of
  `smt-lib/non-incremental` inputs with agreement obligations.
- Coverage/telemetry-guided selection fed by solver statistics.
- Model validation: round-trip witness assignments through the solver
  (`--validate-model`) as an additional oracle.
