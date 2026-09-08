# Conflict-analysis metadata fusion: rejected cost screen

The target is ordinary Nixie's cost per conflict. The user's `6333f83`
mode-matched panel still shows substantial wall time per conflict even on
instances with similar or fewer conflicts than Kissat. Solver tick totals
are not interchangeable with hardware cycles or with each other's counters.
This experiment changes the implementation of existing bookkeeping, with
exact search identity required; it introduces no search policy.

## Implementation and null

First-UIP resolution repeatedly fetches the same clause to increment usage,
read/promote its tier, check low glue, add activity and finally walk literals.
Replace that sequence with one validated header read, combined metadata writes,
and the ensuing literal view. Preserve the original-clause no-op, deleted
header behavior, saturating usage byte, Local/Mid/Core transition order,
unmodified flag bits, exact f32 addition, reduction recency/histogram updates,
and LRAT antecedent order. The clause-traffic observer must still see the
pre-update state. Keep the scalar sequence as a test-only oracle.

Baseline/null is the committed ordinary solver including the arena repair
landed with this registration. Pin its actual SHA and release binary hash in
the records before running anything. The candidate adds only the fusion and
its tests. Neither arm uses the rejected grouped watcher representation.
Both are built from clean committed sources with the same lockfile, compiler
and release settings. No dirty-tree binary is admissible.

This is an engineering comparison: the null does identical semantic work on
an identical trajectory. Any discrepancy in clauses, proof, model, counters
or observed state is a failed correctness gate, not evidence of a heuristic
benefit. Exhaust all usage/flag encodings and glue boundaries against the
original update sequence, compare explicit per-clause state in paired solves,
and independently check small SAT models and UNSAT LRAT proofs.

## Four fixed cells, no tuning

Use circuit_48in64out and j3037_10_mdd_bm1 from `satcomp2024/bench`, whose exact
content hashes are already recorded in the recent throughput studies. Run
baseline and candidate once each, seed 0, at 40,000 conflicts, CPU 10, CaDiCaL
preset, ordinary release features, `NIXIE_SWEEP=0`, model output enabled.
All other study overrides are cleared. Order: circuit baseline, circuit
candidate, j3037 candidate, j3037 baseline. Reuse an existing exact cell if
present; record each new cell once in `precompile/<sha>/benchmark/runs/`.
A 300-second emergency timeout cannot become a policy input or a repeat.

Measure whole-process user instructions as the primary complete-work counter;
report user cycles/conflict, branch misses, conflicts, verdict and secondary
wall time. Require one active PMU, at least 99.9% scheduling coverage, and
byte-identical solver stdout in each pair. A conflict-budget `Unknown` is a
prefix-cost observation, never a solved or independently verified verdict.

Advance only if geometric-mean instructions and cycles/conflict ratios are
both at most **0.95**, neither individual ratio exceeds **1.03**, and all
identity/correctness gates pass. Otherwise record the finding and stop this
candidate without tuning or repeated cells. Four cells are a rejection screen,
not a broad performance claim or a substitute for a multi-seed heuristic
study. A positive screen still requires all repository correctness gates and
fresh SMT differential parity before production landing.

## Result: neutral, below the registered bar

The baseline was the clean committed integration **`02afce4`**, binary SHA-256
`bfefa18cd55f68c33f2f4cf0d32c343bd6daf4524c29961e45527884b1c4b563`.
The candidate **`19f2d21`** descends directly from it, binary SHA-256
`314d2565021cf1fd4f63cc46f13b399eaac3f421a61937d7fcc00c0dab8fe946`.
Both used Rust 1.96.0 / LLVM 22.1.2 and the same lockfile/profile. All four
registered cells ran once. Both pairs returned budget `Unknown` at 40,000
conflicts, with byte-identical complete solver stdout.

| input | scalar instructions | fused instructions | T/null instructions | scalar cycles/conflict | fused cycles/conflict | T/null cycles |
|---|---:|---:|---:|---:|---:|---:|
| circuit | 12,073,482,219 | 12,060,827,589 | 0.998952 | 129,999.99 | 127,890.78 | 0.983775 |
| j3037 | 29,619,237,310 | 29,580,770,574 | 0.998701 | 463,120.58 | 448,993.96 | 0.969497 |
| geometric mean | | | **0.998827** | | | **0.976610** |

The instruction difference is only **0.12%**; the measured cycle difference
is **2.34%**. Both are inside the repository's neutrality band and fail the
registered 5% advancement threshold. This is not a throughput win. Source-level
repeated accesses did not yield substantial removable executed work in this
implementation; the screen does not establish which compiler optimization or
microarchitectural effect accounts for that. Do not retry this same header
fusion or tune its inline choices based on these cells.

All four records use one active `cpu_atom` PMU with 100% event scheduling
coverage. Circuit's scalar wall time was 9.19 s versus fused 1.22 s; j3037
was 4.12 s versus 3.97 s. Those secondary wall figures are not the effect
estimate: hardware instruction/cycle counts above cover the invocation's
user-mode execution. The anomalous wall cell is retained, not rerun.

Canonical record IDs (scalar / fused): circuit **a7a1c5fa679a8802 /
64e42bfc6b45aa7f**, j3037 **6514a0f4984c4d5c / 755967e4dc22240f**. Schema,
record identities and canonical paths were validated. Raw files, runner,
completion records, summary, source patch/bundle, build metadata and test
logs are under the corresponding `precompile/<sha>/benchmark/` entries.

## Correctness coverage and disposition

- All **756 SAT library tests** passed with all features. The raw-header
  oracle checks all 256 flag-byte values × 256 usage values × six glue
  boundaries (393,216 combinations), including deleted/original/learned
  clauses, raw tier encodings, saturation and activity bits.
- Relocated and tombstoned database IDs agree with the scalar sequence;
  database statistics remain unchanged.
- **32 ten-variable truth tables**, each with proof recording off and on,
  compare exact clause literal order and metadata, trail, watches, stats,
  ticks, reduction recency/histograms and LRAT transcripts. SAT models and
  UNSAT LRAT proofs are checked independently. These checks also passed in
  separate Kissat-reduction and null-reduction processes, and with ordinary
  features.
- The final test extension enables the clause-traffic observer and compares
  its complete reports between scalar and fused solves; that focused check
  passed. All-target SAT clippy, formatting and release builds passed.
- The candidate failed the cost gate, so its code is archived and **not
  landed**. No full workspace/parity qualification or broad performance claim
  is made for the rejected candidate. The independently verified arena
  initialization repair remains on main.

The temporary checkout and branch are removed after recording this verdict.
The source bundle includes the integration baseline as well as the candidate;
it remains recoverable after main's concurrent history changes. Current main
`cf9c4d1` has identical Rust and Cargo source to baseline `02afce4`; only docs
and commit history differ. The measured SHA/binary identities are unchanged.
