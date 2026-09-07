# Exact small-relation factorization

Registered before implementation and new measurements. This follows the
700 eight-variable tables audited in
[the region traffic study](2026-09-07-structured-region-traffic.md).

## First implementation and correctness gate

Provide an explicit, offline Rust CNF transformer. Ordinary solver paths and
defaults do not invoke it. Group clauses with eight distinct variables by
their complete support; require exactly 240 distinct forbidden assignments.
Choose the first lexicographic four-variable projection that is bijective on
the 16 allowed rows. Emit four output implications per row: 64 clauses of
width five. Preserve every variable and every other clause, including units,
empty clauses and duplicate clauses outside replaced groups.

Validate all 256 assignments before accepting a replacement. Derive each new
clause by seven binary resolutions from eight identified original clauses,
emitting explicit two-parent LRAT hints through widths seven and six. Delete
original group clauses and intermediate proof clauses only after additions.
Export output-clause proof IDs so a later solver proof can be remapped; the
prefix itself does not prove UNSAT. Bound extraction and proof growth; limit
exhaustion preserves the original formula, while malformed input or a failed
certificate is an error. No mutable solver state or incremental scopes are
involved. Resolution semantics follow CaDiCaL's elimination/proof code and
Nixie's LRAT tracer/checker.

Tests must exercise missing rows, nonfunctional relations, signs and variable
permutations, duplicate clauses/literals, tautologies, overlapping groups,
empty/unit clauses, limits, exact local truth tables and independent LRAT
checking. A complete UNSAT certificate must compose a solver proof through
the exported ID map and verify against the original formula. Run the full
repository verification gates and Z3 differential suite.

## Minimal feasibility measurement

The user requested fewer solver runs. Allow **one new circuit solve**, seed 1,
CaDiCaL preset, 10 million conflicts, CPU 2, portable release build, with a
300-second emergency timeout. Transform once, independently check the full
prefix and original-CNF model, and retain content hashes and artifacts in the
result store. Reuse original circuit results and Kissat references already
recorded; do not rerun controls. Collect whole-process user-space
instructions/cycles for both transformation and solving so preprocessing work
cannot disappear. Kernel work and independent audit checks are excluded.
Primary work is their summed instructions; cycles/conflict is descriptive.
No parameter tuning or additional seeds follow the result in this step.

This is an operational feasibility screen, not an improvement claim. The
encoding changes propagation/search; one seed cannot separate its merit from
trajectory reshuffling. There is no established equal-size, sound semantic
null for this exact factorization. A clause shuffle is not one, and scrambling
function outputs would be unsound. Therefore the result cannot qualify a
default flip or a causal speedup claim. A later comparison must resolve that
control question and register its seed panel before claiming general gains.

The implementation gate is exact equivalence, a checked proof prefix, a model
valid on the original input, and successful fallback tests. The size audit
must reproduce 700 groups, 44,800 non-unit clauses and 224,000 non-unit literal
slots. A mismatch, invalid proof/model, or new unresolved correctness failure
blocks use. Failure to solve within the registered cap rejects operational
feasibility on this input; a successful solve only licenses further study.

## Using the explicit transformer

```sh
cargo build --release -p nixie-sat --example relation_factor --example stats_solve
target/release/examples/relation_factor input.cnf factored.cnf prefix.lrat map.json
target/release/examples/stats_solve factored.cnf
```

All three output paths must be new. The transformer prints a JSON size/proof
summary and produces no SAT verdict. Its strict DIMACS reader rejects missing
or repeated headers, invalid literals/tokens, unterminated clauses, mismatched
clause counts and `%` trailers. Library callers use
`nixie_sat::relation_factor::factor_relations`; a limit error leaves their
borrowed input untouched, and the example writes that original formula with
an empty proof prefix and an explicit `fallback: true` summary.

`map.json` identifies each output clause in the original formula's proof ID
space. A downstream solver sees its own originals as IDs `1..M`; replace those
references with the exported IDs, and map each derived ID `d > M` to
`last_proof_id + d - M`. Deletion IDs need the same translation (their leading
line label is cosmetic). Check the composed proof against the **original**
CNF. A regression test exercises the complete UNSAT composition. For SAT,
there is no reconstruction: validate the returned model on the original CNF.

The reusable measurement/checker is
`bench/suite/scripts/relation_factor_probe.py`. Its checker independently
replays set resolution, checks the surviving clause-ID map and every dropped
original clause, then exhaustively checks the reverse implication for each
replaced relation. Completed subprocess results are retained immediately;
an interrupted recording never licenses rerunning an existing solver cell.

## Implementation verification

The implementation passes all-feature build, strict all-target clippy, format
and strict documentation checks; **10,660 nextest tests** (12 skipped),
**111 doctests** (29 ignored), the two explicit parser example tests, and
three Python certificate-auditor rejection tests. The eight new library tests
include complete LRAT composition, signed/permuted nonlinear relations,
overlapping groups, incomplete/nonfunctional tables, duplicate/tautological
clauses, empty/unit clauses, exact limit boundaries and output errors.

Fresh Z3 **4.16.0** parity reports **169 agreements, zero disagreements and one
inconclusive case** (`array_unique.smt2`: Nixie UNSAT, Z3 UNKNOWN). The available
Z3 release is recorded explicitly; this is not a comparison to the historical
4.15.4 snapshot. Ordinary solver paths do not call the new transformer.
