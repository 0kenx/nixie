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
recorded; do not rerun controls. Collect whole-process instructions/cycles for
both transformation and solving so preprocessing cost cannot disappear.
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
