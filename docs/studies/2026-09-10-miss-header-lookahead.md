# Miss-only clause-header lookahead

## Registration (before implementation and performance runs)

Goal: reduce Nixie's wall cost against mode-matched Kissat by overlapping
independent clause-header loads in the fixed-assignment long-watch scan.
This follows the [source audit](2026-09-09-miss-header-lookahead-audit.md) and
the [compact adjacency rejection](2026-09-10-compact-adjacency.md). Smaller
directories and cold growth paths did not remove the dependent memory work.

The candidate prepares at most one following entry, only on a live blocker
miss. It reads that entry's blocker and, if nontrue, its header. The actual
visit consumes this work without repeating those reads. Literal reads,
normalization, watch movement, reasons, tick charges, and assignment order
stay at their original positions. Discard preparation at every scanner
return and prefix-to-suffix transfer. No policy or search-order change is
intended; any trajectory difference fails the experiment.

The arena owns pending metadata inside an exclusive scan borrow. No cached
length or pointer token is exposed to callers. Growth, shrink, deletion and
relocation are inaccessible during that borrow; mutable literal slices
borrow the scan itself, preventing overlap even for duplicate references.
The only new unsafe operation may form a literal slice from metadata read
by this same scan. Solver instances retain ordinary ownership and Rayon
compatibility; no global state, custom Send/Sync assertion or shared raw
pointer is permitted.

Before performance: default and all-feature SAT tests, exact scalar-oracle
state comparisons (ghosts, duplicate refs, stable compaction, units,
conflicts, growth between yields and backtracking), focused Miri for the
arena API, strict SAT Clippy, format, and generated-code inspection. The
assembly must issue the next header read before current-clause work and
consume it without a second read. Record code size, stack and dispatch
cost. A failed preflight is a result; do not time known-broken code.

Use seed 0, the existing CaDiCaL preset, disabled sweep/definitions, CPU 15,
the same warmed-input whole-process user cycles/instructions protocol as
the compact adjacency study, and the existing Kissat 4.0.4 reference cells.
First run one qualified control and one candidate on j3037. The control
binary is fd01d0b (the qualified binary-span repair); subsequent main edits
are arithmetic/quantifier code outside this DIMACS execution path. Record
all raw cells once with benchstore. Require identical complete solver
stdout, at least 99.9% PMU coverage and at most 5% off-CPU time for a usable
wall comparison. Failed measurement quality is inconclusive, not a license
to repeat the cell. No own build may overlap performance measurement.

Advance only at at least 10% lower wall with no instruction regression,
or at least 5% fewer instructions without a usable wall regression. A
passing screen permits one paired si2 confirmation (check the SAT model)
before full workspace qualification and landing. A negative/neutral screen
gets one LBR profile to explain its cost. One code-directed repair is
permitted only if that profile and assembly identify removable overhead;
otherwise stop and archive the candidate. No distance/width sweep, seed
search, rerun or cross-profile counter ratio. These are bounded engineering
screens, not population estimates or a new Kissat-suite geomean.
