# Fail-closed reasons in learned-clause minimization

The throughput source audit found a separate correctness defect: the plain
and LRAT minimizers treated an unavailable reason as an empty dependency
list, permitting literal removal without a justification. This repair makes
unavailable or malformed reasons fail the optional removal attempt. It is
not a throughput improvement or evidence that the Kissat cost gap is closed.

The reproductions inject invalid internal reason state. No well-formed CNF
or SMT input producing that state has been identified by this study. A
countermodel test nevertheless establishes the local semantic defect: after
removing c's reason from `a => b => c`, the assignment a=b=u=true, c=false
satisfies the surviving premises and `(!u | !a | !c)`, but falsifies the
unjustifiably minimized `(!u | !a)`.

## Repair and independent layers examined

1. **Reason storage.** `ClauseDatabase::get` can return no clause, a deleted
   clause, or a compacted tombstone. Those states must not stand in for an
   empty reason. The shared minimization lookup now requires a live clause
   containing the exact signed head. It rejects missing, retired, compacted
   and headless reasons. Binary heads remain valid in either stored position.
2. **Plain minimization.** Classification now verifies the requested literal
   is true before level-0 or cached-flag exits. This prevents an unassigned
   variable's default level 0, or a kept variable's opposite polarity, from
   masquerading as a proof. The iterative walker skips only the exact head;
   its unavailable-clause branch poisons the attempt rather than completing
   it successfully. A failed descendant propagates failure to its ancestors.
3. **LRAT minimization.** The separate depth-bounded recursive path uses the
   same live-head requirement and truth guard. It no longer snapshots a
   missing reason into an empty vector. Clause minimization retains an
   unjustified literal and contributes no proof subchain for its removal.
4. **Block shrinking.** Its independent reason snapshot now uses the shared
   lookup. Each tail must be false and assigned earlier than the popped
   head. The latter check fixes another fault-injection defect: a circular
   reason could encounter an already-SHRINKABLE variable, reduce the open
   count without resolving that dependency, and drop it. The first repair
   alone did not fix this; the self-cycle regression failed after ordinary
   and LRAT minimization tests were already passing. Failed blocks retain
   their existing fallback order and use the repaired minimizer.
5. **Proof-chain consumption and flag lifetime.** Both callers of
   `calculate_minimize_chain_lrat` consume graphs established by minimization
   or shrinking before the graph or clause database can change. Kept and
   poisoned variables stop the chain; removable nodes now have justified
   reasons. Existing cleanup clears keep/removable/poison/shrinkable/added
   flags and unit marks before the next analysis. Tests inspect both the
   retained clause and the absence of an unjustified chain, and check flag
   cleanup. This is not a claim that arbitrary direct calls with corrupted
   proof state are supported.
6. **Assignment and retirement producers.** Ordinary BIG/watch propagation
   records clause reasons; live-reason checks protect clause reduction, and
   `retire_clause`/`remove_clause` clear matching assignment reasons. The
   inspected BV and FP callers restore their saved trail before forgetting
   learned clauses. Scope pop retracts its clause set and restores its saved
   trail. Chronological backtracking compacts survivors stably, preserving
   the antecedent-before-head order used by the shrink guard. This inspection
   found no input-level producer of the injected states; it is not an
   exhaustive proof of all solver state transitions.
7. **Reference semantics and result boundary.** CaDiCaL's `minimize.cpp`
   requires a true head and an actual reason, and skips that head by signed
   value. `shrink.cpp` requires false antecedents; a valid implication graph
   depends on earlier assignments. Nixie's invariant checks independently
   check live reasons and graph acyclicity. Initial conflict analysis still
   requires a live, falsified conflict supplied by propagation; this change
   concerns optional strengthening of an already-derived learned clause.
   Failure to prove a removal keeps that clause literal, which is sound
   without inventing a new solver verdict.

No branching, watch selection, restart, deletion schedule, RNG, literal
ordering on valid reasons, or minimization depth policy is changed. The
plain and LRAT walkers retain their existing implementations and depth-100
guard. Additional validity checks can cost time; no performance gain is
claimed and no timing-driven policy is introduced.

## Verification

Eight focused tests cover nine invalid-reason shapes at both the root and a
descendant, both proof modes, block shrinking, proof/flag cleanup, and the
countermodel above. Valid implication chains spanning inline-stack and
depth-limit boundaries (lengths 1, 2, 31, 32, 33, 100, 101, 102 and 150)
compare both minimizers' result, flags and cleanup records. The original
correctly initialized six-test set failed five tests on the old source;
its valid-chain control passed. Initial test-fixture/compilation errors are
retained separately and are not counted as solver defects.

Qualification passed on the combined source based on `e9a343a`:

- Workspace all-features build.
- Workspace all-features nextest: **10,801 passed**, 12 existing skips.
- Workspace all-features doc tests: **111 passed**, 29 ignored.
- All-features/all-targets Clippy with warnings denied; workspace format
  check; all-features documentation with warnings denied by the repository's
  `rustdocflags` setting.
- Fresh `run_parity.sh` with installed **Z3 4.16.0**: **174 decisive
  agreements, zero disagreements**, and one inconclusive case out of 175.
  On `array_unique.smt2`, Nixie returned Unsat and Z3 returned Unknown;
  that cell is not counted as agreement. There were no timeouts or errors.

Builds used Rust 1.96.0, four Cargo jobs, the existing lockfile (SHA-256
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`),
offline dependencies, and no Rust optimization flag overrides. Nextest used
four test threads. The independent LRAT end-to-end checks, chronological
minimizer regression, and SAT differential tests are included in the full
pass. No new performance benchmark cells or Kissat runs were consumed.

The repair commit's `precompile` directory retains the release CLI and
`stats_solve` binaries. Its `benchmark/minimization-reason-guards/` directory
retains the full qualification logs, earlier fault-injection failures,
runner, source and binary identities, and the complete parity JSON. The
parity script's suggestion to commit that JSON is stale: the repository
explicitly ignores `bench/z3_parity/results.*.json`, so this study preserves
it in the result cache instead. The private build checkout and temporary
branch are removed after landing.

The first all-features build passed on `bfadd12`. Its subsequent nextest
compilation was deliberately stopped when the independent quantifier repair
`e9a343a` reached main. The private checkout was fast-forwarded to that
commit, preserving this repair, and qualification restarted on the combined
source. The interrupted compilation is not a completed test-suite result.
