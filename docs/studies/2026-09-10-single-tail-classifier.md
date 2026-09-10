# Search the false tail before classifying its replacement

## Registration

The [precise branch audit](2026-09-10-propagation-branch-attribution.md)
places 25.37% of whole-process branch-miss sample IPs at the contiguous
engine's two-stage tail classifier. Header null/deleted guards receive no
samples. The next implementation targets that classifier, preserving the
ordinary signed-byte truth representation and the archived complete engine
with contiguous binary spans. This is a changed combined implementation,
not retiming an unchanged rejected candidate.

Scan tail literals in order until the first value >=0, carrying its index,
literal and value out of the loop. Then classify that one result: a true
literal parks the existing watch and updates its blocker; an undefined
literal moves the watch. If all tail literals are false, use the already
read other-watch value for unit/conflict. Preserve exact clauses, eager pair
normalization, assignments, reasons, watch order, conflict tails, ticks,
budgets and observers. Local Kissat proplit.h is the nonfalse-search reference;
retain Nixie's true-literal parking, which differs from Kissat's moving rule.

This removes the positive/undefined classifier from false-prefix iterations.
It does not remove the selected-result distinction, length bounds, literal
value loads or any propagation obligation. Short tails bound saved work.
Price any new result dispatch, register state or reload instead of treating
the previous 25.37% event share as removable wall. No sentinel, SIMD, batching,
search policy, new adjacency tuning or additional unsafe block is added.

Before cost, compare the complete engine with the scalar exact-state oracle,
all truth patterns on bounded tails, selected-literal positions, prefix/suffix
watch phases, all-false unit/conflict, true parking, undefined moves and
unvisited tails. Reuse independent original-model/LRAT checks and native
Rayon owner movement. Run default/all-feature SAT nextest, SAT doctests,
strict SAT Clippy, workspace formatting and six focused strict-provenance
Miri span/queue tests. Full workspace build/tests/doctests/Clippy/fmt/docs
and installed Z3 4.16.0 parity remain mandatory before production promotion.

Portable release/perf assembly must show one sign test per false-prefix
iteration, no reread of the selected literal's truth, and classification
outside the scan backedge. Record text/local stack sizes against the previous
2,769/184 bytes. Permit one source-directed preflight repair; stop without
cost if those sizes increase or the intended loop does not materialize.
No measured repair or alternative classifier encoding after the result.

At most THREE new performance invocations beyond the closed branch audit:
candidate j3037 whole-solve cost; one candidate j3037 LBR cycle profile after
an output-identical completed cost, regardless of win/fail; and candidate
crn only if j3037 instructions and usable wall are both <=0.95 qualified
production and peak RSS <=1.10. Confirm crn instructions/wall <=1.03 and
two-input wall geomean <=0.95. These are rejection/advancement screens,
not a suite-wide or multi-seed performance claim.

Reuse fd01d0b j3037 record 0ec1f4bfcfe8f5f9 and crn 0840cab28aa276cb;
the previous contiguous cost fe075d2cf545b689 is additional implementation
context. Reuse requested-mode Kissat 4.0.4 record 45a3c8f2e3057841 as context.
No new baseline/reference, repeated cell or profile-as-cost substitution.
Use CPU15 Atom, seed0, MAXC=10000000, PRINT_MODEL=1, NIXIE_SWEEP=0,
NIXIE_DEFINITIONS=0, cleared unrelated study overrides, identical Rust
1.96.0 / LLVM22.1.2 and lock hash 3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439.
Portable profiles, no native/PGO/RUSTFLAGS overrides. Instructions are primary,
wall/cycles secondary, never policy inputs. Warm executable/input; anonymous
tmpfs output, GNU time1.10, cap300s, no owned build during cost. Require exact
stdout, >=99.9% PMU coverage, no major faults, <=5% off CPU and unchanged
constrained sleeper runtime. Shared cache/load/frequency and older controls
remain limits. LBR uses period10472903, 128 pages, grouped user Atom cycles/
instructions, CPU/read/running-time records, >=1000 samples, no loss/throttle
and <=0.1% unresolved self weight.

Store each start/completion and canonical result once with source/binary/input
identities. Unchecked UNSAT stays unknown/unverified. Land productive code
only after all promotion gates; otherwise archive source, profile and diagnosis
on main. Clean the owned temporary checkout, branch and disposable artifacts;
retain binary/source/result caches.
