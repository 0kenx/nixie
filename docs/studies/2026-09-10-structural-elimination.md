# Structural gate elimination toward the Kissat wall gap

The user's paired 2.27x wall / 1.24x conflict geomeans imply approximately
1.83x wall per conflict. Prior local loop rewrites do not establish enough
remaining opportunity. This step targets fewer clauses, auxiliary variables
and propagation events through cheap definition recognition and bounded
gate-aware elimination. References are local Kissat `gates.c`,
`equivalences.c`, `ands.c`, `ifthenelse.c`, `definition.c` and `resolve.c`.

## Scope and prerequisites

Use the existing explicit `NIXIE_DEFINITIONS=1` mode. Recognize equivalence,
AND/OR and ITE clause patterns before the embedded semantic solver; preserve
the existing semantic fallback. Share occurrence preparation and index
storage. Admit denser neighborhoods only to the structural path, with an
explicit occurrence bound, work budget and the existing resolvent growth
bound. Do not expose a larger unrestricted all-pairs resolution search.

The source audit found that the ordinary round's stop condition consults
`elim_resolutions_total`, which is unchanged until the round returns.
Repair the budget against work consumed in the current round, enforce it
inside both resolution products, and re-arm unfinished candidates. A denied
attempt must not retire its pivot or install an incomplete resolvent set;
already justified units and strengthening remain valid. Tests must cover
zero/exact/exhausted boundaries and resumption independently of recognition.

Pattern recognition must use live original clauses and the eliminator's
current root assignment. Return actual antecedent IDs, handle both pivot
polarities, and prove that the pivot-erased gate clauses are inconsistent.
The existing three-product resolver then omits the antecedent-by-antecedent
product justified by that property. Check shrinking/deletion during
resolution, eager units, model extension, removal of learned clauses over
eliminated variables, scopes, assumptions, frozen variables and proofs.
Preserve the existing proof-mode refusal for definition extraction until
the corresponding provenance is implemented and checked.

## Evidence and measurement boundary

This is a new search-transforming implementation, not an exact-trajectory
loop optimization. A matched semantic null for definition enablement is
still unresolved in the existing definition/factorization studies. Neither
a shuffled invalid gate nor an ordinary clause shuffle supplies that null.
Correctness qualification and an explicit usable mode do not establish a
default-enablement or broad performance claim.

Before any solver performance call, complete recognition/resolution/model
tests and strict SAT checks, commit the candidate and cache its binary
identity. Register the specific cost cell and its controls separately once
the implemented work counters and static opportunity audit are available.
No performance run is authorized merely by this design note. A negative
cost result must retain a profile/diagnosis and account for recognition,
resolution, maintenance and subsequent search. Before a production source
landing, run all required workspace and correctness-only parity gates.

Initial source: `c452903`. No implementation or measurement result is
claimed by this registration.
