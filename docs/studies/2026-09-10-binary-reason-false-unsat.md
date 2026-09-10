# Kissat-style `Reason::Binary` — false UNSAT, reverted

Tried storing the other literal of a binary implication as
`Reason::Binary(Lit)` instead of `Reason::Propagation(ClauseId)`, matching
Kissat `assigned.binary` / `reason = not_lit`. Analysis marked that literal
without loading the arena clause. `Reason` stayed 8 bytes.

j3037 dropped from 347882 conflicts to 2309 and 39.72 s to 0.26 s, both
UNSAT. SAT instances became UNSAT: si2-b03m (11433 conflicts) and
circuit_48in64out (2835 conflicts). Independent prior runs and Kissat treat
both as SAT. The analysis path dropped antecedents and learned over-strong
clauses.

Reverted before any commit of solver source. Do not retry a binary-reason
literal without an exact-state oracle against `Propagation(cid)` on the
same binary edges, including polarity of the stored trigger and
minimization. Arena slots remain the binary reason until that contract is
proved.

## Retry after stale-watch XOR fix (`d7b5dc34`)

Retried Theory-style 1-UIP (`mark_antecedent(other)` for `Reason::Binary(!lit)`
on BIG assigns) with the stale-watcher guard in place. SAT lib 827 tests
passed. si2-b03m still returned **Unsat at 0 conflicts** (1.00M props);
circuit_48in64out Unsat at 7882 conflicts. Independent runs treat both as
SAT. The false UNSAT is not the XOR-corrupt stale watcher. Do not enable
Binary trail reasons until a same-trail oracle vs `Propagation(cid)`
explains the 0-conflict root unit.
