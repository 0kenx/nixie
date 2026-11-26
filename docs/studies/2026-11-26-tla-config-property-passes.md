# `PROPERTY` in a configuration is checked – a `check` is passes (issues #29, #31)

## The gap

`TlcConfig::properties` was parsed and never consulted. A configuration with
`INVARIANT Inv` and `PROPERTY Liveness` ran the invariant, printed `The
outcome is: NoError`, exited 0 – with the liveness property unexamined. In
Apalache's own integration suite that is the `Config1.cfg` cell, and Nixie
"agreed" with the oracle on it by coincidence: both said `NoError`, one of
them without asking the question. Had `AwesomeLiveness` been false the
oracle would have said `Error` and Nixie `NoError` – a wrong verdict class,
from a silent drop, which is the shape this codebase refuses everywhere else.

## What a run is now

A `check` is a list of **passes** over one configuration:

* the invariants and the deadlock question, over the ordinary unrolling –
  when there is an invariant to check or a deadlock question to ask;
* one pass per temporal property, over the lasso encoding of #29.

A property is named by `--temporal=P` or by `PROPERTY`/`PROPERTIES` in the
configuration. The command line overrides the file, with a warning, as
`--inv` does over `INVARIANT`. The outcome is the worst of the passes: a
counterexample or a deadlock is `Error` (12), an undecided pass with nothing
found is `Unknown` (255), otherwise `NoError` (0). Counterexamples are
numbered and written across the whole run (`violation1`, `violation2`, …),
`--max-error` counts across it, and when it is reached the remaining passes
are not run – said out loud, never reported as if they had held.

A single-pass run prints exactly what it printed before. A multi-pass run
prints a heading per pass and one outcome line at the end:

```text
checking invariant(s) Inv
  no counterexample of 4 step(s) or fewer
checking temporal property `Never`
  counterexample 1: a lasso of 3 step(s) whose last state returns to state 2, violating `Never`
    independently replayed: yes
The outcome is: Error
EXITCODE: ERROR (12)
```

Three contracts moved with it:

* `--temporal` with `--inv` is no longer "cannot be combined" (255). The
  claim that Apalache refuses the mix was true of neither tool once the
  configuration file was read; they are two passes now. `--inv=<a temporal
  formula>` is still 255, refused before any pass runs.
* a configuration with a `PROPERTY` and no invariant is a legal request
  (with the deadlock question, two passes; with `CHECK_DEADLOCK FALSE`,
  one), where "nothing to check" used to be the answer.
* `simulate` does not check properties and says which ones it did not
  check, rather than dropping them.

Fairness interacts as in the #46 study: invariants are checked with the
clause announced and unassumed; a property under it is declined (75).

## Cells (Apalache's own suite, `--config` cells, pinned 0.63.0 oracle)

| cell | Apalache | Nixie | class |
|---|---|---|---|
| `Config1.cfg` (`INIT`/`NEXT`, `INVARIANT Inv1`, `PROPERTY AwesomeLiveness`) | NoError | NoError | **Agree-Ok** – two passes, the property's lasso search included |
| `Config2.cfg` (`SPECIFICATION Spec2`) | NoError | NoError | Agree-Ok |
| `Config4.cfg`, `Config5.cfg` (`SPECIFICATION` with fairness) | NoError | NoError | Agree-Ok |
| `ConfigReplacements2.cfg`, `Test2750.cfg` | NoError | NoError | Agree-Ok |
| `Bug2750.cfg` | 255 | 255 | Agree-Refused |
| `Config3.cfg` (`PROPERTY NoLiveness`, undefined) | 255 | 75 | Declined |
| `ConfigParams.cfg` | NoError | timeout (300 s) | Inconclusive |
| `Config1.cfg` + `--init=Init2 --next=Next2` | exit 1 (oracle drift; the corpus expects 12) | Error | Inconclusive by the harness, agreeing with the expectation |
| 9 more | exit 1 (oracle drift) / `--config-file` (not an option) | – | Inconclusive |

Before this commit the first row was Agree-Ok for the wrong reason and the
two `HandshakeWithTypes` cells were not compared at all (below).

## Two defects in the harness, fixed

`run_parity.sh` carried one tab-separated field per option into `read`,
which hands the **last** variable the remainder; a cell with two or more
options (`--length=5 --config=…`, `--config=… --inv=Inv`) was read as a cell
whose spec was its second option and skipped ("SKIP …: no --init=Init2").
Every cell the standing result was ever computed on had exactly one option.
The options are one field now. And the comparator: `Unknown` (exit 255 with
"The outcome is: Unknown") was counted a `MISMATCH`; it is `Inconclusive`
by the methodology's own table. Both `TooShort` is an agreement; the same
non-verdict exit code on both sides is `Agree-Refused`.

## Tests

`tests/cli.rs`: a property checked beside the invariants (two passes, one
outcome line, the lasso written as `violation1`), `--max-error` stopping
before a later pass and saying so, two errors across two passes numbered 1
and 2, a property-only configuration with and without the deadlock question,
the `--temporal` override, `simulate`'s note, and the two contracts that
moved.

## Remaining

* A deadlock question beside a property is two encodings of the same
  specification (the ordinary unrolling and the lasso); a run pays for both.
* `ConfigParams.cfg` times out at 300 s: capacity, not shape.
* Fairness for liveness is issue #47.
