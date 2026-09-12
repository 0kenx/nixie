# TLA+ semantic parity — methodology

## Why this exists

Every other check on this front end is **structural**:

| Suite | Checks |
|---|---|
| `bench/tla_parity` (syntax) | does SANY parse what we parse? |
| `bench/tla_parity` (levels) | does SANY assign the level we assign? |
| `nixie-tla`'s coverage tool | does a definition lower at all? |

None of those can tell a *correct* lowering from a well-formed *wrong* one.
The `INSTANCE` visibility bug is the demonstration: lowering resolved an
instantiated module's definition directly, using the **unsubstituted** body and
reading the wrong module's variables. It produced a perfectly valid kernel
term, passed every structural check, and was found only by a test that asked
what the term actually *meant*.

This suite asks that question at scale.

## How it works

1. For every module with **no declared constants or variables** — so TLC needs
   no configuration to run it — lower each nullary definition and evaluate it
   to a value.
2. Emit a probe module that `EXTENDS` the **original** module and `PrintT`s
   those same definitions.
3. Run TLC and compare the two sets of values.

Step 2 is the load-bearing detail. The probe extends the *source* module, so
TLC evaluates the definition **as written** — not a kernel term printed back
out. Comparing against a re-printed term would test the evaluator and the
printer against each other and say nothing about lowering.

TLC is an oracle, never a dependency: the suite needs `java` and
`tla2tools.jar`; nothing Nixie ships does.

## Comparison is structural, not textual

TLA+ values have several printed forms:

- sets are unordered, and TLC prints them in insertion order;
- TLC prints a function on `1..n` as a sequence (`<<1>>`), and one on strings
  as a record (`[a |-> 1]`) — both are the same *value* as `(1 :> 1)` and
  `("a" :> 1)`;
- record fields keep source order;
- a contiguous integer set prints as `1..3`.

Nine "mismatches" in the first run were every one of those, and none was a
disagreement about a value. `compare.py` therefore parses both sides into a
canonical form — tuples and records both become functions — and compares
values.

## What is deliberately not compared

- **`CHOOSE`.** TLA+ says only that it picks *some* satisfying element. Any
  answer could differ from TLC's without either being wrong, so evaluating it
  would turn the differential into noise.
- **Operators TLC implements in Java** (`JavaTime`, `TLCGet`, `TLCSet`,
  `RandomElement`, `Permutations`). TLC overrides the TLA+ definition, so a
  comparison measures TLC's runtime rather than this evaluator. `JavaTime` was
  the single "mismatch" of the first clean run: the examples' `TLC.tla` defines
  it as `123`, and the tool substitutes the clock.
- **Anything the evaluator declines** — a free name, an unimplemented
  primitive such as `\o`, a set past the size cap. It reports the reason and
  evaluates nothing; an evaluator that guesses would make the differential
  compare two guesses.

## Running it

```bash
bench/tla_eval/run_eval_parity.sh
TLA2TOOLS_JAR=/path/to/tla2tools.jar bench/tla_eval/run_eval_parity.sh
```

## Parallelism, again

Two isolation requirements, both found by this suite silently producing almost
nothing:

- **A private working directory per TLC run.** TLC writes its metadata into the
  working directory; parallel runs sharing one clobber each other.
- **A bounded heap (`-Xmx`).** TLC reserves a very large heap by default, so
  parallel runs are OOM-killed and produce no output — which looks exactly like
  "TLC could not evaluate these".

That is now the third oracle harness in this project to have been wrong because
parallel processes shared something. **Check isolation before believing a low
hit rate.**

## Standing result

Recorded 2026-09-12, TLC 2.19 (tlaplus 1.7.4), OpenJDK 11, 907-file corpora:

```
probes TLC evaluated            : 28
definitions agreeing with TLC   : 93
SEMANTIC MISMATCHES             : 0
not printed by TLC              : 161
```

93 definitions is a small sample against 4 349 that lower, and the restriction
to constant- and variable-free modules is what makes it small. Widening it
means generating TLC configurations that assign the constants — the obvious
next step, and the one that would turn this from a spot check into a gate.
