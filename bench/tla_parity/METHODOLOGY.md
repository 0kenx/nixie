# TLA+ front-end parity — methodology

## What this suite is

`nixie-tla-syntax` replaces SANY, the TLA+ parser Apalache shells out to. This
suite checks it against SANY itself, the same relationship
[`bench/z3_parity`](../z3_parity/METHODOLOGY.md) has with Z3.

**SANY is an oracle, never a dependency.** It is consulted to find out what the
right answer is; nothing Nixie ships links it, and the product has no JVM.
`deny.toml` still bans FFI. Running this suite needs `java` and
`tla2tools.jar`; not running it changes nothing about the build.

## The two comparisons

### 1. Syntax — a *one-sided* gate

Every file SANY parses must parse here. That direction is the gate and must
stay at zero.

The other direction is **not** a failure. The long-term target is a superset of
TLA+ as Apalache accepts it, so parsing something SANY rejects is allowed
provided the extra parse is unambiguous. Those files are listed each run for
review, and each one should have a reason:

| File | Why |
|---|---|
| `test49b.tla`, `test49c.tla` | `\mod` as a definable infix operator. SANY rejects it. Accepted here with its **own identity** — deliberately not aliased to `%`, since folding them together would make `u \mod v == u` silently redefine `%`. |

### 2. Levels — only what was actually established

For files SANY fully resolves, every definition's constant/state/action/temporal
level must match.

Only definitions whose level `nixie-tla-syntax` *established* are compared.
A level that depends on an unresolved `EXTENDS`, or on an operator the max rule
cannot handle, is marked untrusted and skipped — comparing a guess would
measure the missing module resolution rather than the level walk. The run
prints how many were skipped; that number going up is a regression in coverage
even when mismatches stay at zero.

## Known oracle defects

SANY is the reference, not scripture. One entry so far, listed in
`tlaparity.rs` and excluded by name:

- **`x * x` loses its level.** With `VARIABLE x`, SANY reports `x * x` as
  *constant*. Every neighbouring operator is right — `x + x`, `x - x`,
  `x \div x`, `x = x`, `x .. x` and a user-declared `F(x, x)` all give *state*.
  Only `*` is affected. `x * x` plainly depends on the state, so nixie's answer
  is the correct one.

Adding to that list is a claim that the reference implementation is wrong;
every entry needs a reproducer of the kind above.

## Running it

```bash
bench/tla_parity/run_parity.sh                  # default sibling corpora
bench/tla_parity/run_parity.sh /path/to/specs   # or your own
TLA2TOOLS_JAR=/path/to/tla2tools.jar bench/tla_parity/run_parity.sh
```

Corpora are the read-only sibling checkouts from `AGENTS.md`:

```
../temp/tlaplus-examples    github.com/tlaplus/Examples
../temp/apalache            github.com/apalache-mc/apalache
../temp/communitymodules    github.com/tlaplus/CommunityModules  (raises level coverage)
```

## Parallelism is not free here

Two isolation requirements, both found by this suite producing wrong answers:

- **Private `java.io.tmpdir` per invocation.** SANY extracts the standard
  modules into the JVM temp directory; parallel runs sharing `/tmp` corrupt
  each other and report spurious parse failures.
- **Private output file per invocation.** SANY's per-file output is many
  lines; parallel processes writing one pipe interleave them, pairing a
  `#FILE` header with another process's definitions. That manufactured ~120
  phantom level mismatches on the first run of this suite.

Validate the oracle before believing it. The `*` defect above and both
isolation bugs were all found by checking SANY against hand-written modules
with levels that are obvious by inspection.

## Running with `EXTENDS` resolved

Set `TLA_LIBRARY` to a `:`-separated list of directories to search for
imported modules; `run_parity.sh` passes it to both sides. Without it most
levels depend on unresolved imports, are marked untrusted, and never reach the
comparison — the suite passes while testing much less than it appears to. The
"definitions skipped (untrusted)" line is the number to watch.

## Standing result

Recorded 2026-09-12, SANY from tlaplus 1.7.4, OpenJDK 11, 907 files, with
`TLA_LIBRARY=../temp/communitymodules/modules`:

```
=== syntax parity ===
  both accept                     : 903
  SANY accepts, nixie rejects     : 0
  nixie accepts, SANY rejects     : 2     (the \mod extension above)

=== level parity ===
  files SANY could fully resolve  : 684
  definitions compared            : 5067
  definitions skipped (untrusted) : 574
  known SANY defects excluded     : 1
  level mismatches                : 0
```

Previous rounds, for the trend: 4 541 compared / 1 106 skipped before `EXTENDS`
resolution and per-parameter level functions existed.
