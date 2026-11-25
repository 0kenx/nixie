# TLA+ verdict parity vs Apalache – methodology

## What this measures

`nixie-tla`'s **verdicts** against the pinned Apalache oracle, on the
`check`/`simulate` cells of Apalache's own CLI integration suite. This is
the harness the tracking issue (#31) named as the measuring instrument for
"drop-in": same argv, same working directory, same exit code class, and –
for agreeing violations – equal counterexample length.

## The oracle

* Binary: apalache-mc **0.63.0**, from the nix store
  (`159k2slmq3qjwxmrawcxg6j4awj0yfq3-apalache-0.63.0`). The `apalache-mc`
  on PATH is 0.52.2 and predates the strict-JSON config – it is the wrong
  oracle and the runner does not use it. `APALACHE_BIN` overrides, for
  re-pinning only; a re-pin is a new store directory, not an edit.
* Source of the corpus: `cli-integration-tests.md` at
  `../temp/apalache/test/tla` (extracted into `corpus.json` by the
  extractor; regenerate only with the pinned version in hand, and record
  where it came from in the corpus header).
* Oracle results are stored once per cell under
  `precompile/apalache-0.63.0/benchmark/tla_parity/<cell-id>/` and never
  re-run. Where the mdx expectation and the pinned binary disagree, that is
  *oracle drift*: recorded as the binary's answer, with the mdx expectation
  kept in `corpus.json` for reference.

## Comparator (ported from `bench/z3_parity`)

| class | meaning |
|---|---|
| `Agree-Ok` | both `NoError` |
| `Agree-Violation` | both `Error` (exit 12); counterexample length must also be equal – both tools search lengths in increasing order, so each one's first counterexample is the shortest |
| `Agree-Deadlock` | both `Deadlock` |
| `MISMATCH` | same cell, different verdict class |
| `Inconclusive` | `Unknown`, timeout (124), or the oracle itself failed |
| `Declined` | Nixie 75/120/150 – could not evaluate the spec |

`Inconclusive` and `Declined` **never count as a match** and are reported
as separate counts. The run exits non-zero on any `MISMATCH` or on zero
compared cells.

## Running

```bash
MAX_CELLS=40 bash bench/tla_apalache_parity/run_parity.sh
```

`MAX_CELLS` takes a deterministic prefix of the corpus (sorted as the mdx
orders it). The oracle arm is cached after the first run, so later runs are
Nixie-only in cost. Both arms run under `taskset -c 0-7`.

## Standing result (2026-11-25, first 13 comparable cells)

| class | count |
|---|---|
| Agree-Ok | 3 |
| Agree-Violation | 0 |
| Agree-Deadlock | 0 |
| Declined | 7 |
| Inconclusive | 3 |
| **MISMATCH** | **0** |

The `Declined` cells in this prefix are the known gaps the tracking issue
already lists: the `Fix365_ExistsSubset*` family is
existential-over-symbolic-set (#20's frames); `Bug540`/`pr`/`Fix531`
decline in the encoder and `Bug20190118` in the type checker – each is a
denominator entry, not a divergence. Two of the three `Inconclusive` are
the *oracle* failing on its own cells (`y2k_instance` exits 127,
`Bug593` exits 1), which is oracle drift, not a Nixie mismatch; `ast`
is Nixie timing out at 300 s, honestly reported.

## Known oracle defects (to grow, each with a reproducer)

* `y2k_instance.tla` – the pinned 0.63.0 binary itself dies (exit 127) on
  this cell; the mdx expectation says OK. Oracle drift, not compared.
* Candidates to confirm and add: `Deadlock712` ("Apalache may miss a
  deadlock", their issue 712); `InfDomFun` (expected violation but
  `f[0] = 42` appears to hold).
