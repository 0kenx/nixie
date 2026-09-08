# Real QF_FP corpus ingestion: parse-complete, beyond both solvers

**Date:** 2026-09-09 · **Status:** recorded (completeness characterization —
no code change warranted).

## What ran

The official SMT-LIB benchmark repository's QF_FP content
(`SMT-LIB/benchmark-submission`, `non-incremental/QF_FP/20260424-AutoSMTGen`;
the only QF_FP submission currently published there — 130 files, 2.4 MB):

```bash
curl -s "https://api.github.com/repos/SMT-LIB/benchmark-submission/contents/non-incremental/QF_FP/20260424-AutoSMTGen" \
  | jq -r '.[].download_url' | xargs -P8 -I{} curl -s -o "qf_fp_corpus/$(basename {})" "{}"
```

Generator-stamped: 100 `sat` / 30 `unsat`; ~16 KB each; ~30k `fp.mul` +
~14k `fp.add` atoms over 9–10 free `(_ FloatingPoint 11 53)` variables
with `fp.leq`/`fp.geq` chain constraints ("small solution spaces to make
them challenging for SMT solvers", targeted at Z3/CVC5/Bitwuzla).

## Results

| solver | outcome |
|---|---|
| **nixie** (`fab65f8`) | **130/130 parse and load cleanly** — the full syntax (`(_ FloatingPoint 11 53)` declarations, every `fp.*` operator, exact-width literals) — then an **instant honest `unknown`** (~7 ms): no operand is pinned to a literal, so the fold pass emits nothing and the FP honesty gate correctly declines rather than letting the free atoms fabricate a verdict. |
| **z3 4.16.0** | **0/130 at 30 s; 0/2 at 300 s** (timeout) — the corpus is hard for the reference solver too. |

Zero wrong answers, zero crashes.  The two solvers fail *differently but
honestly*: nixie declines instantly (no symbolic FP theory is wired into
the CDCL(T) core), z3 grinds its bit-blasting FP engine to timeout.

## What this validates, and what it scopes

* **The parse surface is complete** for this corpus — the format-alias fix
  (`254ff45`) and the parser hardening (`66166ed`) hold on real benchmark
  files, not just probes.
* The constant-semantics stack (marks, folds, conversions) is irrelevant
  here by construction: every variable is free, nothing pins.  That is the
  corpus's design, not a regression.
* **Deciding these needs a symbolic FP theory in the CDCL(T) loop** —
  bit-blasting (z3 `fpa` / Bitwuzla's route) or interval/base-`k` search —
  a dedicated solver project, not an extension of the fold layer.  Scoped
  as the long-term FP rung; the `fpboundary` family keeps guarding the
  ground nixie *can* decide, exactly.

## Decision

The corpus is not checked in (no test can consume it — both solvers
timeout); the download recipe above is the record.  Revisit when a
symbolic FP theory lands.
