# Logic registry completion: all 89 SMT-LIB benchmark logics (2026-08-24)

## Trigger

The quantified-UF pin study's probe case `(set-logic UFNIA)` was rejected
at the command surface (`unknown logic 'UFNIA'`) while z3 answered `unsat`
— a *completeness* defect in the Priority-0 logic-contract layer: valid
SMT-LIB input refused before any engine moved.

## Ground truth

The smt-lib.org benchmark catalog (89 logics; the authoritative listing
of logics with shipped benchmarks, provided from the site's bench index).
Decoding semantics: cvc5's grammar decoder (`src/theory/logic_info.cpp`) —
leading `QF_` drops quantifiers; `A`=arrays, `UF`, `C`=cardinality,
`BV`, `FF`, `FP`, `DT`, `S`=strings; exactly one arithmetic suffix
(`IDL/RDL/IRDL/LIA/LRA/LIRA/NIA/NRA/NIRA`) sets linear/nonlinear and
integer/real/diff.  z3 is compositional (accepts `UFXYZ`) and is *not* an
arbiter for name validity; the catalog + cvc5 grammar are.

## Gap and fix

Registry held 57 entries; 43 catalog logics were missing (rejected at
`set-logic`): `UFNIA`/`UFNIRA`/`UFIDL` (the quantified UF+arith families),
the whole `DT`/`BVDT` composition stack (`UFDT*`, `UFBVDT*`, `AUFDT*`,
`AUFBVDT*`, `QF_UFDTNIA`, `QF_UFBVDT`), quantified `ABV`/`AUFBV`/
`AUFBVFP`/`UFBV*`, `FPLRA`/`BVFPLRA`/`ABVFPLRA` (FP+arith mixes),
`QF_LIRA`/`QF_BVFPLRA`/`QF_ABVFPLRA`/`QF_SNIA`/`QF_UFFP`/
`QF_UFFPDTNIRA`/`UFFPDTNIRA`/`AUFFPDTNIRA`/`UFBVFP*`/`UFBVLIA`/
`ANIA`/`ALIA`/`ABV`/`ABVFP`/`BVFP`/`ABVFPLRA`.

All 43 added, decoded mechanically from the cvc5 grammar.  Mixed
Int+Real shapes (`LIRA`/`NIRA`) follow the table's shipped convention
(`AUFLIRA`, `AUFNIRA`, `QF_UFDTLIRA`): `integer: false` — provenance is
deliberately unenforced in `validate` (mixed-comparison coercion), the
flag only routes the linear fallback solver.  No existing entry changed.

## Guards

- `logic_contract_acceptance::smt_lib_catalog_is_accepted_at_set_logic`:
  all 89 names through the *command surface* (a future gap breaks the
  suite, not a user's file).
- `logic_contract::tests::smt_lib_catalog_decodes_grammar_semantics`:
  grammar decode pinned for representative additions (UFNIA, UFIDL,
  mixed-integer convention, SNIA, the UFBVDTNIRA stack, FPLRA, ABV).

## Routing smoke (newly reachable engine combinations)

| logic | input shape | oxiz | z3 |
|---|---|---|---|
| UFNIA | quantified f, `(* (f z) (f z))`, congruence refutation | unsat | unsat |
| UFIDL | quantified diff + congruence | sat | sat |
| QF_SNIA | `str.len` vs `(* i i)`, NL int | unsat | unsat |
| QF_LIRA | mixed Int+Real linear | unsat | unsat |
| UFBV | `forall` over BitVec | unsat | unsat |
| UFDT | `forall` over datatype | unsat | unsat |
| FPLRA | quantified Real (FP+LRA header) | unsat | unsat |
| ABV | `forall` over BV-indexed array | **unknown** | unsat |

The `ABV` row is a known-incomplete-but-honest result: MBQI over
BitVec-indexed arrays does not enumerate the index domain.  Before this
change the file was rejected outright; `unknown` is strictly better and
is a recorded follow-up (quantified-array + BV-index instantiation), not
a regression.

## Verification

10 088 tests, clippy/fmt/doc; differential **0 wrong verdicts, solved 160
byte-identical to the pre-change run** (the registry only affects inputs
that were previously rejected); canaries unchanged (pete/cxs-bp `unsat`,
wisas `unsat`, sorted_list `sat`); Z3 parity 168/168.
