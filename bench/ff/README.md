# `bench/ff` — QF_FF corpus

Synthesized R1CS-shaped goals (the circuit form the theory targets):
planted-witness systems (ground truth `sat`) and mutated systems (one
constraint corrupted — satisfiable in general since mutation does not
force unsat; used for crash/honesty probing, never scored without an
oracle). Generated deterministically; see `docs/FF_THEORY_DESIGN.md`
§10.5 for the role corpora play in the verification ladder.

Two families:

- `sparse_*` — each linear form mentions ≤ 3 variables, the shape real
  R1CS rows have (the realistic case);
- (plain) `planted_*`/`mutated_*` — every linear form is dense over all
  variables, an intentionally adversarial shape kept as the capacity
  marker: the GB cascade is the bottleneck and split-GB (Phase 7) is the
  designed fix.

Current status (see
`docs/studies/2026-09-14-ff-front-end-components-and-work-budgets.md` for
the measurement protocol): every `sparse`/`planted` goal up to 64×96
solves at BN254 and Goldilocks; the dense 12×20 and the sparse ≥16×24
BN254 goals answer an honest `unknown` in seconds (budget-proportional
refusal). The exhaustive/planted fuzzers in
`nixie-theories/tests/ff_{oracle,planted_fuzz}.rs` are the soundness
canaries; these files are the *performance* substrate.
