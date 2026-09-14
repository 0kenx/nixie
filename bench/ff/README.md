# `bench/ff` — QF_FF corpus

Synthesized R1CS-shaped goals (the circuit form the theory targets):
planted-witness systems (ground truth `sat`) and mutated systems (one
constraint corrupted — generally `unsat`, used for capacity probing,
never scored without an oracle). Generated deterministically by the
script embedded in the git history of this file's introduction; see
`docs/FF_THEORY_DESIGN.md` §10.5 for the role corpora play in the
verification ladder. The exhaustive/planted fuzzers in
`nixie-theories/tests/ff_{oracle,planted_fuzz}.rs` are the soundness
canaries; these files are the *performance* substrate for Phase 5+
step-count measurement.
