# QF_NIA counterexample fixtures

Self-contained SMT-LIB2 instances for quantifier-free nonlinear (and a few
linear) integer arithmetic. Each file records the ground-truth verdict as:

```
;; expected: sat
```

or `unsat`.

The integration test requires an **exact** match on every fixture (no gap
allowlist). Failures print the full per-file table (`ok` / `wrong` / `unknown`).

## Run

```bash
cargo test -p oxiz-solver --test qf_nia_ce -- --nocapture
```
