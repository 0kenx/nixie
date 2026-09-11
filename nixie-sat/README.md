# nixie-sat

CDCL SAT solver implementation for Nixie.

## Overview

This crate implements a modern Conflict-Driven Clause Learning (CDCL) SAT solver with:

- **Two-Watched Literals** - Efficient unit propagation
- **VSIDS** - Variable State Independent Decaying Sum branching heuristic
- **Clause Learning** - First-UIP conflict analysis
- **Incremental Solving** - Push/pop for assumption-based solving

## Architecture

```
┌─────────────────────────────────────────┐
│              Solver                     │
├─────────────────────────────────────────┤
│  ┌─────────┐  ┌─────────┐  ┌─────────┐  │
│  │  Trail  │  │ Watched │  │  VSIDS  │  │
│  │         │  │  Lists  │  │         │  │
│  └─────────┘  └─────────┘  └─────────┘  │
├─────────────────────────────────────────┤
│           Clause Database               │
└─────────────────────────────────────────┘
```

## Usage

```rust
use nixie_sat::{Solver, SolverResult, Lit, Var};

let mut solver = Solver::new();

// Create variables
let x = solver.new_var();
let y = solver.new_var();
let z = solver.new_var();

// Add clauses: (x OR y) AND (NOT x OR z) AND (NOT y OR NOT z)
solver.add_clause([Lit::pos(x), Lit::pos(y)]);
solver.add_clause([Lit::neg(x), Lit::pos(z)]);
solver.add_clause([Lit::neg(y), Lit::neg(z)]);

match solver.solve() {
    SolverResult::Sat => {
        let model = solver.model();
        println!("SAT: {:?}", model);
    }
    SolverResult::Unsat => println!("UNSAT"),
    SolverResult::Unknown => println!("UNKNOWN"),
}
```

## Explicit relation-solving example

For DIMACS inputs containing dense eight-variable functional relations,
`cnf_solve` can apply the existing exact relation transformer in memory:

```bash
cargo build --release -p nixie-sat --example cnf_solve
NIXIE_RELATION_FACTOR=1 target/release/examples/cnf_solve input.cnf
```

This optional mode checks the transformation before solving and validates
every SAT model against the original CNF. Transformation limits fall back
to the original formula. It does not export an UNSAT proof over the original
input; use the standalone `relation_factor` certificate pipeline when proof
files are required. See the [implementation and measured whole-path cost](../docs/studies/2026-09-09-direct-relation-solve.md).

## Modules

### `literal`

Literal and variable representation:
- `Var` - Variable index
- `Lit` - Signed literal (variable + polarity)
- `LBool` - Three-valued logic (True, False, Undef)

### `clause`

Clause representation and database:
- `Clause` - Immutable clause with literals
- `ClauseRef` - Reference to clause in database
- `ClauseDatabase` - Storage for all clauses

### `trail`

Assignment trail for backtracking:
- Decision levels
- Propagation reasons
- Efficient backtracking

### `watched`

Two-watched literal scheme:
- O(1) watch updates during propagation
- Lazy watch list maintenance

### `vsids`

VSIDS branching heuristic:
- Activity-based variable selection
- Exponential decay
- Conflict-driven bumping

## Performance

The solver is optimized for:
- Cache-friendly clause storage
- Minimal allocations during solving
- Fast unit propagation via two-watched literals

## Status (v0.3.1)

| Metric | Value |
|:-------|:------|
| Version | 0.3.1 |
| Status | Stable |
| Tests | 778 passing |
| Source files | 89 |
| Public API items | 1,147+ |

0.3.1 hardening: hyper-binary-resolution clauses are now registered in the
learned/assertion ledgers (previously unreclaimable by clause-DB reduction,
`forget`, or `pop`, which could grow a goal's clause count unboundedly across
repeated push/pop+check cycles).

*Last updated: 2026-07-31*

## License

Apache-2.0
