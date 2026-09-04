# Nixie for Deno

Deno support for Nixie WASM SMT Solver.

## Installation

Import directly from a URL:

```typescript
import { WasmSolver, initNixie } from "https://deno.land/x/nixie/mod.ts";
```

Or use an import map:

```json
{
  "imports": {
    "nixie": "https://deno.land/x/nixie/mod.ts"
  }
}
```

Then:

```typescript
import { WasmSolver, initNixie } from "nixie";
```

## Usage

### Basic Example

```typescript
import { WasmSolver, initNixie } from "https://deno.land/x/nixie/mod.ts";

// Initialize the WASM module
await initNixie();

// Create a solver instance
const solver = new WasmSolver();
solver.setLogic("QF_LIA");
solver.declareConst("x", "Int");
solver.assertFormula("(> x 0)");

const result = solver.checkSat();
console.log("Result:", result); // "sat"

if (result === "sat") {
  const model = solver.getModel();
  console.log("Model:", model);
}
```

### Custom WASM Path

If you have the WASM file in a custom location:

```typescript
await initNixie("./path/to/nixie_wasm_bg.wasm");
```

### Complete Example

```typescript
import { WasmSolver, initNixie } from "https://deno.land/x/nixie/mod.ts";

async function main() {
  // Initialize
  await initNixie();

  // Create solver
  const solver = new WasmSolver();
  solver.setLogic("QF_LIA");
  solver.applyPreset("complete");

  // Declare variables
  solver.declareConst("x", "Int");
  solver.declareConst("y", "Int");

  // Add constraints
  solver.assertFormula("(> x 0)");
  solver.assertFormula("(< y 10)");
  solver.assertFormula("(= (+ x y) 15)");

  // Check satisfiability
  const result = solver.checkSat();
  console.log("Result:", result);

  if (result === "sat") {
    const model = solver.getModel();
    console.log("Model:", JSON.stringify(model, null, 2));

    // Get specific values
    const values = solver.getValue(["x", "y"]);
    console.log("Values:", values);
  }

  // Clean up
  solver.reset();
}

if (import.meta.main) {
  main();
}
```

### Incremental Solving

```typescript
import { WasmSolver, initNixie } from "https://deno.land/x/nixie/mod.ts";

await initNixie();

const solver = new WasmSolver();
solver.setLogic("QF_LIA");
solver.declareConst("x", "Int");

// First check
solver.push();
solver.assertFormula("(> x 5)");
console.log(solver.checkSat()); // "sat"
solver.pop();

// Second check
solver.push();
solver.assertFormula("(< x 0)");
console.log(solver.checkSat()); // "sat"
solver.pop();

// Third check
solver.push();
solver.assertFormula("(= x 10)");
console.log(solver.checkSat()); // "sat"
solver.pop();
```

### Using check-sat-assuming

```typescript
import { WasmSolver, initNixie } from "https://deno.land/x/nixie/mod.ts";

await initNixie();

const solver = new WasmSolver();
solver.setLogic("QF_UF");
solver.declareConst("p", "Bool");
solver.declareConst("q", "Bool");
solver.assertFormula("(or p q)");

// Check with assumption p
const result1 = solver.checkSatAssuming(["p"]);
console.log(result1); // "sat"

// Check with assumptions not p and not q
const result2 = solver.checkSatAssuming(["(not p)", "(not q)"]);
console.log(result2); // "unsat"
```

### Error Handling

```typescript
import { WasmSolver, initNixie } from "https://deno.land/x/nixie/mod.ts";

await initNixie();

const solver = new WasmSolver();

try {
  // This will fail - invalid sort
  solver.declareConst("x", "InvalidSort");
} catch (err) {
  console.error("Error:", err.message);
}

try {
  // Validate before asserting
  solver.setLogic("QF_LIA");
  solver.declareConst("x", "Int");
  solver.validateFormula("(> x 0)"); // OK
  solver.assertFormula("(> x 0)");
} catch (err) {
  console.error("Validation failed:", err.message);
}
```

## Permissions

Deno requires explicit permissions. Depending on your use case, you may need:

```bash
# Read permission for loading WASM file
deno run --allow-read your_script.ts

# Net permission if fetching WASM from URL
deno run --allow-net your_script.ts
```

## API Reference

See the main [Nixie WASM documentation](../README.md) for the complete API reference.

## License

Apache-2.0
