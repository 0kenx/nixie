# Nixie SMT Solver - VS Code Extension

VS Code extension for [Nixie](https://github.com/cool-japan/oxiz), a high-performance SMT solver written in pure Rust.

## Features

### Syntax Highlighting

Full syntax highlighting for SMT-LIB2 files (`.smt2`), including:

- Commands (`set-logic`, `declare-const`, `assert`, `check-sat`, etc.)
- Sorts (`Int`, `Bool`, `Real`, `BitVec`, `Array`, etc.)
- Operators (logical, arithmetic, comparison, bit-vector)
- Comments, strings, and quoted symbols
- Numeric literals (decimal, hexadecimal, binary)

### Language Server Protocol (LSP)

When the Nixie solver is available, the extension uses LSP for:

- **Real-time Diagnostics**: Parenthesis matching, syntax validation
- **Code Completion**: Smart completions for commands, sorts, and operators
- **Hover Information**: Documentation for SMT-LIB2 keywords
- **Document Symbols**: Navigate declarations and definitions

### Run Solver

Execute the solver directly from VS Code:

- **Command**: `Nixie: Run Solver on Current File` (`Ctrl+Shift+R` / `Cmd+Shift+R`)
- View results in the Output panel
- Status bar shows SAT/UNSAT/UNKNOWN result

## Requirements

- [Nixie SMT Solver](https://github.com/cool-japan/oxiz) installed and available in PATH
- VS Code 1.85.0 or later

### Installing Nixie

```bash
# From crates.io
cargo install nixie-cli

# From source
git clone https://github.com/cool-japan/oxiz
cd nixie
cargo install --path nixie-cli
```

## Extension Settings

| Setting | Default | Description |
|---------|---------|-------------|
| `nixie.executablePath` | `"nixie"` | Path to the nixie executable |
| `nixie.timeout` | `30` | Timeout for solver operations (seconds) |
| `nixie.enableLsp` | `true` | Enable Language Server Protocol support |
| `nixie.diagnostics.enabled` | `true` | Enable real-time diagnostics |
| `nixie.diagnostics.delay` | `500` | Delay before running diagnostics (ms) |
| `nixie.format.indentWidth` | `2` | Indentation width for formatting |
| `nixie.solver.logic` | `""` | Default logic (e.g., QF_LIA, QF_BV) |
| `nixie.solver.parallel` | `false` | Enable parallel solving |
| `nixie.solver.threads` | `4` | Number of threads for parallel solving |

## Commands

| Command | Keybinding | Description |
|---------|------------|-------------|
| `Nixie: Run Solver on Current File` | `Ctrl+Shift+R` | Run solver on the active file |
| `Nixie: Check Satisfiability` | - | Run check-sat on current file |
| `Nixie: Get Model` | - | Get model (after SAT result) |
| `Nixie: Restart Language Server` | - | Restart the LSP server |
| `Nixie: Show Solver Information` | - | Display solver version |

## Supported SMT-LIB2 Commands

The extension provides syntax highlighting and completion for all standard SMT-LIB2 commands:

- **Declarations**: `declare-const`, `declare-fun`, `declare-sort`, `define-fun`, `define-sort`
- **Assertions**: `assert`, `check-sat`, `check-sat-assuming`
- **Model**: `get-model`, `get-value`, `get-assignment`
- **Proof**: `get-proof`, `get-unsat-core`, `get-unsat-assumptions`
- **Stack**: `push`, `pop`, `reset`, `reset-assertions`
- **Info**: `set-logic`, `set-option`, `set-info`, `get-option`, `get-info`
- **Control**: `exit`, `echo`

## Supported Logics

- **Propositional**: QF_UF
- **Arithmetic**: QF_LIA, QF_LRA, QF_NIA, QF_NRA, QF_IDL, QF_RDL
- **Bit-vectors**: QF_BV, QF_ABV, QF_AUFBV
- **Arrays**: QF_AX, QF_AUFLIA, QF_AUFNIA
- **Combined**: ALL, HORN, and many more

## Example SMT-LIB2 File

```smtlib2
; Simple linear integer arithmetic example
(set-logic QF_LIA)

; Declare integer variables
(declare-const x Int)
(declare-const y Int)

; Add constraints
(assert (>= x 0))
(assert (>= y 0))
(assert (= (+ x y) 10))
(assert (> x y))

; Check satisfiability
(check-sat)

; Get the model
(get-model)
```

## Development

### Building from Source

```bash
cd nixie-vscode
npm install
npm run compile
```

### Debugging

1. Open the extension folder in VS Code
2. Press F5 to launch Extension Development Host
3. Open an `.smt2` file to test

## License

Apache License 2.0 - see [LICENSE](../LICENSE) for details.

## Contributing

Contributions are welcome! Please see the [main repository](https://github.com/cool-japan/oxiz) for contribution guidelines.
