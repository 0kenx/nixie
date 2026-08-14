# oxiz-cli

Command-line interface for OxiZ SMT solver.

## Installation

From crates.io:

```bash
cargo install oxiz-cli
```

Or build from source:

```bash
git clone https://github.com/cool-japan/oxiz
cd oxiz/oxiz-cli
cargo build --release
# Binary will be at: target/release/oxiz
```

## Usage

### Solve SMT-LIB2 Files

```bash
# Solve a single file
oxiz input.smt2

# Solve multiple files
oxiz file1.smt2 file2.smt2 file3.smt2

# Read from stdin
cat input.smt2 | oxiz -
```

### Interactive Mode

```bash
oxiz --interactive

# Or use short flag
oxiz -i
```

In interactive mode, enter SMT-LIB2 commands directly:

```
oxiz> (set-logic QF_LIA)
oxiz> (declare-const x Int)
oxiz> (assert (> x 0))
oxiz> (check-sat)
sat
oxiz> (exit)
```

### Options

```
USAGE:
    oxiz [OPTIONS] [FILES]...

ARGS:
    <FILES>...    Input SMT-LIB2 files (use - for stdin)

OPTIONS:
    -i, --interactive    Run in interactive mode
    -v, --verbose        Enable verbose output
    -t, --timeout <MS>   Set timeout in milliseconds
        --certified-mode Require an independently checked result certificate
    -h, --help           Print help information
    -V, --version        Print version information
```

### Certified mode

`oxiz --certified-mode input.smt2` applies a fail-closed exit gate. A `sat`
candidate is returned only after the original assertion DAG evaluates to true
under the concrete model, using cached exact integer, rational, and bit-vector
operations. An `unsat` candidate is currently returned only when the
propositional skeleton is contradictory without theory semantics: OxiZ
independently builds a complete Tseitin encoding, generates an LRAT refutation,
and checks that refutation in process. A result whose certificate cannot be
constructed or completely checked is reported as `unknown`.

The checker design and current trusted boundary are documented in
[`docs/CERTIFIED_MODE.md`](../docs/CERTIFIED_MODE.md).

The command-line policy cannot be disabled by commands in the input script.
Library users can select the same reversible SMT option with
`(set-option :certified-mode true)`, or call `Context::require_certified_mode()`
for the non-downgradable embedding policy.

## Examples

### Basic Satisfiability

```bash
echo '
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 0))
(assert (< x 10))
(check-sat)
' | oxiz -
```

Output:
```
sat
```

### Unsatisfiable Problem

```bash
echo '
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 10))
(assert (< x 5))
(check-sat)
' | oxiz -
```

Output:
```
unsat
```

## Exit Codes

| Code | Meaning |
|------|---------|
| 0    | Success (satisfiable or completed) |
| 1    | Unsatisfiable |
| 2    | Unknown/Timeout |
| 3    | Parse error |
| 4    | Other error |

## License

Apache-2.0
