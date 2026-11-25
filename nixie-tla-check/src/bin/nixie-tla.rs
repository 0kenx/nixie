//! `nixie-tla` – bounded model checking of a TLA+ specification, from the
//! command line, emitting counterexamples in the Informal Trace Format.
//!
//! # Why this looks like `apalache-mc`
//!
//! Because it has to. The tools that consume TLA+ counterexamples already
//! exist and already call Apalache: `tla-connect`, the model-based testing
//! harness for Rust, builds
//!
//! ```text
//! apalache-mc check --inv=Inv --max-error=N --length=K [--cinit=C] [--view=V] \
//!                   --out-dir=DIR Spec.tla
//! ```
//!
//! collects `*.itf.json` from `DIR`, and replays each trace against a driver.
//! Matching that command line – and the exit codes, which Apalache documents
//! and callers branch on – makes this binary a drop-in: point the tool at it
//! instead and nothing else changes.
//!
//! Where it *cannot* be a drop-in it says so out loud rather than pretending.
//! Those places are listed under `simulate` and `--view` below.
//!
//! # Exit codes
//!
//! Apalache's, which are in turn a subset of TLC's:
//!
//! | code | meaning |
//! |------|---------|
//! | 0    | no counterexample within the bound |
//! | 12   | a counterexample was found |
//! | 75   | the specification could not be evaluated (not lowered, not encoded) |
//! | 120  | the specification does not type check |
//! | 150  | the specification does not parse |
//! | 255  | anything else |
//!
//! Note what 0 does **not** mean. A bounded search that finds nothing is
//! silent about longer behaviours; it is not a proof, and `--length` is part
//! of the answer.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use nixie_core::TermManager;
use nixie_tla_check::bmc::{Bmc, Outcome, Roles, SetupError};

/// No counterexample within the bound.
const EXIT_OK: u8 = 0;
/// A counterexample was found.
const EXIT_COUNTEREXAMPLE: u8 = 12;
/// The specification could not be evaluated.
const EXIT_EVAL: u8 = 75;
/// The specification does not type check.
const EXIT_TYPES: u8 = 120;
/// The specification does not parse.
const EXIT_SYNTAX: u8 = 150;
/// Anything else.
const EXIT_SYSTEM: u8 = 255;

/// What the command line asked for.
///
/// `init`, `next` and `inv` are [`Option`]/`Vec` because a `--config=` file
/// can supply them – that is Apalache's precedence: the command line wins,
/// with a warning, and what it does not say comes from the file.
struct Args {
    /// `check` or `simulate`; see `main`'s note on the difference.
    simulate: bool,
    spec: PathBuf,
    /// `--init=`; the `.cfg`'s `INIT` when absent; `Init` when neither says.
    init: Option<String>,
    /// `--next=`; the `.cfg`'s `NEXT` when absent; `Next` when neither says.
    next: Option<String>,
    /// `--inv=NAME` or `--inv=A,B` – a comma-separated list, as in Apalache.
    inv: Option<Vec<String>>,
    /// Extra definitions to assume, from `--cinit`.
    cinit: Option<String>,
    /// Accepted and not used; reported.
    view: Option<String>,
    length: u32,
    max_errors: usize,
    /// `--max-run=`: the number of **simulation** runs. Apalache's meaning,
    /// which is *not* `--max-error`; accepted under `simulate` only.
    max_runs: Option<usize>,
    out_dir: Option<PathBuf>,
    /// `--config=FILE`: a TLC configuration to read roles and constants from.
    config: Option<PathBuf>,
    /// `--no-deadlock`: do not look for deadlocks. Apalache's default is to
    /// look; a `.cfg`'s `CHECK_DEADLOCK FALSE` says the same thing.
    no_deadlock: bool,
    /// `--seed=N`: the simulation PRNG's seed. Deterministic by design –
    /// the same seed gives byte-identical sampled behaviour, where
    /// Apalache's is not reproducible.
    seed: u64,
    /// `--output-traces`: write `example<k>.itf.json` for each sampled run
    /// (simulate), as Apalache does.
    output_traces: bool,
    /// `--run-dir=DIR`: Apalache's flat mirror of the run output. Nixie has
    /// no timestamped run directories, so this is simply where the files go
    /// when `--out-dir` does not say otherwise.
    run_dir: Option<PathBuf>,
    /// `--max-conflicts=N`: a deterministic per-query budget, in conflicts.
    /// A query that exhausts it reports `Unknown` — the same honest answer
    /// the corpus harness gets from `NIXIE_BMC_CONFLICTS`. Unset: no budget.
    max_conflicts: Option<u64>,
    /// `--temporal=NAME`: check the temporal property `NAME` with the lasso
    /// encoding (issue #29). Exactly one name; mutually exclusive with
    /// `--inv`. Apalache's `check --temporal=P`.
    temporal: Option<String>,
    /// `--paranoid` (issue #20, step 6): probe every frame's containment
    /// obligation at every step – `Init /\ Trans_{<k} /\ ~(v@k \subseteq
    /// U_k)` must be `Unsat` – and refuse the check (exit 255, cause named)
    /// when it is not. Off by default: the frame derivation's fixpoint
    /// argument already guarantees containment, and the probes roughly
    /// double the query count.
    paranoid: bool,
}

const USAGE: &str = "\
nixie-tla – bounded model checking of a TLA+ specification

USAGE:
    nixie-tla <check|simulate> [OPTIONS] --out-dir=DIR SPEC.tla

OPTIONS:
    --temporal=NAME     check the temporal property NAME (lasso encoding;
                        a counterexample is a lasso; no lasso within the
                        bound is NOT a proof) -- exclusive with --inv
    --inv=NAMES         the invariant(s) to check, comma-separated
    --init=NAME         the initial-state predicate        [default: Init]
    --next=NAME         the next-state action              [default: Next]
    --length=K          how many steps to unroll           [default: 10]
    --max-error=N       stop after N counterexamples       [default: 1]
    --max-run=N         number of simulation runs (simulate only)
    --cinit=NAME        a definition constraining the CONSTANTs
    --config=FILE       a TLC .cfg supplying roles and constants
    --view=NAME         what makes two counterexamples `the same` one
    --out-dir=DIR       where to write violation<N>.itf.json
    --seed=N            the simulation PRNG seed         [default: 0]
    --max-conflicts=N   per-query solver budget; exhausted = Unknown (deterministic)
    --output-traces     write example<k>.itf.json (simulate)
    --no-cfg            accepted, no effect (a .cfg is not read by default)
    -h, --help          this text

A TLC configuration is read only when --config names it, which is Apalache's
default since 0.25.0; a SPEC.cfg next to the spec produces a hint, nothing
more. In the file, INIT/NEXT/INVARIANT and CONSTANTS are honoured, and a
command-line option overrides the file's value with a warning.

EXIT CODES
    0 no counterexample within the bound   12 counterexample found
   75 could not be evaluated              120 does not type check
  150 does not parse                      255 other
";

fn parse_args() -> Result<Args, String> {
    let mut it = std::env::args().skip(1);
    let Some(mode) = it.next() else {
        return Err(USAGE.to_string());
    };
    if mode == "-h" || mode == "--help" {
        return Err(USAGE.to_string());
    }
    // The subcommand surface (ApalacheCommand). `check` and `simulate` are
    // the checking modes; `parse` and `typecheck` are thin wrappers over
    // this binary's own front end and return their own exit codes (150
    // syntax, 120 types); everything else Apalache spells is refused with
    // the reason, which a script can read, rather than a usage dump.
    match mode.as_str() {
        "check" | "simulate" => {}
        // (parse/typecheck are intercepted in `main` before option parsing.)
        "transpile" => {
            return Err("error: `transpile` is not supported; this checker has no \\
                 intermediate-format output, only `--out-dir` traces"
                .to_string());
        }
        "server" => {
            return Err("error: `server` mode is not supported; it is the Quint \\
                     integration path (deferred, see the tracking issue)"
                .to_string());
        }
        "config" | "test" | "trace" => {
            return Err(format!(
                "error: `{mode}` is not supported; `check` (and `parse`/`typecheck`) \\
                 are this binary's modes"
            ));
        }
        other => return Err(format!("unknown mode `{other}`\n\n{USAGE}")),
    }
    let simulate = mode == "simulate";
    let mut a = Args {
        simulate,
        spec: PathBuf::new(),
        init: None,
        next: None,
        inv: None,
        cinit: None,
        view: None,
        length: 10,
        max_errors: 1,
        max_runs: None,
        seed: 0,
        output_traces: false,
        out_dir: None,
        config: None,
        no_deadlock: false,
        run_dir: None,
        temporal: None,
        max_conflicts: None,
        paranoid: false,
    };
    let mut spec: Option<PathBuf> = None;
    for arg in it {
        // Apalache spells every option `--name=value`, so that is the only
        // form accepted: a caller that writes `--inv Inv` gets told, rather
        // than silently checking a specification with no invariant.
        if let Some(rest) = arg.strip_prefix("--") {
            let (name, value) = match rest.split_once('=') {
                Some((n, v)) => (n, Some(v)),
                None => (rest, None),
            };
            let need = |v: Option<&str>| -> Result<String, String> {
                v.map(std::string::ToString::to_string)
                    .ok_or_else(|| format!("`--{name}` needs a value: `--{name}=…`"))
            };
            match name {
                "help" => return Err(USAGE.to_string()),
                // A comma-separated list, as in Apalache: `--inv=A,B` checks
                // both. An empty entry is a typing slip, not "no invariant".
                "inv" => {
                    let raw = need(value)?;
                    let parts: Vec<String> = raw
                        .split(',')
                        .map(str::trim)
                        .map(std::string::ToString::to_string)
                        .filter(|p| !p.is_empty())
                        .collect();
                    if parts.is_empty() {
                        return Err("`--inv` needs at least one name".to_string());
                    }
                    a.inv = Some(parts);
                }
                "temporal" => a.temporal = Some(need(value)?),
                "max-conflicts" | "max-conflict" => {
                    a.max_conflicts = Some(
                        need(value)?
                            .parse()
                            .map_err(|_| "`--max-conflicts` needs a whole number".to_string())?,
                    )
                }
                "init" => a.init = Some(need(value)?),
                "next" => a.next = Some(need(value)?),
                "cinit" => a.cinit = Some(need(value)?),
                "view" => a.view = Some(need(value)?),
                "seed" => {
                    a.seed = need(value)?
                        .parse()
                        .map_err(|_| "`--seed` needs a whole number".to_string())?;
                }
                "output-traces" => a.output_traces = true,
                "out-dir" => a.out_dir = Some(PathBuf::from(need(value)?)),
                "config" => a.config = Some(PathBuf::from(need(value)?)),
                "no-deadlock" => a.no_deadlock = true,
                "paranoid" => a.paranoid = true,
                // Accepted, no effect: a `.cfg` is not read by default any
                // more (see `run`), so there is nothing left to turn off.
                // Kept rather than rejected so a caller scripted against
                // older Nixie, or against TLC, does not break.
                "no-cfg" => {
                    eprintln!(
                        "note: `--no-cfg` has no effect: a `.cfg` is read only with --config"
                    );
                }
                "length" => {
                    a.length = need(value)?
                        .parse()
                        .map_err(|_| "`--length` needs a whole number".to_string())?;
                }
                "max-error" => {
                    a.max_errors = need(value)?
                        .parse()
                        .map_err(|_| "`--max-error` needs a whole number".to_string())?;
                }
                // Apalache's `--max-run` is the number of random simulation
                // runs – emphatically not `--max-error`. Accepting it as an
                // alias silently changed how many counterexamples a caller
                // asked for, which changes the verdict surface, not the
                // plumbing.
                "max-run" => {
                    a.max_runs = Some(
                        need(value)?
                            .parse()
                            .map_err(|_| "`--max-run` needs a whole number".to_string())?,
                    );
                }
                // ======== the option table for everything else ========
                //
                // One line per option, each in exactly one of three classes:
                // * `Implemented` – handled above;
                // * `AcceptedNoEffect` – performance-only knobs Apalache
                //   documents; accepted with a printed note so scripts do
                //   not break, and **never** an option that changes a
                //   verdict (`--view`, `--no-deadlock`, `--max-run`,
                //   `--temporal`, `--config` are all handled for real above
                //   or refused);
                // * `Refused` – semantics Nixie does not have, with the
                //   reason said out loud (exit 255, not a silent ignore).
                other => match other {
                    "debug"
                    | "profiling"
                    | "smtprof"
                    | "write-intermediate"
                    | "features"
                    | "algo"
                    | "smt-encoding"
                    | "smt-solver"
                    | "tuning-options"
                    | "tuning-options-file"
                    | "discard-disabled" => {
                        eprintln!(
                            "note: `--{other}` is accepted and has no effect here; it is a \\
                             performance knob of Apalache's, not a verdict input"
                        );
                    }
                    "run-dir" => {
                        // Accepted and honoured as the output directory's
                        // flat mirror, below.
                        let v = need(value)?;
                        a.run_dir = Some(PathBuf::from(v));
                    }
                    "temporal" => {
                        return Err("error: `--temporal` properties are not supported yet; \
                             invariants (`--inv`) and deadlock checking are"
                            .to_string());
                    }
                    "timeout-smt" => {
                        return Err(
                            "error: `--timeout-smt` is refused: this checker's budget is a \\
                             deterministic conflict count (NIXIE_BMC_CONFLICTS), and a \\
                             wall-clock timeout would make verdicts machine-load-dependent"
                                .to_string(),
                        );
                    }
                    other => {
                        return Err(format!("unknown option `--{other}`\n\n{USAGE}"));
                    }
                },
            }
        } else if spec.is_none() {
            spec = Some(PathBuf::from(arg));
        } else {
            return Err(format!("more than one specification given: `{arg}`"));
        }
    }
    a.spec = spec.ok_or_else(|| format!("no specification given\n\n{USAGE}"))?;
    Ok(a)
}

/// `parse` and `typecheck`: the loader and the inferencer, alone.
///
/// Apalache has these as their own subcommands, and a ported script uses
/// them as a cheap syntax gate. The exits are the checking codes that
/// match: 150 for a file that does not parse, 120 for one that does not
/// type check, 0 otherwise – and nothing is *checked*.
fn front_end_mode(mode: &str, it: &mut impl Iterator<Item = String>) -> u8 {
    // Only the spec path (and `--config`, for the constants a type check
    // may need) makes sense here; everything else is a checking option.
    let mut spec: Option<PathBuf> = None;
    for arg in it {
        if arg.starts_with("--config=") {
            // Accepted so a scripted pipeline does not break; the constants
            // it names matter to , not to a syntax/type gate over
            // the module as written.
        } else if arg.starts_with("--") {
            eprintln!(
                "error: `{arg}` is a checking option; `{mode}` takes only the spec path and --config="
            );
            println!("EXITCODE: ERROR ({EXIT_SYSTEM})");
            return EXIT_SYSTEM;
        } else if spec.is_none() {
            spec = Some(PathBuf::from(arg));
        } else {
            eprintln!("more than one specification given: `{arg}`");
            println!("EXITCODE: ERROR ({EXIT_SYSTEM})");
            return EXIT_SYSTEM;
        }
    }
    let Some(spec) = spec else {
        eprintln!("no specification given");
        println!("EXITCODE: ERROR ({EXIT_SYSTEM})");
        return EXIT_SYSTEM;
    };
    if !spec.exists() {
        eprintln!("error: no such file: {}", spec.display());
        println!("EXITCODE: ERROR ({EXIT_SYSTEM})");
        return EXIT_SYSTEM;
    }
    let mut loader = nixie_tla_syntax::Loader::new();
    if let Some(dir) = spec.parent().filter(|d| !d.as_os_str().is_empty()) {
        loader = loader.with_search_path(dir);
    }
    if let Ok(lib) = std::env::var("NIXIE_TLA_LIB") {
        for d in lib.split(':').filter(|d| !d.is_empty()) {
            loader = loader.with_search_path(Path::new(d));
        }
    }
    let loaded = match loader.load(&spec) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("could not load {}: {e}", spec.display());
            println!("Parser has found an error");
            println!("EXITCODE: ERROR ({EXIT_SYNTAX})");
            return EXIT_SYNTAX;
        }
    };
    if mode == "parse" {
        println!("Parser has found no errors");
        println!("EXITCODE: OK");
        return EXIT_OK;
    }
    // typecheck: infer every zero-argument definition, and say which name
    // failed if one does.
    let Some(module) = loaded.root_module() else {
        println!("Type checker has found an error");
        println!("EXITCODE: ERROR ({EXIT_SYNTAX})");
        return EXIT_SYNTAX;
    };
    let mut low = nixie_tla::Lowerer::new();
    low.add_spec(&loaded);
    let mut inf = nixie_tla::types::Inference::new();
    let mut failures = Vec::new();
    for unit in &module.units {
        if let nixie_tla_syntax::UnitKind::OpDef {
            name, params, body, ..
        } = &unit.kind
            && params.is_empty()
            && let Ok(k) = low.lower(body)
            && inf.infer(&k).is_err()
        {
            failures.push(name.name.clone());
        }
    }
    if failures.is_empty() {
        println!("Type checker has found no errors");
        println!("EXITCODE: OK");
        EXIT_OK
    } else {
        for name in &failures {
            eprintln!("error: `{name}` does not type check");
        }
        println!("Type checker has found an error");
        println!("EXITCODE: ERROR ({EXIT_TYPES})");
        EXIT_TYPES
    }
}

fn main() -> ExitCode {
    // `parse`/`typecheck` exit with their own codes (150/120), which the
    // `Result<String, _>` plumbing of the option parser cannot carry; they
    // are intercepted here, before option parsing proper.
    let mut argv = std::env::args().skip(1);
    let Some(mode) = argv.next() else {
        eprintln!("{USAGE}");
        return ExitCode::from(EXIT_SYSTEM);
    };
    if mode == "parse" || mode == "typecheck" {
        let mut rest: Vec<String> = argv.collect();
        rest.reverse();
        let mut it = rest.into_iter();
        return ExitCode::from(front_end_mode(&mode, &mut it));
    }
    let args = match parse_args() {
        Ok(a) => a,
        Err(msg) => {
            eprintln!("{msg}");
            return ExitCode::from(EXIT_SYSTEM);
        }
    };
    ExitCode::from(run(&args))
}

#[allow(clippy::too_many_lines)]
/// The `simulate` arm: sampled behaviours (issue #28), not a search. The
/// exit codes are Apalache's, and the "no error" message says what it is
/// about – the sampled runs, never an exhaustive claim.
fn run_simulate(args: &Args, bmc: &mut Bmc, tm: &mut TermManager) -> u8 {
    let runs = args.max_runs.unwrap_or(100);
    let outcome = match bmc.simulate(runs, args.length, args.seed, args.output_traces, tm) {
        Ok(o) => o,
        Err(e) => {
            eprintln!("{e}");
            return exit_for(&e);
        }
    };
    use nixie_tla_check::bmc::SimOutcome;
    match outcome {
        SimOutcome::NoErrorInSampledRuns { runs, dead_ends } => {
            if args.output_traces
                && let Some(dir) = args.out_dir.as_ref().or(args.run_dir.as_ref())
            {
                let name = args
                    .spec
                    .file_name()
                    .and_then(|n| n.to_str())
                    .unwrap_or("spec");
                for (run, trace) in bmc.sampled_traces() {
                    if let Some(doc) = bmc.trace_itf(trace, name)
                        && let Ok(text) = serde_json::to_string_pretty(&doc)
                        && std::fs::create_dir_all(dir).is_ok()
                        && std::fs::write(dir.join(format!("example{run}.itf.json")), text).is_ok()
                    {
                        println!(
                            "  wrote {}",
                            dir.join(format!("example{run}.itf.json")).display()
                        );
                    }
                }
            }
            println!(
                "The outcome is: NoError in {runs} sampled run(s) ({dead_ends} dead-ended \
                 early); this is a sample, not an exhaustive search"
            );
            println!("EXITCODE: OK");
            EXIT_OK
        }
        SimOutcome::Violation { run, step } => {
            println!("counterexample in run {run}: {step} step(s)");
            if let Some(v) = bmc.verification() {
                println!("  independently replayed: {}", describe(v));
            }
            if args.output_traces
                && let Some(dir) = args.out_dir.as_ref().or(args.run_dir.as_ref())
            {
                let name = args
                    .spec
                    .file_name()
                    .and_then(|n| n.to_str())
                    .unwrap_or("spec");
                match write_itf_as("example", bmc, dir, name, run) {
                    Ok(path) => println!("  wrote {path}"),
                    Err(code) => return code,
                }
            }
            println!("The outcome is: Error");
            println!("EXITCODE: ERROR (12)");
            EXIT_COUNTEREXAMPLE
        }
        SimOutcome::Unknown(why) => {
            eprintln!("undecided: {why}");
            println!("The outcome is: Unknown");
            println!("EXITCODE: ERROR (255)");
            EXIT_SYSTEM
        }
    }
}

fn run(args: &Args) -> u8 {
    // `simulate` is accepted because it is `tla-connect`'s default mode, and
    // it does **not** do what Apalache's does. Apalache simulates: it walks
    // random behaviours, cheaply, without exhausting the space. This is a
    // bounded *exhaustive* check, which finds a counterexample within
    // `--length` whenever one exists – stronger per trace and far more
    // expensive at the lengths simulation is usually run at. Said out loud
    // because a caller that asked for cheap sampling and got exhaustive
    // search deserves to know why it is slow.
    if args.simulate {
        // `--max-run` counts simulation runs. Under `check` it is refused
        // rather than reinterpreted – the old alias made `--max-run=5`
        // mean `--max-error=5`, which is a different number of *answers*,
        // not a different pace.
    } else if let Some(runs) = args.max_runs {
        eprintln!(
            "error: `--max-run={runs}` is a `simulate` option (the number of \
             random runs); `check` has no use for it. For several \
             counterexamples, that is `--max-error`."
        );
        return EXIT_SYSTEM;
    }
    // `--view=V` decides what makes two counterexamples *the same one*:
    // with it, `--max-error=N` returns N traces distinct under the view;
    // without it, more than one counterexample cannot be made distinct and
    // Apalache refuses the combination (`ApalacheConfigResolver`: "when
    // maxError > 1, a view is required").
    if args.max_errors > 1 && args.view.is_none() {
        eprintln!(
            "error: --max-error={} requires --view: without a view every further \
             counterexample is near-duplicate of the first, and Apalache refuses the \
             combination",
            args.max_errors
        );
        return EXIT_SYSTEM;
    }
    // Apalache's stdout contract: the output directory line up front, the
    // outcome line at the end, the exit code restated last. Scripts grep
    // for these; see `Tool.scala`'s EXITCODE lines.
    if let Some(dir) = args.out_dir.as_ref().or(args.run_dir.as_ref()) {
        let _ = std::fs::create_dir_all(dir);
        println!("Output directory: {}", dir.display());
    }

    // A missing file or a foreign extension is an invocation error (255), not
    // a parse error (150): Apalache's split, and the one a wrapper can act on
    // – 150 says "your specification is malformed", 255 says "you pointed me
    // at the wrong thing".
    if !args.spec.exists() {
        eprintln!("error: no such file: {}", args.spec.display());
        return EXIT_SYSTEM;
    }
    if args.spec.extension().and_then(|e| e.to_str()) != Some("tla") {
        eprintln!("error: {}: expected a .tla file", args.spec.display());
        return EXIT_SYSTEM;
    }

    let mut loader = nixie_tla_syntax::Loader::new();
    // The specification's own directory, so `EXTENDS` of a sibling module
    // resolves the way it does for every other TLA+ tool.
    if let Some(dir) = args.spec.parent().filter(|d| !d.as_os_str().is_empty()) {
        loader = loader.with_search_path(dir);
    }
    if let Ok(lib) = std::env::var("NIXIE_TLA_LIB") {
        for d in lib.split(':').filter(|d| !d.is_empty()) {
            loader = loader.with_search_path(Path::new(d));
        }
    }
    let spec = match loader.load(&args.spec) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("could not load {}: {e}", args.spec.display());
            return EXIT_SYNTAX;
        }
    };
    let Some(module) = spec.root_module() else {
        eprintln!("{} has no module", args.spec.display());
        return EXIT_SYNTAX;
    };

    // A TLC configuration is read **only** when `--config` names it. That is
    // Apalache's own default (flipped in 0.25.0), and the divergence was
    // dangerous in both directions: reading `<Spec>.cfg` unasked applied its
    // `CONSTRAINT` – pruning exactly the behaviour a violation lived in –
    // while a caller porting from TLC expected `CONSTANTS` to pin what made
    // the spec finite. With `--config` the file supplies `INIT`, `NEXT`,
    // `INVARIANT` and `CONSTANTS`, and a command-line value overrides the
    // file's with a warning, which is `ApalacheConfigResolver`'s precedence.
    let cfg_default_path = args.spec.with_extension("cfg");
    let mut config = nixie_tla_syntax::TlcConfig::default();
    let mut cfg_init: Option<String> = None;
    let mut cfg_next: Option<String> = None;
    let mut cfg_invariants: Vec<String> = Vec::new();
    let mut cfg_deadlock: Option<bool> = None;
    match &args.config {
        Some(path) => {
            if !path.exists() {
                eprintln!(
                    "error: specified TLC config file not found: {}",
                    path.display()
                );
                return EXIT_SYSTEM;
            }
            let text = match std::fs::read_to_string(path) {
                Ok(t) => t,
                Err(e) => {
                    eprintln!("error: {}: {e}", path.display());
                    return EXIT_SYSTEM;
                }
            };
            config = match nixie_tla_syntax::parse_config(&text) {
                Ok(c) => c,
                Err(e) => {
                    eprintln!("could not parse {}: {e}", path.display());
                    return EXIT_SYSTEM;
                }
            };
            match config.behavior.clone() {
                nixie_tla_syntax::BehaviorSpec::InitNext { init, next } => {
                    cfg_init = Some(init);
                    cfg_next = Some(next);
                }
                // No INIT/NEXT in the file: the defaults or the command line
                // decide, exactly as when there is no file at all.
                nixie_tla_syntax::BehaviorSpec::Unspecified => {}
                // `SPECIFICATION` names a temporal behaviour spec – `Spec ==
                // Init /\ [][Next]_vars /\ WF…` – which a bounded
                // unrolling of `Init`/`Next` does not answer. Refused by
                // name rather than approximated: checking `Init /\ Next`
                // against such a spec would silently drop the temporal half.
                nixie_tla_syntax::BehaviorSpec::Temporal(name) => {
                    eprintln!(
                        "error: {} names SPECIFICATION {name}, a temporal \
                         behaviour spec; this checker needs INIT/NEXT (or a \
                         temporal-properties pass, not yet built)",
                        path.display()
                    );
                    return EXIT_SYSTEM;
                }
            }
            cfg_invariants = config.invariants.clone();
            if let Some(deadlock) = config.check_deadlock {
                cfg_deadlock = Some(deadlock);
            }
        }
        None => {
            // Apalache's own hint, in its own words – including naming the
            // file by its *name*, not the caller's whole path, which is what
            // `warnIfTLCConfigIsPresent` prints.
            if cfg_default_path.exists() {
                let name = args
                    .spec
                    .file_stem()
                    .and_then(|s| s.to_str())
                    .unwrap_or("spec");
                eprintln!(
                    "  > TLC config file found in specification directory. To \
                     enable it, pass --config={name}.cfg."
                );
            }
        }
    }

    // Precedence: the command line wins, with a warning naming both sides –
    // `ApalacheConfigResolver.overrideString`'s contract, which a caller
    // scripts against.
    let resolve = |cli: &Option<String>, cfg: Option<String>, what: &str| -> String {
        match (cli, cfg) {
            (Some(c), Some(f)) => {
                eprintln!("warning: --{what}={c} overrides `{what}` from the config ({f})");
                c.clone()
            }
            (Some(c), None) => c.clone(),
            (None, Some(f)) => f,
            (None, None) => String::new(),
        }
    };
    let init = resolve(&args.init, cfg_init, "init");
    let init = if init.is_empty() {
        "Init".to_string()
    } else {
        init
    };
    let next = resolve(&args.next, cfg_next, "next");
    let next = if next.is_empty() {
        "Next".to_string()
    } else {
        next
    };
    // The deadlock setting, Apalache's precedence: the command line wins
    // over the `.cfg`, with the warning `resolveDeadlockSetting` prints.
    let check_deadlocks = if args.no_deadlock {
        if cfg_deadlock == Some(true) {
            eprintln!("warning: TLC CHECK_DEADLOCK=TRUE is overridden by --no-deadlock.");
        }
        false
    } else if let Some(value) = cfg_deadlock {
        eprintln!("Using CHECK_DEADLOCK={value} from the TLC configuration.");
        value
    } else {
        true
    };
    // `--temporal` is its own role: exactly one property, and never
    // together with an invariant list (the two ask different questions of
    // the same trace length; Apalache refuses the mix).
    if let Some(t) = &args.temporal {
        if args.inv.is_some() || !cfg_invariants.is_empty() {
            eprintln!(
                "error: --temporal={t} cannot be combined with --inv (or INVARIANT in the config)"
            );
            return EXIT_SYSTEM;
        }
        if !module.units.iter().any(|u| {
            matches!(&u.kind, nixie_tla_syntax::UnitKind::OpDef { name: n, params, .. }
                if params.is_empty() && n.name == *t)
        }) {
            eprintln!("error: the module has no zero-argument definition named `{t}`");
            return EXIT_EVAL;
        }
    }
    let inv: Vec<String> = match (&args.inv, cfg_invariants.is_empty()) {
        (Some(cli), false) => {
            eprintln!(
                "warning: --inv={} overrides INVARIANT from the config ({})",
                cli.join(","),
                cfg_invariants.join(",")
            );
            cli.clone()
        }
        (Some(cli), true) => cli.clone(),
        (None, false) => cfg_invariants,
        // No invariant is legal **iff** deadlock checking is on: a
        // deadlock-only check is a complete question on its own. With
        // deadlocks off too, there is nothing to check at all.
        (None, true) if check_deadlocks => Vec::new(),
        (None, true) => {
            eprintln!(
                "error: nothing to check: name an invariant with `--inv` (or \
                 put INVARIANT in the --config file), or leave deadlock \
                 checking on"
            );
            return EXIT_SYSTEM;
        }
    };
    // Every name in the list must resolve, or none of them is checked: a
    // subset would answer a narrower question than the caller asked, which is
    // the same silent narrowing a dropped assumption is. A member of an
    // **unnamed** instance counts (`--inv=Safety` with `INSTANCE y2k WITH …`):
    // it is visible unprefixed, which is what a role names.
    let open_member = |name: &str| -> bool {
        module.units.iter().any(|u| {
            matches!(&u.kind, nixie_tla_syntax::UnitKind::Instance { instance, .. }
            if spec
                .modules
                .iter()
                .find(|(n, _)| *n == instance.module.name)
                .is_some_and(|(_, m)| {
                    m.units.iter().any(|u| {
                        matches!(&u.kind, nixie_tla_syntax::UnitKind::OpDef { name: n, params, .. }
                            if params.is_empty() && n.name == name)
                    })
                }))
        })
    };
    for name in &inv {
        if !module.units.iter().any(|u| {
            matches!(&u.kind, nixie_tla_syntax::UnitKind::OpDef { name: n, params, .. }
                if params.is_empty() && n.name == *name)
        }) && !open_member(name)
        {
            eprintln!("error: the module has no zero-argument definition named `{name}`");
            return EXIT_EVAL;
        }
    }
    let inv_names: Vec<&str> = inv.iter().map(String::as_str).collect();

    let cinit: Vec<&str> = args.cinit.as_deref().into_iter().collect();
    let roles = Roles {
        init: &init,
        next: &next,
        inv: &inv_names,
        constraints: &cinit,
    };

    let mut tm = TermManager::new();
    let prepared = match &args.temporal {
        Some(t) => Bmc::prepare_temporal(&spec, module, &init, &next, t, &config, &mut tm),
        None => Bmc::prepare_with_config(&spec, module, roles, &config, &mut tm),
    };
    let mut bmc = match prepared {
        Ok(b) => b,
        Err(e) => {
            eprintln!("{e}");
            return exit_for(&e);
        }
    };
    bmc.set_check_deadlocks(check_deadlocks);
    bmc.set_paranoid(args.paranoid);
    if let Some(n) = args.max_conflicts {
        bmc.set_conflict_limit(n);
    }

    // The view: a state-level definition whose value at a step is what the
    // author considers "the same" counterexample. Anything above state
    // level (an action or temporal view) cannot be evaluated per step and
    // is refused by name.
    if let Some(v) = &args.view {
        let levels = nixie_tla_syntax::check_module(module);
        match levels.trusted_level_of(v) {
            Some(lev) if lev <= nixie_tla_syntax::Level::State => {}
            Some(_) => {
                eprintln!("error: --view={v} is above state level; a view is evaluated per state");
                return EXIT_SYSTEM;
            }
            None => {
                eprintln!("error: --view={v} could not be level-checked; refusing it");
                return EXIT_SYSTEM;
            }
        }
        let mut low = nixie_tla::Lowerer::new();
        low.add_spec(&spec);
        match low.lower_named(module, v) {
            Ok(body) => bmc.set_view(body),
            Err(e) => {
                eprintln!("error: --view={v} could not be lowered: {e}");
                return EXIT_SYSTEM;
            }
        }
    }

    if args.simulate {
        return run_simulate(args, &mut bmc, &mut tm);
    }

    // Up to `--max-error` counterexamples. A bounded query has one *shortest*
    // counterexample, so asking again without ruling that one out returns it
    // forever; each trace found is blocked before the next query. Blocking
    // only narrows the search, so a later trace is still a real model of the
    // encoded formula – and is still replayed before it is written.
    let mut found = 0usize;
    let mut undecided: Option<String> = None;
    while found < args.max_errors {
        let outcome = match bmc.check(args.length, &mut tm) {
            Ok(o) => o,
            Err(e) => {
                eprintln!("{e}");
                return exit_for(&e);
            }
        };
        match outcome {
            Outcome::NoViolationWithin(k) => {
                if found == 0 {
                    match &args.temporal {
                        // A lasso search's bound: no lasso of k steps or
                        // fewer violates the property. Not a proof — a
                        // longer lasso may.
                        Some(t) => println!(
                            "no lasso of {k} step(s) or fewer violates `{t}`; this is a \
                             bound, not a proof that the property holds"
                        ),
                        None => println!("no counterexample of {k} step(s) or fewer"),
                    }
                }
                break;
            }
            // A reachable state with no successor. The same exit code as a
            // counterexample – Apalache's – with the distinction in the
            // message: "Deadlock", not "Error".
            Outcome::Deadlock { step } => {
                println!("The outcome is: Deadlock");
                println!(
                    "a reachable state after {step} step(s) has no successor; the no-successor claim is a proved `Unsat`, not a sample"
                );
                return EXIT_COUNTEREXAMPLE;
            }
            // Every behaviour stopped short of the bound. Exit 0 – Apalache's
            // code – with the outcome line saying what actually happened,
            // because "no error" and "nothing ran that far" are different
            // facts a caller may treat differently.
            Outcome::ExecutionsTooShort => {
                if found == 0 {
                    println!("The outcome is: ExecutionsTooShort");
                    println!(
                        "no behaviour of the full length exists; with deadlock checking off this is not a statement about errors"
                    );
                }
                break;
            }
            // The specification has no behaviours. Not "no error": an
            // invariant vacuously holds over an empty behaviour set, and a
            // caller that greps for the zero exit would congratulate itself
            // on a specification whose assumptions cannot all be true.
            Outcome::AssumptionsUnsatisfiable => {
                eprintln!(
                    "error: the assumptions are contradictory; the specification has no behaviours"
                );
                return EXIT_SYSTEM;
            }
            Outcome::Unknown(why) => {
                undecided = Some(why);
                break;
            }
            Outcome::Violation { step } => {
                found += 1;
                let broken = bmc.violated_invariants();
                let which = if broken.len() == 1 {
                    broken[0].clone()
                } else {
                    format!("[{}]", broken.join(", "))
                };
                match bmc.loop_start() {
                    Some(l) => println!(
                        "counterexample {found}: a lasso of {step} step(s) whose last state \
                         returns to state {l}, violating `{which}`"
                    ),
                    None => println!("counterexample {found}: {step} step(s), invariant {which}"),
                }
                if let Some(v) = bmc.verification() {
                    println!("  independently replayed: {}", describe(v));
                }
                let out_dir = args.out_dir.as_ref().or(args.run_dir.as_ref());
                if let Some(dir) = out_dir {
                    let name = args
                        .spec
                        .file_name()
                        .and_then(|n| n.to_str())
                        .unwrap_or("spec");
                    match write_itf_as("violation", &bmc, dir, name, found) {
                        Ok(path) => println!("  wrote {path}"),
                        Err(code) => return code,
                    }
                }
                if found >= args.max_errors {
                    break;
                }
                // Nothing to say "not that one" with means asking again would
                // hand back the same states. Stop, and say why.
                if !bmc.block_counterexample(&mut tm) {
                    eprintln!(
                        "note: that counterexample could not be ruled out, so no further \
                         traces were searched for"
                    );
                    break;
                }
            }
        }
    }

    if found == 0 {
        if let Some(why) = undecided {
            eprintln!("undecided: {why}");
            println!("The outcome is: Unknown");
            println!("EXITCODE: ERROR (255)");
            return EXIT_SYSTEM;
        }
        if args.temporal.is_some() {
            // Apalache's exit code for a passing `--temporal` check is OK
            // too; the outcome line says what was actually established.
            println!("The outcome is: NoError (no violating lasso within the bound)");
        } else {
            println!("The outcome is: NoError");
        }
        println!("EXITCODE: OK");
    } else {
        if let Some(why) = undecided {
            eprintln!("note: the search stopped early: {why}");
        }
        if found < args.max_errors {
            eprintln!(
                "note: {found} counterexample(s) found; --max-error/--max-run={} asked for more",
                args.max_errors
            );
        }
        println!("The outcome is: Error");
        println!("EXITCODE: ERROR ({EXIT_COUNTEREXAMPLE})");
        return EXIT_COUNTEREXAMPLE;
    }
    EXIT_OK
}

/// Write one counterexample as `violation<n>.itf.json` (check) or one
/// sampled trace as `example<k>.itf.json` (simulate – Apalache's naming).
fn write_itf_as(prefix: &str, bmc: &Bmc, dir: &Path, spec: &str, n: usize) -> Result<String, u8> {
    let Some(doc) = bmc.counterexample_itf(spec) else {
        eprintln!("the counterexample could not be read back, so no ITF was written");
        return Err(EXIT_COUNTEREXAMPLE);
    };
    let text = match serde_json::to_string_pretty(&doc) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("could not render the counterexample as ITF: {e}");
            return Err(EXIT_SYSTEM);
        }
    };
    if let Err(e) = std::fs::create_dir_all(dir) {
        eprintln!("could not create {}: {e}", dir.display());
        return Err(EXIT_SYSTEM);
    }
    let out = dir.join(format!("{prefix}{n}.itf.json"));
    if let Err(e) = std::fs::write(&out, text) {
        eprintln!("could not write {}: {e}", out.display());
        return Err(EXIT_SYSTEM);
    }
    Ok(out.display().to_string())
}

/// Which of Apalache's exit codes a setup failure is.
fn exit_for(e: &SetupError) -> u8 {
    match e {
        SetupError::Types(_) | SetupError::NoSort { .. } => EXIT_TYPES,
        // A violated assumption is not a counterexample and not a defect in
        // the specification's *other* parts: TLC and Apalache report it and
        // abort, which is the 255 bucket here. It must never read as 12 –
        // there is no behaviour to show.
        SetupError::AssumptionViolated { .. } => EXIT_SYSTEM,
        // A frame the paranoid probe refused is a declined check, not a
        // counterexample: the 255 bucket, with the named cause in the
        // message.
        SetupError::FrameEscaped { .. } => EXIT_SYSTEM,
        // `--inv=P` where `P` is a temporal formula: Apalache's integration
        // corpus has this exact cell at **255** (`check --inv=FalseLiveness
        // LongPrefix.tla` → EXITCODE: ERROR (255)), unlike a merely
        // malformed role, which is 75. The property is fine; the *question*
        // was asked with the wrong flag, and that is a usage error.
        SetupError::Level { found, .. } if found == "a temporal formula" => EXIT_SYSTEM,
        SetupError::NoSuchDefinition(_)
        | SetupError::Lower { .. }
        | SetupError::Encode { .. }
        | SetupError::Level { .. }
        | SetupError::Replacement { .. } => EXIT_EVAL,
    }
}

fn describe(v: &nixie_tla_check::bmc::Verification) -> String {
    use nixie_tla_check::bmc::Verification;
    match v {
        Verification::Replayed => "yes".to_string(),
        Verification::NotDecoded(why) => format!("no, the model could not be read back: {why}"),
        Verification::NotReplayed(why) => format!("no, the trace does not replay: {why}"),
    }
}
