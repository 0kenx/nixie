//! `nixie-tla` — bounded model checking of a TLA+ specification, from the
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
//! Matching that command line — and the exit codes, which Apalache documents
//! and callers branch on — makes this binary a drop-in: point the tool at it
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
/// can supply them — that is Apalache's precedence: the command line wins,
/// with a warning, and what it does not say comes from the file.
struct Args {
    /// `check` or `simulate`; see `main`'s note on the difference.
    simulate: bool,
    spec: PathBuf,
    /// `--init=`; the `.cfg`'s `INIT` when absent; `Init` when neither says.
    init: Option<String>,
    /// `--next=`; the `.cfg`'s `NEXT` when absent; `Next` when neither says.
    next: Option<String>,
    /// `--inv=NAME` or `--inv=A,B` — a comma-separated list, as in Apalache.
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
}

const USAGE: &str = "\
nixie-tla — bounded model checking of a TLA+ specification

USAGE:
    nixie-tla <check|simulate> [OPTIONS] --out-dir=DIR SPEC.tla

OPTIONS:
    --inv=NAMES         the invariant(s) to check, comma-separated
    --init=NAME         the initial-state predicate        [default: Init]
    --next=NAME         the next-state action              [default: Next]
    --length=K          how many steps to unroll           [default: 10]
    --max-error=N       stop after N counterexamples       [default: 1]
    --max-run=N         number of simulation runs (simulate only)
    --cinit=NAME        a definition constraining the CONSTANTs
    --config=FILE       a TLC .cfg supplying roles and constants
    --view=NAME         accepted, not used (reported on stderr)
    --out-dir=DIR       where to write violation<N>.itf.json
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
    let simulate = match mode.as_str() {
        "check" => false,
        "simulate" => true,
        other => return Err(format!("unknown mode `{other}`\n\n{USAGE}")),
    };
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
        out_dir: None,
        config: None,
        no_deadlock: false,
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
                "init" => a.init = Some(need(value)?),
                "next" => a.next = Some(need(value)?),
                "cinit" => a.cinit = Some(need(value)?),
                "view" => a.view = Some(need(value)?),
                "out-dir" => a.out_dir = Some(PathBuf::from(need(value)?)),
                "config" => a.config = Some(PathBuf::from(need(value)?)),
                "no-deadlock" => a.no_deadlock = true,
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
                // runs — emphatically not `--max-error`. Accepting it as an
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
                other => return Err(format!("unknown option `--{other}`\n\n{USAGE}")),
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

fn main() -> ExitCode {
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
fn run(args: &Args) -> u8 {
    // `simulate` is accepted because it is `tla-connect`'s default mode, and
    // it does **not** do what Apalache's does. Apalache simulates: it walks
    // random behaviours, cheaply, without exhausting the space. This is a
    // bounded *exhaustive* check, which finds a counterexample within
    // `--length` whenever one exists — stronger per trace and far more
    // expensive at the lengths simulation is usually run at. Said out loud
    // because a caller that asked for cheap sampling and got exhaustive
    // search deserves to know why it is slow.
    if args.simulate {
        eprintln!(
            "note: `simulate` runs a bounded exhaustive check here, not random \
             simulation; it is stronger within --length and slower"
        );
        // `--max-run` counts simulation runs, and only makes sense where
        // there are runs to count. Under `check` it is refused rather than
        // reinterpreted — the old alias made `--max-run=5` mean `--max-error=5`,
        // which is a different number of *answers*, not a different pace.
        if let Some(runs) = args.max_runs
            && runs != 100
        {
            eprintln!(
                "note: `--max-run={runs}` counts sampled runs in Apalache's \
                 simulation; this checker is exhaustive within --length, so \
                 the run count does not bound anything here"
            );
        }
    } else if let Some(runs) = args.max_runs {
        eprintln!(
            "error: `--max-run={runs}` is a `simulate` option (the number of \
             random runs); `check` has no use for it. For several \
             counterexamples, that is `--max-error`."
        );
        return EXIT_SYSTEM;
    }
    if let Some(v) = &args.view {
        eprintln!("note: `--view={v}` is not used: this checker has no trace-diversity view");
    }

    // A missing file or a foreign extension is an invocation error (255), not
    // a parse error (150): Apalache's split, and the one a wrapper can act on
    // — 150 says "your specification is malformed", 255 says "you pointed me
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
    // `CONSTRAINT` — pruning exactly the behaviour a violation lived in —
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
                // `SPECIFICATION` names a temporal behaviour spec — `Spec ==
                // Init /\ [][Next]_vars /\ WF…` — which a bounded
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
            // Apalache's own hint, in its own words — including naming the
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

    // Precedence: the command line wins, with a warning naming both sides —
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
    // the same silent narrowing a dropped assumption is.
    for name in &inv {
        if !module.units.iter().any(|u| {
            matches!(&u.kind, nixie_tla_syntax::UnitKind::OpDef { name: n, params, .. }
                if params.is_empty() && n.name == *name)
        }) {
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
    let mut bmc = match Bmc::prepare_with_config(&spec, module, roles, &config, &mut tm) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("{e}");
            return exit_for(&e);
        }
    };
    bmc.set_check_deadlocks(check_deadlocks);

    // Up to `--max-error` counterexamples. A bounded query has one *shortest*
    // counterexample, so asking again without ruling that one out returns it
    // forever; each trace found is blocked before the next query. Blocking
    // only narrows the search, so a later trace is still a real model of the
    // encoded formula — and is still replayed before it is written.
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
                    println!("no counterexample of {k} step(s) or fewer");
                }
                break;
            }
            // A reachable state with no successor. The same exit code as a
            // counterexample — Apalache's — with the distinction in the
            // message: "Deadlock", not "Error".
            Outcome::Deadlock { step } => {
                println!("The outcome is: Deadlock");
                println!(
                    "a reachable state after {step} step(s) has no successor; the no-successor claim is a proved `Unsat`, not a sample"
                );
                return EXIT_COUNTEREXAMPLE;
            }
            // Every behaviour stopped short of the bound. Exit 0 — Apalache's
            // code — with the outcome line saying what actually happened,
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
                println!("counterexample {found}: {step} step(s), invariant {which}");
                if let Some(v) = bmc.verification() {
                    println!("  independently replayed: {}", describe(v));
                }
                if let Some(dir) = &args.out_dir {
                    let name = args
                        .spec
                        .file_name()
                        .and_then(|n| n.to_str())
                        .unwrap_or("spec");
                    match write_itf(&bmc, dir, name, found) {
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
            return EXIT_SYSTEM;
        }
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
        return EXIT_COUNTEREXAMPLE;
    }
    EXIT_OK
}

/// Write one counterexample as `violation<n>.itf.json`.
fn write_itf(bmc: &Bmc, dir: &Path, spec: &str, n: usize) -> Result<String, u8> {
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
    let out = dir.join(format!("violation{n}.itf.json"));
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
        // abort, which is the 255 bucket here. It must never read as 12 —
        // there is no behaviour to show.
        SetupError::AssumptionViolated { .. } => EXIT_SYSTEM,
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
