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
struct Args {
    /// `check` or `simulate`; see `main`'s note on the difference.
    simulate: bool,
    spec: PathBuf,
    init: String,
    next: String,
    inv: Option<String>,
    /// Extra definitions to assume, from `--cinit`.
    cinit: Option<String>,
    /// Accepted and not used; reported.
    view: Option<String>,
    length: u32,
    max_errors: usize,
    out_dir: Option<PathBuf>,
    /// Read `<spec>.cfg` for constants. On by default; `--no-cfg` turns it off.
    read_cfg: bool,
}

const USAGE: &str = "\
nixie-tla — bounded model checking of a TLA+ specification

USAGE:
    nixie-tla <check|simulate> [OPTIONS] --out-dir=DIR SPEC.tla

OPTIONS:
    --inv=NAME          the invariant to check (required)
    --init=NAME         the initial-state predicate        [default: Init]
    --next=NAME         the next-state action              [default: Next]
    --length=K          how many steps to unroll           [default: 10]
    --max-error=N       stop after N counterexamples       [default: 1]
    --max-run=N         alias of --max-error, for `simulate`
    --cinit=NAME        a definition constraining the CONSTANTs
    --view=NAME         accepted, not used (reported on stderr)
    --out-dir=DIR       where to write violation<N>.itf.json
    --no-cfg            do not read SPEC.cfg for CONSTANT values
    -h, --help          this text

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
        init: "Init".to_string(),
        next: "Next".to_string(),
        inv: None,
        cinit: None,
        view: None,
        length: 10,
        max_errors: 1,
        out_dir: None,
        read_cfg: true,
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
                "inv" => a.inv = Some(need(value)?),
                "init" => a.init = need(value)?,
                "next" => a.next = need(value)?,
                "cinit" => a.cinit = Some(need(value)?),
                "view" => a.view = Some(need(value)?),
                "out-dir" => a.out_dir = Some(PathBuf::from(need(value)?)),
                "no-cfg" => a.read_cfg = false,
                "length" => {
                    a.length = need(value)?
                        .parse()
                        .map_err(|_| "`--length` needs a whole number".to_string())?;
                }
                "max-error" | "max-run" => {
                    a.max_errors = need(value)?
                        .parse()
                        .map_err(|_| format!("`--{name}` needs a whole number"))?;
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
    if a.inv.is_none() {
        return Err(format!("`--inv=NAME` is required\n\n{USAGE}"));
    }
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
    }
    if let Some(v) = &args.view {
        eprintln!("note: `--view={v}` is not used: this checker has no trace-diversity view");
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

    // The `.cfg` supplies `CONSTANT` values and replacements; the command line
    // keeps the roles. That split is deliberate: Apalache does not read a
    // `.cfg` at all, so a caller porting from it must not find its invariant
    // silently replaced — but a constant the file pins is what makes `1..N`
    // finite, and refusing to read it would decline specifications for no
    // reason.
    let cfg_path = args.spec.with_extension("cfg");
    let config = if args.read_cfg {
        match std::fs::read_to_string(&cfg_path) {
            Ok(text) => match nixie_tla_syntax::parse_config(&text) {
                Ok(c) => {
                    eprintln!(
                        "note: read {} for CONSTANT values (--no-cfg to ignore)",
                        cfg_path.display()
                    );
                    Some(c)
                }
                Err(e) => {
                    eprintln!("could not parse {}: {e}", cfg_path.display());
                    return EXIT_SYNTAX;
                }
            },
            Err(_) => None,
        }
    } else {
        None
    };

    let Some(inv) = args.inv.as_deref() else {
        eprintln!("`--inv=NAME` is required");
        return EXIT_SYSTEM;
    };
    let cinit: Vec<&str> = args.cinit.as_deref().into_iter().collect();
    let roles = Roles {
        init: &args.init,
        next: &args.next,
        inv,
        constraints: &cinit,
    };

    let mut tm = TermManager::new();
    let empty = nixie_tla_syntax::TlcConfig::default();
    let mut bmc = match Bmc::prepare_with_config(
        &spec,
        module,
        roles,
        config.as_ref().unwrap_or(&empty),
        &mut tm,
    ) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("{e}");
            return exit_for(&e);
        }
    };

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
            Outcome::Unknown(why) => {
                undecided = Some(why);
                break;
            }
            Outcome::Violation { step } => {
                found += 1;
                println!("counterexample {found}: {step} step(s)");
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
