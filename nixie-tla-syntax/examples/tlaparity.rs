//! Compare `nixie-tla-syntax` against SANY's verdicts.
//!
//! Driven by `bench/tla_parity/run_parity.sh`, which produces the SANY side.
//! Takes two files: the corpus listing, and `LevelDump`'s output.
//!
//! Reports two things:
//!
//! * **Syntax parity.** The gate is one-sided — every file SANY parses must
//!   parse here. Accepting more is allowed, because the long-term target is a
//!   superset; those files are listed for review rather than counted as
//!   failures.
//! * **Level parity.** For files SANY fully resolved, every definition must
//!   get the same level. This is the check that the level walk is right, as
//!   opposed to merely quiet.

use std::collections::HashMap;
use std::process::ExitCode;

fn main() -> ExitCode {
    let mut args = std::env::args().skip(1);
    let (Some(list), Some(dump)) = (args.next(), args.next()) else {
        eprintln!("usage: tlaparity <corpus-list> <sany-level-dump>");
        return ExitCode::from(2);
    };
    let Ok(list) = std::fs::read_to_string(&list) else {
        eprintln!("cannot read {list}");
        return ExitCode::from(2);
    };
    let Ok(dump) = std::fs::read_to_string(&dump) else {
        eprintln!("cannot read {dump}");
        return ExitCode::from(2);
    };

    /// What SANY made of a file.
    enum Sany {
        /// Parsed and fully resolved; levels available.
        Levels(HashMap<String, u8>),
        /// Parsed, but an `EXTENDS` could not be resolved, so no levels.
        Resolved,
        /// SANY could not parse it. This is the syntax verdict.
        ParseError,
    }

    let mut sany: HashMap<String, Sany> = HashMap::new();
    let mut current: Option<String> = None;
    for line in dump.lines() {
        if let Some(rest) = line.strip_prefix("#FILE\t") {
            current = Some(canon(rest));
            sany.insert(canon(rest), Sany::Levels(HashMap::new()));
        } else if let Some(rest) = line.strip_prefix("#PARSE_ERR\t") {
            let path = rest.split('\t').next().unwrap_or_default();
            sany.insert(canon(path), Sany::ParseError);
            current = None;
        } else if let Some(rest) = line.strip_prefix("#RESOLVE_ERR\t") {
            let path = rest.split('\t').next().unwrap_or_default();
            sany.insert(canon(path), Sany::Resolved);
            current = None;
        } else if let Some(file) = &current
            && let Some((name, lvl)) = line.split_once('\t')
            && let Ok(lvl) = lvl.trim().parse::<u8>()
            && let Some(Sany::Levels(map)) = sany.get_mut(file)
        {
            map.insert(name.to_string(), lvl);
        }
    }

    let mut syntax_gap = Vec::new();
    let mut superset = Vec::new();
    let mut both_ok = 0usize;
    let mut level_files = 0usize;
    let mut level_defs = 0usize;
    let mut level_mismatch: Vec<String> = Vec::new();
    let mut unresolved_files = 0usize;
    let mut skipped_untrusted = 0usize;
    let mut known_defects = 0usize;

    for path in list.lines().map(str::trim).filter(|p| !p.is_empty()) {
        let key = canon(path);
        let Ok(src) = std::fs::read_to_string(path) else {
            continue;
        };
        let ours = nixie_tla_syntax::parse_file(&src);
        // Follow EXTENDS so that imported levels are known. Without it most
        // levels are untrusted and never reach the comparison at all; with it
        // the suite actually exercises the level walk.
        let resolved = {
            let mut loader = nixie_tla_syntax::Loader::new();
            if let Ok(lib) = std::env::var("TLA_LIBRARY") {
                for dir in lib.split(':').filter(|d| !d.is_empty()) {
                    loader = loader.with_search_path(dir);
                }
            }
            loader.load(std::path::Path::new(path)).ok()
        };
        // `#FILE` and `#RESOLVE_ERR` both mean SANY parsed the file;
        // `#PARSE_ERR` is the only syntax rejection.
        let sany_entry = sany.get(&key);
        let sany_parsed = matches!(sany_entry, Some(Sany::Levels(_) | Sany::Resolved));

        match (&ours, sany_parsed) {
            (Err(e), true) => syntax_gap.push(format!("{path}: {e}")),
            (Ok(_), false) => superset.push(path.to_string()),
            (Ok(_), true) => both_ok += 1,
            (Err(_), false) => {}
        }

        let (Ok(parsed), Some(Sany::Levels(expected))) = (&ours, sany_entry) else {
            if matches!(sany_entry, Some(Sany::Resolved)) {
                unresolved_files += 1;
            }
            continue;
        };
        level_files += 1;
        let report = match &resolved {
            Some(spec) => nixie_tla_syntax::check_spec(spec)
                .into_iter()
                .find(|(n, _)| *n == spec.root)
                .map(|(_, r)| r)
                .unwrap_or_else(|| nixie_tla_syntax::check_module(&parsed.module)),
            None => nixie_tla_syntax::check_module(&parsed.module),
        };
        // Only compare levels we actually established. A tainted level is a
        // guess (an unresolved `EXTENDS` or instance member), and holding a
        // guess against SANY measures the missing module resolution, not the
        // level walk.
        let got: HashMap<&str, u8> = report
            .definitions
            .iter()
            .filter(|(_, l)| !l.unresolved)
            .map(|(n, l)| (n.as_str(), l.level as u8))
            .collect();
        let untrusted = report.definitions.len() - got.len();
        skipped_untrusted += untrusted;
        for (name, want) in expected {
            let Some(&mine) = got.get(name.as_str()) else {
                continue;
            };
            level_defs += 1;
            if mine != *want {
                if is_known_defect(path, name) {
                    known_defects += 1;
                    continue;
                }
                level_mismatch.push(format!(
                    "{path}: {name} — SANY {}, nixie {}",
                    level_name(*want),
                    level_name(mine)
                ));
            }
        }
    }

    println!("\n=== syntax parity ===");
    println!("  both accept                     : {both_ok}");
    println!("  SANY accepts, nixie rejects     : {}", syntax_gap.len());
    for g in syntax_gap.iter().take(30) {
        println!("      GAP {g}");
    }
    println!("  nixie accepts, SANY rejects     : {}", superset.len());
    for s in superset.iter().take(30) {
        println!("      superset {s}");
    }

    println!("\n=== level parity ===");
    println!("  files SANY could fully resolve  : {level_files}");
    println!("  files SANY could not resolve    : {unresolved_files}");
    println!("  definitions compared            : {level_defs}");
    println!("  definitions skipped (untrusted) : {skipped_untrusted}");
    println!("  known SANY defects excluded     : {known_defects}");
    println!(
        "  level mismatches                : {}",
        level_mismatch.len()
    );
    for m in level_mismatch.iter().take(40) {
        println!("      MISMATCH {m}");
    }

    if syntax_gap.is_empty() && level_mismatch.is_empty() {
        println!("\nPARITY OK");
        ExitCode::SUCCESS
    } else {
        println!("\nPARITY FAILED");
        ExitCode::FAILURE
    }
}

/// Definitions where SANY's own answer is wrong, so a mismatch is expected.
///
/// Each entry is `(file suffix, definition name, why)`. Keep this list tiny
/// and justified: it is an escape hatch from the oracle, and every entry is a
/// claim that the reference implementation is mistaken.
const KNOWN_ORACLE_DEFECTS: &[(&str, &str, &str)] = &[(
    "NonLinearArithmetic.tla",
    "SquareNonNegative",
    // Reproducer: with `VARIABLE x`, SANY gives `x * x` constant level but
    // `x + x`, `x - x`, `x \div x`, `x = x`, `x .. x` and a user-declared
    // `F(x, x)` all correctly give state level. Only `*` loses the level.
    // `x * x` plainly depends on the state, so nixie's answer is the right one.
    "SANY assigns constant level to `x * x` for a state-level x; only `*` is affected",
)];

fn is_known_defect(path: &str, name: &str) -> bool {
    KNOWN_ORACLE_DEFECTS
        .iter()
        .any(|(suffix, def, _)| path.ends_with(suffix) && *def == name)
}

fn canon(p: &str) -> String {
    std::fs::canonicalize(p.trim())
        .map(|p| p.display().to_string())
        .unwrap_or_else(|_| p.trim().to_string())
}

fn level_name(l: u8) -> &'static str {
    match l {
        0 => "constant",
        1 => "state",
        2 => "action",
        3 => "temporal",
        _ => "?",
    }
}
