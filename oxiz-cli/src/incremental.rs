//! Incremental session mode for `--incremental`.
//!
//! The default multi-file batch path gives *each file its own fresh context*,
//! so a declaration in one file is invisible to the next (see
//! `processor::process_files_sequential`). Incremental mode instead treats the
//! entire input — every file, in order, or all of stdin — as **one continuous
//! incremental session against a single context**: earlier declarations and
//! assertions remain in scope for later files, and `push`/`pop` span the whole
//! session.
//!
//! # Why a single combined execute rather than per-command streaming
//!
//! `Context::execute_script` parses each call with a *fresh, script-local*
//! symbol table (a constant declared by an earlier separate call is unknown to
//! a later one — see the note in `main::enumerate_additional_models`). Feeding
//! commands one at a time through separate `execute_script` calls would
//! therefore fail the moment an assertion referenced a previously-declared
//! symbol. Concatenating the whole session into one script and executing it
//! once keeps every declaration in scope while still processing the commands
//! incrementally inside `execute_script` (which honors `push`/`pop` and
//! sequential `check-sat`s).

use std::io::{self, Read};

use oxiz_solver::Context;

use crate::execute_and_format;
use crate::format::eprintln_colored;
use crate::{Args, Verbosity};

/// Concatenate several per-file scripts into one incremental-session script,
/// separating them with newlines so tokens never run together across a file
/// boundary.
fn combine_scripts(scripts: &[String]) -> String {
    scripts.join("\n")
}

/// Run the CLI in incremental-session mode.
///
/// Reads from stdin when no input files are given, otherwise concatenates
/// every input file in order, then executes the combined session against a
/// single `ctx` so state carries across files.
pub fn run_incremental(ctx: &mut Context, args: &Args, verbosity: Verbosity) {
    if verbosity >= Verbosity::Verbose {
        eprintln_colored(
            args,
            "Incremental mode: treating all input as one continuous session",
        );
    }

    let combined = if args.input.is_empty() {
        let mut script = String::new();
        if let Err(e) = io::stdin().read_to_string(&mut script) {
            eprintln_colored(args, &format!("Error reading stdin: {e}"));
            std::process::exit(1);
        }
        script
    } else {
        let mut scripts = Vec::with_capacity(args.input.len());
        for file in &args.input {
            match std::fs::read_to_string(file) {
                Ok(script) => scripts.push(script),
                Err(e) => {
                    eprintln_colored(args, &format!("Failed to read {}: {e}", file.display()));
                    std::process::exit(1);
                }
            }
        }
        combine_scripts(&scripts)
    };

    let output = execute_and_format(ctx, &combined, args);
    if !output.is_empty() {
        println!("{output}");
    }

    // Signal failure via the exit code when the combined session errored, so a
    // shell/Makefile checking `$?` can detect it (mirrors `run_files`).
    if output.contains("(error") {
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn combine_keeps_all_scripts_in_order() {
        let combined = combine_scripts(&[
            "(declare-const x Int)".to_string(),
            "(assert (> x 0))".to_string(),
        ]);
        assert!(combined.contains("declare-const x"));
        assert!(combined.contains("assert"));
        // Declaration must precede use.
        assert!(combined.find("declare-const").unwrap() < combined.find("assert").unwrap());
    }

    #[test]
    fn combine_separates_files_with_newline() {
        // Without a separator, `Int` and `(assert` on adjacent file boundaries
        // could fuse into one token; the newline prevents that.
        let combined = combine_scripts(&[
            "(declare-const x Int)".to_string(),
            "(check-sat)".to_string(),
        ]);
        assert!(combined.contains("Int)\n(check-sat)"));
    }
}
