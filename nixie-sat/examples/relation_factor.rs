//! Explicit offline relation factorization with an LRAT preprocessing prefix.
//! Usage: relation_factor INPUT.cnf OUTPUT.cnf PREFIX.lrat MAP.json
//! No SAT verdict is produced. Output paths must not already exist.

use nixie_sat::relation_factor::{FactorError, Limits, factor_relations};
use std::fs::{File, OpenOptions};
use std::io::{BufReader, BufWriter, Write};

#[path = "support/relation_input.rs"]
mod relation_input;
use relation_input::parse;

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    if args.len() != 4 {
        return Err("usage: relation_factor INPUT.cnf OUTPUT.cnf PREFIX.lrat MAP.json".into());
    }
    let (vars, original) = parse(BufReader::new(File::open(&args[0])?))?;
    let factored = match factor_relations(vars, &original, Limits::default()) {
        Ok(result) => Some(result),
        Err(FactorError::Limit) => None,
        Err(error) => return Err(error.into()),
    };
    let clauses = factored
        .as_ref()
        .map_or(original.as_slice(), |f| f.clauses());
    // create_new prevents overwriting the source, aliases, and old evidence.
    let mut output = BufWriter::new(
        OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&args[1])?,
    );
    let mut proof = BufWriter::new(
        OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&args[2])?,
    );
    let mut map = BufWriter::new(
        OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&args[3])?,
    );
    writeln!(output, "p cnf {vars} {}", clauses.len())?;
    for clause in clauses {
        for lit in clause {
            write!(output, "{lit} ")?;
        }
        writeln!(output, "0")?;
    }
    let original_count = i64::try_from(original.len())?;
    let (ids, last_id, groups, resolutions) = if let Some(f) = &factored {
        f.write_lrat_prefix(&mut proof)?;
        (
            f.clause_ids().to_vec(),
            f.last_proof_id(),
            f.groups(),
            f.resolutions(),
        )
    } else {
        ((1..=original_count).collect(), original_count, 0, 0)
    };
    let summary = serde_json::json!({
        "schema": "nixie-relation-factor/1", "groups": groups,
        "resolutions": resolutions, "fallback": factored.is_none(),
        "original_clauses": original.len(), "output_clauses": clauses.len(),
        "original_literals": original.iter().map(Vec::len).sum::<usize>(),
        "output_literals": clauses.iter().map(Vec::len).sum::<usize>(),
        "last_proof_id": last_id,
    });
    serde_json::to_writer(
        &mut map,
        &serde_json::json!({"summary": summary, "clause_ids": ids}),
    )?;
    writeln!(map)?;
    output.flush()?;
    proof.flush()?;
    map.flush()?;
    println!("{summary}");
    Ok(())
}

fn main() -> std::process::ExitCode {
    match run() {
        Ok(()) => std::process::ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("relation_factor: {error}");
            std::process::ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::parse;

    #[test]
    fn strict_input_keeps_empty_and_multiline_clauses() {
        let (vars, clauses) =
            parse(&b"c input\np cnf 2 3\n1\n-2 0 0\n2 0\n"[..]).expect("valid CNF");
        assert_eq!(vars, 2);
        assert_eq!(clauses, vec![vec![1, -2], vec![], vec![2]]);
    }

    #[test]
    fn malformed_input_is_never_partially_accepted() {
        for text in [
            "1 0",
            "p cnf 1 1\n2 0",
            "p cnf 1 1\n1",
            "p cnf 1 0\n0",
            "p cnf 1 1\n1 nope 0",
            "p cnf 1 0\np cnf 1 0",
            "p cnf 1 0\n%\n0",
            "p cnf 1 1\n-2147483648 0",
        ] {
            assert!(parse(text.as_bytes()).is_err(), "{text}");
        }
    }
}
