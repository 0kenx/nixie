//! Strict source parsing shared by the explicit relation tools.

use std::io::BufRead;

type ParsedCnf = (usize, Vec<Vec<i32>>);

pub fn parse(reader: impl BufRead) -> Result<ParsedCnf, Box<dyn std::error::Error>> {
    let mut header = None;
    let mut clauses = Vec::new();
    let mut pending = Vec::new();
    for line in reader.lines() {
        let line = line?;
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        let tokens: Vec<_> = line.split_whitespace().collect();
        if tokens.first() == Some(&"p") {
            if header.is_some() || tokens.len() != 4 || tokens[1] != "cnf" {
                return Err("invalid or repeated CNF header".into());
            }
            let vars = tokens[2].parse::<usize>()?;
            let count = tokens[3].parse::<usize>()?;
            if vars > i32::MAX as usize {
                return Err("variable count exceeds DIMACS literal range".into());
            }
            header = Some((vars, count));
            continue;
        }
        let Some((vars, count)) = header else {
            return Err("missing CNF header".into());
        };
        // Deliberately strict input: malformed tokens, trailing '%' records,
        // out-of-range literals and mismatched counts are errors, not omissions.
        for token in tokens {
            let lit = token.parse::<i32>()?;
            if lit == 0 {
                clauses.push(core::mem::take(&mut pending));
                if clauses.len() > count {
                    return Err("too many clauses".into());
                }
            } else {
                if lit == i32::MIN || lit.unsigned_abs() as usize > vars {
                    return Err("literal out of range".into());
                }
                pending.push(lit);
            }
        }
    }
    let Some((vars, count)) = header else {
        return Err("missing CNF header".into());
    };
    if !pending.is_empty() || clauses.len() != count {
        return Err("unterminated clause or clause count mismatch".into());
    }
    Ok((vars, clauses))
}
