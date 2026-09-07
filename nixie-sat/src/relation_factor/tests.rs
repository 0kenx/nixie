use super::*;
use nixie_proof::lrat_check::check_lrat_proof;

fn relation(vars: [i32; 8], allowed: &[u8]) -> Vec<Vec<i32>> {
    (0..=u8::MAX)
        .filter(|row| !allowed.contains(row))
        .map(|row| clause(&vars, u8::MAX, row))
        .collect()
}

fn table() -> Vec<Vec<i32>> {
    relation(
        [1, 2, 3, 4, 5, 6, 7, 8],
        &(0..16).map(|x| x | (x << 4)).collect::<Vec<_>>(),
    )
}

fn satisfies(cnf: &[Vec<i32>], assignment: usize) -> bool {
    cnf.iter().all(|c| {
        c.iter()
            .any(|&lit| ((assignment >> (lit.unsigned_abs() - 1)) & 1 != 0) == (lit > 0))
    })
}

fn equivalent(original: &[Vec<i32>], result: &Factorization, vars: usize) {
    for assignment in 0..1 << vars {
        assert_eq!(
            satisfies(original, assignment),
            satisfies(result.clauses(), assignment),
            "assignment {assignment}"
        );
    }
}

fn prefix(result: &Factorization) -> String {
    let mut bytes = Vec::new();
    result.write_lrat_prefix(&mut bytes).expect("write prefix");
    String::from_utf8(bytes).expect("ASCII LRAT")
}

fn check_prefix(original: &[Vec<i32>], result: &Factorization) {
    let report = check_lrat_proof(original, &prefix(result));
    assert_eq!(report.additions_checked, result.resolutions(), "{report:?}");
    assert_eq!(
        report.failure.as_deref(),
        Some("proof stream ended without ever deriving (or being given) the empty clause")
    );
    assert!(
        !report.verified,
        "a preprocessing prefix is not an UNSAT proof"
    );
    // Independently replay active IDs, including deletions, and require exact
    // output membership. LRAT checks alone do not validate the output mapping.
    let mut active: BTreeMap<i64, Vec<i32>> = original
        .iter()
        .enumerate()
        .map(|(i, c)| (i as i64 + 1, c.clone()))
        .collect();
    for step in &result.steps {
        assert!(
            step.parents
                .iter()
                .all(|p| *p < step.id && active.contains_key(p))
        );
        assert!(active.insert(step.id, step.clause.clone()).is_none());
    }
    for id in &result.deleted {
        assert!(active.remove(id).is_some());
    }
    assert_eq!(active.len(), result.clauses().len());
    for (id, clause) in result.clause_ids().iter().zip(result.clauses()) {
        assert_eq!(active.get(id), Some(clause));
    }
}

#[test]
fn factors_exact_relation_and_checks_every_proof_addition() {
    let original = table();
    let result = factor_relations(8, &original, Limits::default()).expect("factor");
    assert_eq!(result.groups(), 1);
    assert_eq!(result.clauses().len(), 64);
    assert!(result.clauses().iter().all(|c| c.len() == 5));
    assert_eq!(result.resolutions(), 448);
    equivalent(&original, &result, 8);
    check_prefix(&original, &result);
    let mut corrupt = prefix(&result);
    let first_hint = corrupt
        .lines()
        .next()
        .expect("first step")
        .split_whitespace()
        .nth(9)
        .expect("first parent")
        .to_string();
    // Replace a real parent with a never-allocated ID on the first line.
    let first_line = corrupt.lines().next().expect("first step").to_string();
    let mut tokens: Vec<_> = first_line.split_whitespace().map(str::to_owned).collect();
    assert_eq!(tokens[9], first_hint);
    tokens[9] = "99999999".into();
    corrupt.replace_range(..first_line.len(), &tokens.join(" "));
    let report = check_lrat_proof(&original, &corrupt);
    assert_eq!(report.additions_checked, 0);
    assert!(
        report
            .failure
            .as_deref()
            .is_some_and(|s| s.contains("failed to verify"))
    );
}

#[test]
fn signed_permuted_nonlinear_tables_have_exact_models_and_proofs() {
    for salt in 0..8u8 {
        let allowed: Vec<_> = (0..16u8)
            .map(|x| x | (((x.wrapping_mul(7) ^ (x >> 1) ^ salt) & 15) << 4))
            .collect();
        let mut original = relation([8, 3, 6, 1, 7, 2, 5, 4], &allowed);
        for (i, c) in original.iter_mut().enumerate() {
            for lit in c.iter_mut() {
                if lit.unsigned_abs() as u8 & salt != 0 {
                    *lit = -*lit;
                }
            }
            c.rotate_left(i % 8);
        }
        original.reverse();
        let result = factor_relations(8, &original, Limits::default()).expect("factor");
        assert_eq!(result.groups(), 1);
        equivalent(&original, &result, 8);
        check_prefix(&original, &result);
    }
}

#[test]
fn incomplete_and_nonfunctional_relations_remain_verbatim() {
    let mut missing = table();
    missing.pop();
    missing.push(missing[0].clone()); // Raw count alone cannot certify a table.
    let mut allowed = vec![0];
    allowed.extend((0..8).map(|i| 1 << i));
    allowed.extend((1..8).map(|i| 1 | (1 << i)));
    for original in [missing, relation([1, 2, 3, 4, 5, 6, 7, 8], &allowed)] {
        let result = factor_relations(8, &original, Limits::default()).expect("unchanged");
        assert_eq!(result.groups(), 0);
        assert_eq!(result.clauses(), original);
        assert!(prefix(&result).is_empty());
    }
}

#[test]
fn duplicates_units_empty_and_tautologies_are_preserved_soundly() {
    let mut original = table();
    original.push(original[0].clone());
    let extras = vec![
        vec![1],
        vec![-2, 3],
        vec![1, 1, 2, 3, 4, 5, 6, 7],
        vec![1, -1, 2, 3, 4, 5, 6, 7],
    ];
    original.extend(extras.clone());
    let result = factor_relations(8, &original, Limits::default()).expect("factor");
    assert_eq!(&result.clauses()[..extras.len()], extras);
    equivalent(&original, &result, 8);
    check_prefix(&original, &result);
    original.push(vec![]);
    let result = factor_relations(8, &original, Limits::default()).expect("empty is retained");
    assert!(result.clauses().iter().any(Vec::is_empty));
    equivalent(&original, &result, 8);
}

#[test]
fn overlapping_relations_compose_without_model_reconstruction() {
    let mut original = table();
    original.extend(table().into_iter().map(|c| {
        c.into_iter()
            .map(|l| if l > 0 { l + 1 } else { l - 1 })
            .collect()
    }));
    let result = factor_relations(9, &original, Limits::default()).expect("factor overlap");
    assert_eq!(result.groups(), 2);
    equivalent(&original, &result, 9);
    check_prefix(&original, &result);
}

#[test]
fn limits_fail_atomically_and_do_not_modify_the_input() {
    let original = table();
    for limits in [
        Limits {
            clauses: 239,
            ..Limits::default()
        },
        Limits {
            literals: 1919,
            ..Limits::default()
        },
        Limits {
            groups: 0,
            ..Limits::default()
        },
        Limits {
            resolutions: 447,
            ..Limits::default()
        },
    ] {
        assert!(matches!(
            factor_relations(8, &original, limits),
            Err(FactorError::Limit)
        ));
        assert_eq!(original, table());
    }
    assert!(
        factor_relations(
            8,
            &original,
            Limits {
                clauses: 240,
                literals: 1920,
                groups: 1,
                resolutions: 448
            }
        )
        .is_ok()
    );
    for invalid in [0, 9, -9, i32::MIN] {
        assert_eq!(
            factor_relations(8, &[vec![invalid]], Limits::default()).err(),
            Some(FactorError::InvalidLiteral(invalid))
        );
    }
}

#[test]
fn writer_failure_is_reported() {
    struct Broken;
    impl Write for Broken {
        fn write(&mut self, _: &[u8]) -> io::Result<usize> {
            Err(io::Error::other("broken output"))
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }
    let result = factor_relations(8, &table(), Limits::default()).expect("factor");
    assert!(result.write_lrat_prefix(Broken).is_err());
}

#[test]
fn complete_solver_proof_composes_against_original_relation() {
    // Equality of the low/high nibbles contradicts x1=true and x5=false.
    // Put these units last: adding originals after root contradiction is not
    // supported by the SAT proof tracer. Factorization puts retained units
    // first; they alone are consistent, and all replacements enter the trace.
    let mut original = table();
    original.extend([vec![1], vec![-5]]);
    let result = factor_relations(8, &original, Limits::default()).expect("factor");
    let mut solver = crate::Solver::new();
    solver.ensure_vars(8);
    let handle = solver.enable_lrat_transcript();
    for c in result.clauses() {
        solver.add_clause_dimacs(c);
    }
    assert_eq!(solver.solve(), crate::SolverResult::Unsat);
    solver.flush_proof();
    let transcript = handle.snapshot().expect("complete transcript");
    assert_eq!(transcript.original_clauses, result.clauses());
    assert!(check_lrat_proof(result.clauses(), &transcript.proof).verified);
    let count = result.clauses().len() as i64;
    let remap = |id: i64| -> i64 {
        assert!(id > 0);
        if id <= count {
            result.clause_ids()[id as usize - 1]
        } else {
            result.last_proof_id() + id - count
        }
    };
    let mut joined = prefix(&result);
    for line in transcript.proof.lines() {
        let mut tokens: Vec<String> = line.split_whitespace().map(str::to_owned).collect();
        assert!(tokens.len() >= 3);
        let deletion = tokens[1] == "d";
        // Deletion-line leading IDs are cosmetic, unlike addition IDs.
        tokens[0] = if deletion {
            result.last_proof_id()
        } else {
            remap(tokens[0].parse().expect("ID"))
        }
        .to_string();
        let hint_start = if deletion {
            2
        } else {
            tokens
                .iter()
                .position(|t| t == "0")
                .expect("literal terminator")
                + 1
        };
        for token in &mut tokens[hint_start..] {
            let id: i64 = token.parse().expect("hint ID");
            assert!(id >= 0, "test uses pure RUP");
            if id != 0 {
                *token = remap(id).to_string();
            }
        }
        joined.push_str(&tokens.join(" "));
        joined.push('\n');
    }
    let report = check_lrat_proof(&original, &joined);
    assert!(report.verified, "{report:?}");
    assert!(report.additions_checked > result.resolutions());
}
