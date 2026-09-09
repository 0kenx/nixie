//! Explicit in-memory route through the existing checked transformer.

use super::relation_input::parse;
use nixie_sat::relation_factor::{FactorError, Limits, factor_relations};
use nixie_sat::{LBool, Lit, Solver};
use std::io::BufRead;

pub fn load_file(
    path: impl AsRef<std::path::Path>,
    solver: &mut Solver,
) -> Result<PreparedInput, Box<dyn std::error::Error>> {
    load(
        std::io::BufReader::new(std::fs::File::open(path)?),
        solver,
        Limits::default(),
    )
}

pub struct PreparedInput {
    original: Vec<Vec<i32>>,
    pub groups: usize,
    pub fallback: bool,
    pub clauses: usize,
    pub literals: usize,
}

impl PreparedInput {
    pub fn original_clauses(&self) -> usize {
        self.original.len()
    }

    /// A partial model suffices only when every original clause already has
    /// a concretely true literal. Missing/undefined values cannot justify SAT.
    pub fn verify_model(&self, model: &[LBool]) -> Result<(), String> {
        for (index, clause) in self.original.iter().enumerate() {
            let satisfied = clause.iter().any(|&lit| {
                let value = model.get(lit.unsigned_abs() as usize - 1);
                matches!(
                    (value, lit > 0),
                    (Some(LBool::True), true) | (Some(LBool::False), false)
                )
            });
            if !satisfied {
                return Err(format!(
                    "SAT model does not satisfy original clause {}",
                    index + 1
                ));
            }
        }
        Ok(())
    }
}

/// Parse and finish certification before inserting any clause into the solver.
/// The example calls this only on its fresh, proof-free solver. A limit refusal
/// loads the untouched original; certificate and parse errors are propagated.
pub fn load(
    reader: impl BufRead,
    solver: &mut Solver,
    limits: Limits,
) -> Result<PreparedInput, Box<dyn std::error::Error>> {
    let (vars, original) = parse(reader)?;
    let factored = match factor_relations(vars, &original, limits) {
        Ok(result) => Some(result),
        Err(FactorError::Limit) => None,
        Err(error) => return Err(error.into()),
    };
    let clauses = factored
        .as_ref()
        .map_or(original.as_slice(), |result| result.clauses());
    let groups = factored.as_ref().map_or(0, |result| result.groups());
    let output_clauses = clauses.len();
    let output_literals = clauses.iter().map(Vec::len).sum();
    // Match the DIMACS parser's insertion protocol and literal order, including
    // its reserve bound, root units, empty clauses and deferred binary edges.
    solver.begin_deferred_big();
    solver.ensure_vars(vars);
    if !clauses.is_empty() {
        solver.reserve_clause_slots(clauses.len());
    }
    for clause in clauses {
        solver.add_clause(clause.iter().copied().map(Lit::from_dimacs));
    }
    solver.finish_deferred_big();
    let fallback = factored.is_none();
    // The complete resolution certificate is constructed/checked as before.
    // Drop its scratch storage before search; no proof files are requested by
    // this mode. The original clauses remain available for model verification.
    drop(factored);
    Ok(PreparedInput {
        original,
        groups,
        fallback,
        clauses: output_clauses,
        literals: output_literals,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use nixie_sat::{ConfigPreset, DimacsParser, SolverResult};
    use std::io::Cursor;

    fn encode(vars: usize, clauses: &[Vec<i32>]) -> String {
        use std::fmt::Write;
        let mut output = format!("p cnf {vars} {}\n", clauses.len());
        for clause in clauses {
            for lit in clause {
                write!(output, "{lit} ").expect("string write");
            }
            output.push_str("0\n");
        }
        output
    }

    fn identity_relation() -> Vec<Vec<i32>> {
        (0..256)
            .filter(|row| row & 15 != row >> 4)
            .map(|row| {
                (0..8)
                    .map(|index| {
                        let variable = index + 1;
                        if row & (1 << index) == 0 {
                            variable
                        } else {
                            -variable
                        }
                    })
                    .collect()
            })
            .collect()
    }

    fn compare(vars: usize, original: Vec<Vec<i32>>, limits: Limits, expected: SolverResult) {
        let input = encode(vars, &original);
        let factored = match factor_relations(vars, &original, limits) {
            Ok(result) => Some(result),
            Err(FactorError::Limit) => None,
            Err(error) => panic!("unexpected certificate failure: {error}"),
        };
        let clauses = factored
            .as_ref()
            .map_or(original.as_slice(), |result| result.clauses());
        let serialized = encode(vars, clauses);
        let mut direct = Solver::with_config(ConfigPreset::CaDiCaL.config());
        let mut roundtrip = Solver::with_config(ConfigPreset::CaDiCaL.config());
        direct.set_random_seed(1);
        roundtrip.set_random_seed(1);
        let prepared = load(Cursor::new(input), &mut direct, limits).expect("valid source");
        DimacsParser::new()
            .parse_reader(Cursor::new(serialized), &mut roundtrip)
            .expect("valid transformed DIMACS");
        assert_eq!(prepared.clauses, clauses.len());
        assert_eq!(prepared.original_clauses(), original.len());
        assert_eq!(prepared.fallback, factored.is_none());
        assert_eq!(direct.big_edge_count(), roundtrip.big_edge_count());
        assert_eq!(direct.solve(), expected);
        assert_eq!(roundtrip.solve(), expected);
        assert_eq!(
            format!("{:?}", direct.stats()),
            format!("{:?}", roundtrip.stats())
        );
        assert_eq!(direct.model(), roundtrip.model());
        if expected == SolverResult::Sat {
            prepared
                .verify_model(direct.model())
                .expect("original model");
        }
    }

    #[test]
    fn direct_loading_matches_factored_dimacs_for_sat_and_unsat() {
        let mut clauses = identity_relation();
        clauses.extend([vec![1], vec![-2], vec![3, -3], vec![1, 6], vec![1, 6]]);
        compare(8, clauses.clone(), Limits::default(), SolverResult::Sat);
        clauses.push(vec![-5]);
        compare(8, clauses, Limits::default(), SolverResult::Unsat);
    }

    #[test]
    fn no_group_and_limit_refusal_preserve_original_loading() {
        compare(
            3,
            vec![vec![-1, 2], vec![-2, 3], vec![-1, 2], vec![1]],
            Limits::default(),
            SolverResult::Sat,
        );
        compare(0, vec![vec![]], Limits::default(), SolverResult::Unsat);
        let mut clauses = identity_relation();
        clauses.push(vec![1]);
        compare(
            8,
            clauses,
            Limits {
                groups: 0,
                ..Limits::default()
            },
            SolverResult::Sat,
        );
    }

    #[test]
    fn invalid_source_is_rejected_before_solver_mutation() {
        for source in ["p cnf 1 1\n2 0\n", "p cnf 1 1\n1\n", "p cnf 1 1\n%\n"] {
            let mut solver = Solver::new();
            assert!(load(Cursor::new(source), &mut solver, Limits::default()).is_err());
            assert_eq!(solver.num_vars(), 0);
            assert_eq!(solver.num_original_clauses(), 0);
        }
    }

    #[test]
    fn model_validation_requires_original_clauses_to_be_concretely_true() {
        let mut solver = Solver::new();
        let prepared = load(
            Cursor::new("p cnf 2 2\n1 2 0\n-1 2 0\n"),
            &mut solver,
            Limits::default(),
        )
        .expect("source");
        assert!(prepared.verify_model(&[]).is_err());
        assert!(
            prepared
                .verify_model(&[LBool::Undef, LBool::Undef])
                .is_err()
        );
        assert!(prepared.verify_model(&[LBool::True, LBool::False]).is_err());
        assert!(prepared.verify_model(&[LBool::Undef, LBool::True]).is_ok());
        assert!(prepared.verify_model(&[LBool::False, LBool::True]).is_ok());
    }
}
