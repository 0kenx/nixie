//! Generated CP semantics and explanation checks using a concrete exhaustive oracle.
#![allow(clippy::unwrap_used)]

#[path = "cp_oracle/spec.rs"]
mod spec;

use nixie_core::ast::{TermId, TermManager};
use nixie_solver::{Solver, SolverResult};
use nixie_theories::cp::{CpModel, Task, Transition};
use nixie_theories::user_propagator::{Consequence, PropagatorResult, UserPropagatorManager};
use spec::{Case, Rng, Rule};
use std::collections::BTreeMap;

type Facts = BTreeMap<TermId, bool>;

struct Encoding {
    cp: CpModel,
    atoms: Vec<Vec<TermId>>,
    // Both polarities map to their variable, value index, and sign.
    literals: BTreeMap<TermId, (usize, usize, bool)>,
}

fn encode(case: &Case, tm: &mut TermManager) -> Encoding {
    let mut cp = CpModel::new(tm);
    let mut vars = Vec::new();
    let mut atoms = Vec::new();
    let mut literals = BTreeMap::new();
    for (v, domain) in case.domains.iter().enumerate() {
        let row: Vec<_> = domain
            .iter()
            .enumerate()
            .map(|(i, _)| {
                let atom = tm.mk_var(&format!("cp_{v}_{i}"), tm.sorts.bool_sort);
                literals.insert(atom, (v, i, true));
                literals.insert(tm.mk_not(atom), (v, i, false));
                atom
            })
            .collect();
        vars.push(
            cp.variable(
                domain.iter().cloned().zip(row.iter().copied()).collect(),
                tm,
            )
            .unwrap(),
        );
        atoms.push(row);
    }
    for rule in &case.rules {
        match rule {
            Rule::Distinct(vs) => cp
                .alldifferent(vs.iter().map(|&v| vars[v]).collect())
                .unwrap(),
            Rule::Allowed(vs, rows) => cp
                .table(vs.iter().map(|&v| vars[v]).collect(), rows.clone())
                .unwrap(),
            Rule::Word {
                vars: vs,
                initial,
                accepting,
                edges,
            } => cp
                .regular(
                    vs.iter().map(|&v| vars[v]).collect(),
                    *initial,
                    accepting.clone(),
                    edges
                        .iter()
                        .map(|(source, symbol, destination)| Transition {
                            source: *source,
                            symbol: symbol.clone(),
                            destination: *destination,
                        })
                        .collect(),
                )
                .unwrap(),
            Rule::Tour(vs) => cp.circuit(vs.iter().map(|&v| vars[v]).collect()).unwrap(),
            Rule::Resource { tasks, capacity } => cp
                .cumulative(
                    tasks
                        .iter()
                        .map(|(v, duration, demand)| Task {
                            start: vars[*v],
                            duration: duration.clone(),
                            demand: demand.clone(),
                        })
                        .collect(),
                    capacity.clone(),
                )
                .unwrap(),
        }
    }
    Encoding {
        cp,
        atoms,
        literals,
    }
}

struct Oracle<'a> {
    case: &'a Case,
    atoms: Vec<Vec<TermId>>,
    literals: BTreeMap<TermId, (usize, usize, bool)>,
    solutions: Vec<Vec<usize>>,
    true_term: TermId,
    false_term: TermId,
}

impl Oracle<'_> {
    fn truth(&self, literal: TermId, assignment: &[usize]) -> bool {
        if literal == self.true_term {
            return true;
        }
        if literal == self.false_term {
            return false;
        }
        let &(v, i, positive) = self.literals.get(&literal).unwrap();
        (assignment[v] == i) == positive
    }

    fn current_truth(&self, literal: TermId, facts: &Facts) -> Option<bool> {
        if literal == self.true_term {
            return Some(true);
        }
        if literal == self.false_term {
            return Some(false);
        }
        let &(v, i, positive) = self.literals.get(&literal).unwrap();
        facts.get(&self.atoms[v][i]).map(|&value| value == positive)
    }

    fn compatible(&self, assignment: &[usize], facts: &Facts) -> bool {
        facts
            .iter()
            .all(|(&atom, &value)| self.truth(atom, assignment) == value)
    }

    fn possible(&self, facts: &Facts) -> bool {
        self.solutions.iter().any(|row| self.compatible(row, facts))
    }

    fn consequence(&self, consequence: &Consequence, facts: &Facts) {
        assert!(
            consequence.term == self.true_term
                || consequence.term == self.false_term
                || self.literals.contains_key(&consequence.term),
            "unknown consequence: {:?}",
            self.case
        );
        for &reason in &consequence.justification {
            assert_eq!(
                self.current_truth(reason, facts),
                Some(true),
                "inactive/false reason {reason:?}: {:?}",
                self.case
            );
        }
        // Check ALL base solutions, not merely those satisfying the current
        // context: a missing antecedent must not be hidden by that context.
        for row in &self.solutions {
            if consequence
                .justification
                .iter()
                .all(|&r| self.truth(r, row))
            {
                assert!(
                    self.truth(consequence.term, row),
                    "invalid implication {consequence:?}, witness={row:?}, case={:?}",
                    self.case
                );
            }
        }
    }
}

#[derive(Default, Debug)]
struct Counts {
    cases: usize,
    assignments: usize,
    states: usize,
    consequences: usize,
    conflicts: usize,
    satisfiable_cases: [usize; 6],
    infeasible_cases: [usize; 6],
}

fn inspect(
    manager: &mut UserPropagatorManager,
    oracle: &Oracle<'_>,
    facts: &Facts,
    counts: &mut Counts,
    complete: bool,
    expected: bool,
) {
    let result = manager.final_check();
    let mut consequences = manager.get_consequences();
    match &result {
        PropagatorResult::Sat => assert!(
            oracle.possible(facts),
            "false satisfiable context: {:?}",
            oracle.case
        ),
        PropagatorResult::Unsat(reasons) => {
            counts.conflicts += 1;
            consequences.push(Consequence::new(oracle.false_term, reasons.clone()));
            assert!(!oracle.possible(facts), "false conflict: {:?}", oracle.case);
        }
        PropagatorResult::Unknown => {}
    }
    if complete {
        assert_eq!(
            result == PropagatorResult::Sat,
            expected,
            "{:?}",
            oracle.case
        );
        assert!(
            !matches!(result, PropagatorResult::Unknown),
            "incomplete on a complete assignment: {:?}",
            oracle.case
        );
    }
    for consequence in &consequences {
        oracle.consequence(consequence, facts);
    }
    counts.states += 1;
    counts.consequences += consequences.len();
}

#[test]
fn generated_explanations_and_scope_replay_match_exhaustive_oracle() {
    let mut counts = Counts::default();
    for case in spec::cases() {
        let mut tm = TermManager::new();
        let Encoding {
            cp,
            atoms,
            literals,
        } = encode(&case, &mut tm);
        let assignments = case.assignments();
        let solutions = assignments
            .iter()
            .filter(|r| case.accepts(r))
            .cloned()
            .collect();
        let oracle = Oracle {
            case: &case,
            atoms,
            literals,
            solutions,
            true_term: tm.mk_true(),
            false_term: tm.mk_false(),
        };
        let (_, watches, propagator) = cp.into_propagator();
        let mut manager = UserPropagatorManager::new();
        manager.register_propagator(propagator);
        for &atom in &watches {
            manager.watch_term(atom);
        }
        counts.cases += 1;
        if oracle.solutions.is_empty() {
            counts.infeasible_cases[case.family] += 1;
        } else {
            counts.satisfiable_cases[case.family] += 1;
        }
        let empty = Facts::new();
        inspect(&mut manager, &oracle, &empty, &mut counts, false, false);

        for assignment in &assignments {
            manager.push();
            let mut facts = Facts::new();
            for (v, row) in oracle.atoms.iter().enumerate() {
                for (i, &atom) in row.iter().enumerate() {
                    let value = assignment[v] == i;
                    facts.insert(atom, value);
                    manager.notify_fixed(atom, tm.mk_bool(value));
                }
            }
            inspect(
                &mut manager,
                &oracle,
                &facts,
                &mut counts,
                true,
                case.accepts(assignment),
            );
            manager.pop(1);
            counts.assignments += 1;
        }
        // Nested branches include both positive fixations and negative value
        // deletions. After each pop, inspect the restored parent independently.
        let mut rng = Rng::new(case.seed ^ (case.family as u64 * 1009) ^ 0xbac7_7aac);
        for _ in 0..16 {
            manager.push();
            let mut parent = Facts::new();
            for &atom in &watches {
                if rng.pick(4) == 0 {
                    let value = rng.pick(2) == 0;
                    parent.insert(atom, value);
                    manager.notify_fixed(atom, tm.mk_bool(value));
                    inspect(&mut manager, &oracle, &parent, &mut counts, false, false);
                }
            }
            for _ in 0..2 {
                manager.push();
                let mut branch = parent.clone();
                for &atom in &watches {
                    if !branch.contains_key(&atom) && rng.pick(3) == 0 {
                        let value = rng.pick(2) == 0;
                        branch.insert(atom, value);
                        manager.notify_fixed(atom, tm.mk_bool(value));
                        inspect(&mut manager, &oracle, &branch, &mut counts, false, false);
                    }
                }
                manager.pop(1);
                inspect(&mut manager, &oracle, &parent, &mut counts, false, false);
            }
            manager.pop(1);
            inspect(&mut manager, &oracle, &empty, &mut counts, false, false);
        }
    }
    assert_eq!(counts.cases, 244);
    assert!(counts.satisfiable_cases.iter().all(|&n| n > 0));
    assert!(counts.infeasible_cases.iter().all(|&n| n > 0));
    assert!(counts.assignments > 1000 && counts.consequences > 1000 && counts.conflicts > 1000);
    eprintln!("CP exhaustive explanation coverage: {counts:?}");
}

fn check_solver(solver: &mut Solver, tm: &mut TermManager, oracle: &Oracle<'_>, facts: &Facts) {
    let expected = if oracle.possible(facts) {
        SolverResult::Sat
    } else {
        SolverResult::Unsat
    };
    assert_eq!(
        solver.check(tm),
        expected,
        "facts={facts:?}, case={:?}",
        oracle.case
    );
    if expected == SolverResult::Sat {
        let model = solver.model().unwrap();
        let mut selected = Vec::new();
        for row in &oracle.atoms {
            let values: Vec<_> = row
                .iter()
                .enumerate()
                .filter_map(|(i, &atom)| match model.get(atom) {
                    Some(value) if value == oracle.true_term => Some(i),
                    Some(value) if value == oracle.false_term => None,
                    other => panic!(
                        "missing Boolean indicator {atom:?}: {other:?}; {:?}",
                        oracle.case
                    ),
                })
                .collect();
            assert_eq!(
                values.len(),
                1,
                "model violates exactly-one: {:?}",
                oracle.case
            );
            selected.push(values[0]);
        }
        assert!(
            oracle.case.accepts(&selected),
            "invalid decoded model: {:?}",
            oracle.case
        );
        assert!(
            oracle.compatible(&selected, facts),
            "model violates assertions: {:?}",
            oracle.case
        );
    } else {
        assert!(solver.model().is_none());
    }
}

#[test]
fn generated_solver_verdicts_models_and_scopes_match_exhaustive_oracle() {
    let mut checks = 0;
    for case in spec::cases() {
        let mut tm = TermManager::new();
        let Encoding {
            cp,
            atoms,
            literals,
        } = encode(&case, &mut tm);
        let solutions = case
            .assignments()
            .into_iter()
            .filter(|r| case.accepts(r))
            .collect();
        let oracle = Oracle {
            case: &case,
            atoms,
            literals,
            solutions,
            true_term: tm.mk_true(),
            false_term: tm.mk_false(),
        };
        let mut solver = Solver::new();
        solver.register_cp(cp, &mut tm).unwrap();
        let empty = Facts::new();
        check_solver(&mut solver, &mut tm, &oracle, &empty);
        checks += 1;
        let watches: Vec<_> = oracle.atoms.iter().flatten().copied().collect();
        let mut rng = Rng::new(case.seed ^ (case.family as u64 * 1013) ^ 0x05a7_2026);
        for _ in 0..8 {
            solver.push();
            let mut facts = Facts::new();
            for &atom in &watches {
                if rng.pick(4) == 0 {
                    let value = rng.pick(2) == 0;
                    facts.insert(atom, value);
                    let literal = if value { atom } else { tm.mk_not(atom) };
                    solver.assert(literal, &mut tm);
                }
            }
            check_solver(&mut solver, &mut tm, &oracle, &facts);
            check_solver(&mut solver, &mut tm, &oracle, &facts);
            solver.pop();
            assert!(solver.model().is_none());
            check_solver(&mut solver, &mut tm, &oracle, &empty);
            checks += 3;
        }
    }
    assert_eq!(checks, 6100);
    eprintln!("CP generated solver checks: {checks}");
}

#[test]
#[should_panic(expected = "invalid implication")]
fn oracle_rejects_an_omitted_reason_even_when_context_hides_it() {
    let case = Case {
        family: 0,
        seed: 0,
        domains: vec![vec![0.into(), 1.into()]; 2],
        rules: vec![Rule::Distinct(vec![0, 1])],
    };
    let mut tm = TermManager::new();
    let Encoding {
        atoms, literals, ..
    } = encode(&case, &mut tm);
    let solutions = case
        .assignments()
        .into_iter()
        .filter(|r| case.accepts(r))
        .collect();
    let oracle = Oracle {
        case: &case,
        atoms,
        literals,
        solutions,
        true_term: tm.mk_true(),
        false_term: tm.mk_false(),
    };
    // x=0 really implies y!=0. Removing the reason is invalid even though
    // y!=0 is true in every solution of this particular current context.
    let facts = Facts::from([(oracle.atoms[0][0], true)]);
    let consequence = Consequence::new(tm.mk_not(oracle.atoms[1][0]), Vec::new());
    oracle.consequence(&consequence, &facts);
}
