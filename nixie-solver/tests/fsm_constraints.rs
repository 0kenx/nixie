#![allow(clippy::unwrap_used)]

//! End-to-end tests for the FSM constraint integration
//! (`nixie_theories::fsm` + `Solver::register_fsm`).
//!
//! Oracle methodology:
//!
//! - **exhaustive differential vs. the reference interpreter**: for a
//!   family of small NFAs, every total guard assignment and both
//!   acceptance polarities, the solver's verdict (guards pinned, atom
//!   asserted) must equal the interpreter's answer, and every returned
//!   model must independently agree with the interpreter on the atom's
//!   value under the model's guard assignment;
//! - **an independent exact SAT encoding** (bounded epsilon-relaxation
//!   unrolling, structurally different from the product-graph reduction)
//!   must agree on satisfiability of `accepts = true` and `accepts =
//!   false` for free guards;
//! - synthesis scenarios from positive and negative word examples;
//! - scope lifecycle, Boolean combinations, and certification boundaries.
//!
//! Semantics reference: `docs/FSM.md`.

use nixie_core::ast::{TermId, TermManager};
use nixie_solver::{Solver, SolverResult};
use nixie_theories::fsm::{FsmModel, Label};

/// Read a Boolean variable's value from a returned model.
fn model_bool(solver: &Solver, term: TermId, tm: &TermManager) -> bool {
    let model = solver.model().expect("model must exist after sat");
    let value = *model
        .assignments()
        .get(&term)
        .unwrap_or_else(|| panic!("term {term:?} has no model assignment"));
    let true_term = tm.mk_bool(true);
    let false_term = tm.mk_bool(false);
    assert!(
        value == true_term || value == false_term,
        "term {term:?} has non-Boolean model value {value:?}"
    );
    value == true_term
}

/// Build `iff(a, b)` from the Boolean connectives.
fn mk_iff(tm: &mut TermManager, a: TermId, b: TermId) -> TermId {
    let not_a = tm.mk_not(a);
    let not_b = tm.mk_not(b);
    let clause1 = tm.mk_or([not_a, b]);
    let clause2 = tm.mk_or([a, not_b]);
    tm.mk_and([clause1, clause2])
}

/// One declarative NFA for the exhaustive battery.
struct FsmCase {
    states: usize,
    alphabet: usize,
    initial: usize,
    accepting: &'static [usize],
    /// (from, label, to, guard index); guards are fresh vars `g<k>`.
    transitions: Vec<(usize, Label, usize, usize)>,
    words: Vec<Vec<u32>>,
}

impl FsmCase {
    fn guard_count(&self) -> usize {
        self.transitions
            .iter()
            .map(|t| t.3)
            .max()
            .map_or(0, |m| m + 1)
    }

    fn build_model(
        &self,
        tm: &mut TermManager,
    ) -> (FsmModel, nixie_theories::fsm::AutomatonHandle, Vec<TermId>) {
        let guard_vars: Vec<TermId> = (0..self.guard_count())
            .map(|i| tm.mk_var(&format!("g{i}"), tm.sorts.bool_sort))
            .collect();
        let mut model = FsmModel::new(tm);
        let a = model.new_automaton(self.states, self.alphabet).unwrap();
        model.set_initial(a, self.initial).unwrap();
        for &q in self.accepting {
            model.add_accepting(a, q).unwrap();
        }
        for &(from, label, to, k) in &self.transitions {
            model
                .add_transition(a, from, to, label, guard_vars[k], tm)
                .unwrap();
        }
        (model, a, guard_vars)
    }
}

/// Exhaustive differential: every guard assignment × both polarities ×
/// every case word. The solver must agree with the interpreter exactly,
/// and every model must validate independently.
fn exhaustive_differential(case: &FsmCase) {
    let guard_count = case.guard_count();
    for word in &case.words {
        for mask in 0..(1usize << guard_count) {
            for &polarity in &[true, false] {
                let mut tm = TermManager::new();
                let (mut model, a, guard_vars) = case.build_model(&mut tm);
                let atom = model.accepts(a, word, &mut tm).unwrap();
                // A twin declaration for the independent interpreter (same
                // guard names, same interned terms).
                let (mut twin, a_twin, twin_guards) = case.build_model(&mut tm);
                let _ = twin.accepts(a_twin, word, &mut tm);
                let mut solver = Solver::new();
                solver.register_fsm(model, &mut tm).unwrap();
                for (k, &g) in guard_vars.iter().enumerate() {
                    let value = mask & (1 << k) != 0;
                    solver.assert(if value { g } else { tm.mk_not(g) }, &mut tm);
                }
                solver.assert(if polarity { atom } else { tm.mk_not(atom) }, &mut tm);
                let expected = {
                    let truth = |t: TermId| -> bool {
                        twin_guards
                            .iter()
                            .position(|&g| g == t)
                            .is_some_and(|k| mask & (1 << k) != 0)
                    };
                    twin.accepts_under(a_twin, word, &truth).unwrap()
                };
                let result = solver.check(&mut tm);
                assert_eq!(
                    result,
                    if expected == polarity {
                        SolverResult::Sat
                    } else {
                        SolverResult::Unsat
                    },
                    "guards={mask:0b} polarity={polarity} word={word:?} expected_interpreter={expected}"
                );
                if result == SolverResult::Sat {
                    // Independent model validation: the atom's value equals
                    // the interpreter's answer under the model's guards.
                    let model_guards: Vec<bool> = guard_vars
                        .iter()
                        .map(|&g| model_bool(&solver, g, &tm))
                        .collect();
                    let truth = |t: TermId| -> bool {
                        guard_vars
                            .iter()
                            .position(|&g| g == t)
                            .is_some_and(|k| model_guards[k])
                    };
                    let acceptance = twin.accepts_under(a_twin, word, &truth).unwrap();
                    let atom_value = model_bool(&solver, atom, &tm);
                    assert_eq!(
                        atom_value, acceptance,
                        "model atom value disagrees with interpreter (guards={model_guards:?})"
                    );
                }
            }
        }
    }
}

/// Chain with shared guard, skip edge, epsilon back-edge.
#[test]
fn differential_chain_skip_epsilon() {
    exhaustive_differential(&FsmCase {
        states: 3,
        alphabet: 2,
        initial: 0,
        accepting: &[2],
        transitions: vec![
            (0, Label::Symbol(0), 1, 0),
            (1, Label::Symbol(1), 2, 1),
            (0, Label::Symbol(0), 2, 0), // guard 0 shared
            (2, Label::Epsilon, 1, 2),
        ],
        words: vec![vec![], vec![0], vec![0, 1], vec![1], vec![0, 0]],
    });
}

/// Epsilon cycle, empty word, nondeterminism, multiple accepting states.
#[test]
fn differential_epsilon_cycles_and_multi_accepting() {
    exhaustive_differential(&FsmCase {
        states: 3,
        alphabet: 2,
        initial: 0,
        accepting: &[1, 2],
        transitions: vec![
            (0, Label::Epsilon, 1, 0),
            (1, Label::Epsilon, 0, 1),
            (0, Label::Symbol(0), 2, 2),
            (1, Label::Symbol(1), 1, 0),
            (1, Label::Symbol(1), 2, 2),
        ],
        words: vec![
            vec![],
            vec![0],
            vec![1],
            vec![1, 1],
            vec![1, 1, 1],
            vec![0, 1],
        ],
    });
}

/// Self-loops and parallel transitions.
#[test]
fn differential_self_loops_parallel() {
    exhaustive_differential(&FsmCase {
        states: 2,
        alphabet: 2,
        initial: 0,
        accepting: &[1],
        transitions: vec![
            (0, Label::Symbol(0), 1, 0),
            (0, Label::Symbol(0), 1, 1),
            (1, Label::Symbol(0), 1, 2),
            (1, Label::Symbol(1), 0, 0),
        ],
        words: vec![vec![], vec![0], vec![0, 0], vec![0, 0, 0], vec![1]],
    });
}

/// Independent exact SAT encoding: layered one-hot reachability with
/// bounded epsilon relaxation (`|Q|` unrolling steps — the closure
/// converges within `|Q|` monotone steps, and the layering makes the
/// biconditional system acyclic, so its fixpoint is unique and the
/// encoding is exact). Structurally unrelated to the product-graph
/// reduction.
#[allow(clippy::needless_range_loop)]
fn encode_and_check(
    case: &FsmCase,
    word: &[u32],
    polarity: bool,
    tm: &mut TermManager,
) -> SolverResult {
    let guard_vars: Vec<TermId> = (0..case.guard_count())
        .map(|i| tm.mk_var(&format!("g{i}"), tm.sorts.bool_sort))
        .collect();
    let states = case.states;
    let n = word.len();
    let mut solver = Solver::new();
    // R[p][q]: q enters layer p by a consuming step (or is the start).
    // E[i][p][q]: epsilon closure iteration i within layer p.
    let mut r = vec![vec![TermId::new(u32::MAX); states]; n + 1];
    let mut e = vec![vec![vec![TermId::new(u32::MAX); states]; n + 1]; states + 1];
    for p in 0..=n {
        for q in 0..states {
            r[p][q] = tm.mk_var(&format!("R{p}_{q}"), tm.sorts.bool_sort);
        }
        for q in 0..states {
            e[0][p][q] = tm.mk_var(&format!("E0_{p}_{q}"), tm.sorts.bool_sort);
        }
    }
    for i in 1..=states {
        for p in 0..=n {
            for q in 0..states {
                e[i][p][q] = tm.mk_var(&format!("E{i}_{p}_{q}"), tm.sorts.bool_sort);
            }
        }
    }
    // Start configuration.
    solver.assert(r[0][case.initial], tm);
    for q in 0..states {
        if q != case.initial {
            let not_r = tm.mk_not(r[0][q]);
            solver.assert(not_r, tm);
        }
    }
    // Consuming steps: R[p+1][q] ⟺ ∨ consuming transitions into q at p.
    for p in 0..n {
        for q in 0..states {
            let incoming: Vec<TermId> = case
                .transitions
                .iter()
                .filter(|&&(from, label, to, _)| {
                    to == q && label == Label::Symbol(word[p]) && from != usize::MAX
                })
                .map(|&(from, _, _, k)| tm.mk_and([e[states][p][from], guard_vars[k]]))
                .collect();
            let rhs = tm.mk_or(incoming);
            solver.assert(mk_iff(tm, r[p + 1][q], rhs), tm);
        }
    }
    // Epsilon relaxation: E[0][p][q] ⟺ R[p][q];
    // E[i+1][p][q] ⟺ E[i][p][q] ∨ ∨ eps transitions into q from any
    // E[i]-reached state.
    for p in 0..=n {
        for q in 0..states {
            solver.assert(mk_iff(tm, e[0][p][q], r[p][q]), tm);
            for i in 0..states {
                let incoming: Vec<TermId> = case
                    .transitions
                    .iter()
                    .filter(|&&(from, label, to, _)| {
                        to == q && label == Label::Epsilon && from != usize::MAX
                    })
                    .map(|&(from, _, _, k)| tm.mk_and([e[i][p][from], guard_vars[k]]))
                    .collect();
                let mut terms = vec![e[i][p][q]];
                terms.extend(incoming);
                let rhs = tm.mk_or(terms);
                solver.assert(mk_iff(tm, e[i + 1][p][q], rhs), tm);
            }
        }
    }
    // Acceptance: ∨ over accepting states of E[|Q|][n][qf].
    let finals: Vec<TermId> = case.accepting.iter().map(|&qf| e[states][n][qf]).collect();
    let acceptance = tm.mk_or(finals);
    solver.assert(
        if polarity {
            acceptance
        } else {
            tm.mk_not(acceptance)
        },
        tm,
    );
    solver.check(tm)
}

/// The FSM integration and the independent SAT encoding must agree on the
/// satisfiability of "accepts" and "rejects" for free guards.
#[test]
fn independent_sat_encoding_agrees() {
    let cases: Vec<FsmCase> = vec![
        FsmCase {
            states: 3,
            alphabet: 2,
            initial: 0,
            accepting: &[2],
            transitions: vec![
                (0, Label::Symbol(0), 1, 0),
                (1, Label::Symbol(1), 2, 1),
                (0, Label::Symbol(0), 2, 0),
                (2, Label::Epsilon, 1, 2),
            ],
            words: vec![
                vec![],
                vec![0],
                vec![0, 1],
                vec![1],
                vec![0, 0],
                vec![0, 1, 1],
            ],
        },
        FsmCase {
            states: 3,
            alphabet: 2,
            initial: 0,
            accepting: &[1, 2],
            transitions: vec![
                (0, Label::Epsilon, 1, 0),
                (1, Label::Epsilon, 0, 1),
                (0, Label::Symbol(0), 2, 2),
                (1, Label::Symbol(1), 1, 0),
                (1, Label::Symbol(1), 2, 2),
            ],
            words: vec![vec![], vec![0], vec![1], vec![1, 1], vec![1, 1, 1]],
        },
    ];
    for case in &cases {
        for word in &case.words {
            for &polarity in &[true, false] {
                let mut tm = TermManager::new();
                let (mut model, a, _guards) = case.build_model(&mut tm);
                let atom = model.accepts(a, word, &mut tm).unwrap();
                let mut solver = Solver::new();
                solver.register_fsm(model, &mut tm).unwrap();
                solver.assert(if polarity { atom } else { tm.mk_not(atom) }, &mut tm);
                let via_fsm = solver.check(&mut tm);
                let mut tm2 = TermManager::new();
                let via_encoding = encode_and_check(case, word, polarity, &mut tm2);
                assert_eq!(
                    via_fsm, via_encoding,
                    "FSM integration and independent encoding disagree (word={word:?}, polarity={polarity})"
                );
            }
        }
    }
}

/// Synthesis from positive and negative examples: a 3-state automaton over
/// {0,1} whose guards must make "010" accepted and "10"/"" rejected.
/// The found automaton is validated against the interpreter on the
/// examples. Contradictory requirements are unsat.
#[test]
fn synthesis_from_positive_and_negative_examples() {
    let mut tm = TermManager::new();
    let mut model = FsmModel::new(&tm);
    let a = model.new_automaton(3, 2).unwrap();
    model.set_initial(a, 0).unwrap();
    model.add_accepting(a, 2).unwrap();
    // Candidate transitions with symbolic guards: from every state on
    // every symbol, either STAY or MOVE to the next state (mod 3) — the
    // guard chooses. This is nondeterministic, so word acceptance depends
    // on the guard assignment: "010" can end at 2 (move,stay,move).
    let mut stay = vec![vec![TermId::new(u32::MAX); 2]; 3];
    let mut mov = vec![vec![TermId::new(u32::MAX); 2]; 3];
    for q in 0..3 {
        for s in 0..2 {
            let gs = tm.mk_var(&format!("stay{q}_{s}"), tm.sorts.bool_sort);
            let gm = tm.mk_var(&format!("move{q}_{s}"), tm.sorts.bool_sort);
            model
                .add_transition(a, q, q, Label::Symbol(s as u32), gs, &mut tm)
                .unwrap();
            model
                .add_transition(a, q, (q + 1) % 3, Label::Symbol(s as u32), gm, &mut tm)
                .unwrap();
            stay[q][s] = gs;
            mov[q][s] = gm;
        }
    }
    let pos_010 = model.accepts(a, &[0, 1, 0], &mut tm).unwrap();
    let neg_10 = model.accepts(a, &[1, 0], &mut tm).unwrap();
    let neg_empty = model.accepts(a, &[], &mut tm).unwrap();
    let mut solver = Solver::new();
    solver.register_fsm(model, &mut tm).unwrap();
    solver.assert(pos_010, &mut tm);
    solver.assert(tm.mk_not(neg_10), &mut tm);
    solver.assert(tm.mk_not(neg_empty), &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    // Read out the synthesized automaton (guard grid by name).
    let grid: Vec<Vec<(TermId, TermId)>> = (0..3)
        .map(|q| {
            (0..2)
                .map(|s| {
                    (
                        tm.mk_var(&format!("stay{q}_{s}"), tm.sorts.bool_sort),
                        tm.mk_var(&format!("move{q}_{s}"), tm.sorts.bool_sort),
                    )
                })
                .collect()
        })
        .collect();
    let vals: Vec<Vec<(bool, bool)>> = (0..3)
        .map(|q| {
            (0..2)
                .map(|s| {
                    let (gs, gm) = grid[q][s];
                    (model_bool(&solver, gs, &tm), model_bool(&solver, gm, &tm))
                })
                .collect()
        })
        .collect();
    // Validate independently: rebuild a twin declaration (same guard
    // names intern to the same terms) and evaluate with the interpreter.
    let mut tm2 = TermManager::new();
    let mut model2 = FsmModel::new(&tm2);
    let a2 = model2.new_automaton(3, 2).unwrap();
    model2.set_initial(a2, 0).unwrap();
    model2.add_accepting(a2, 2).unwrap();
    for q in 0..3 {
        for s in 0..2 {
            let gs = tm2.mk_var(&format!("stay{q}_{s}"), tm2.sorts.bool_sort);
            let gm = tm2.mk_var(&format!("move{q}_{s}"), tm2.sorts.bool_sort);
            model2
                .add_transition(a2, q, q, Label::Symbol(s as u32), gs, &mut tm2)
                .unwrap();
            model2
                .add_transition(a2, q, (q + 1) % 3, Label::Symbol(s as u32), gm, &mut tm2)
                .unwrap();
        }
    }
    let twin_grid: Vec<Vec<(TermId, TermId)>> = (0..3)
        .map(|q| {
            (0..2)
                .map(|s| {
                    (
                        tm2.mk_var(&format!("stay{q}_{s}"), tm2.sorts.bool_sort),
                        tm2.mk_var(&format!("move{q}_{s}"), tm2.sorts.bool_sort),
                    )
                })
                .collect()
        })
        .collect();
    let truth = |t: TermId| -> bool {
        for q in 0..3 {
            for s in 0..2 {
                let (gs, gm) = twin_grid[q][s];
                if t == gs {
                    return vals[q][s].0;
                }
                if t == gm {
                    return vals[q][s].1;
                }
            }
        }
        false
    };
    assert!(
        model2.accepts_under(a2, &[0, 1, 0], &truth).unwrap(),
        "synthesized automaton must accept the positive example"
    );
    assert!(
        !model2.accepts_under(a2, &[1, 0], &truth).unwrap(),
        "synthesized automaton must reject the negative example"
    );
    assert!(!model2.accepts_under(a2, &[], &truth).unwrap());
    // Contradictory requirements: accept and reject one word.
    let atom = model2.accepts(a2, &[1, 0], &mut tm2).unwrap();
    let mut solver2 = Solver::new();
    solver2.register_fsm(model2, &mut tm2).unwrap();
    solver2.assert(atom, &mut tm2);
    solver2.assert(tm2.mk_not(atom), &mut tm2);
    assert_eq!(solver2.check(&mut tm2), SolverResult::Unsat);
}

/// Structural unsatisfiability: the word is longer than any consuming
/// path, so acceptance is impossible regardless of guards.
#[test]
fn unsat_when_word_too_long() {
    let mut tm = TermManager::new();
    let mut model = FsmModel::new(&tm);
    let a = model.new_automaton(2, 1).unwrap();
    model.set_initial(a, 0).unwrap();
    model.add_accepting(a, 1).unwrap();
    let g = tm.mk_var("t", tm.sorts.bool_sort);
    model
        .add_transition(a, 0, 1, Label::Symbol(0), g, &mut tm)
        .unwrap();
    let atom = model.accepts(a, &[0, 0], &mut tm).unwrap();
    let mut solver = Solver::new();
    solver.register_fsm(model, &mut tm).unwrap();
    solver.assert(atom, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
}

/// Boolean combinations of acceptance atoms, negation, and interaction
/// with linear arithmetic (guards as arithmetic comparisons). Push/pop
/// retractions restore satisfiability.
#[test]
fn boolean_combinations_and_arithmetic_guards() {
    let mut tm = TermManager::new();
    let mut model = FsmModel::new(&tm);
    let a = model.new_automaton(3, 2).unwrap();
    model.set_initial(a, 0).unwrap();
    model.add_accepting(a, 2).unwrap();
    // Guards are arithmetic comparisons over one integer: contradictory
    // on every model.
    let x = tm.mk_var("x", tm.sorts.int_sort);
    let five = tm.mk_int(5);
    let g_le = tm.mk_le(x, five);
    let le = tm.mk_le(x, five);
    let g_gt = tm.mk_not(le);
    model
        .add_transition(a, 0, 1, Label::Symbol(0), g_le, &mut tm)
        .unwrap();
    model
        .add_transition(a, 1, 2, Label::Symbol(1), g_gt, &mut tm)
        .unwrap();
    let accepts01 = model.accepts(a, &[0, 1], &mut tm).unwrap();
    let accepts0 = model.accepts(a, &[0], &mut tm).unwrap();
    let accepts_empty = model.accepts(a, &[], &mut tm).unwrap();
    let mut solver = Solver::new();
    solver.register_fsm(model, &mut tm).unwrap();
    // "01" requires x ≤ 5 ∧ x > 5 — impossible, so accepting it is unsat
    // no matter what; rejecting "0" and "" adds consistent demands.
    solver.push();
    solver.assert(accepts01, &mut tm);
    solver.assert(tm.mk_not(accepts0), &mut tm);
    solver.assert(tm.mk_not(accepts_empty), &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
    solver.pop();
    // Without the contradictory acceptance demand: satisfiable.
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    // Requiring rejection of "0" (x ≤ 5 must not enable the step, i.e.
    // x > 5) and acceptance of "" is impossible — state 2 is unreachable
    // in zero steps, so both cannot hold... "" is rejected anyway; the
    // interesting consistent demand is ¬accepts("0") alone.
    solver.assert(tm.mk_not(accepts0), &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
}

/// Push/pop lifecycle: repeated checks, scope retraction, and stale-model
/// invalidation across scope changes.
#[test]
fn push_pop_lifecycle() {
    let mut tm = TermManager::new();
    let mut model = FsmModel::new(&tm);
    let a = model.new_automaton(2, 1).unwrap();
    model.set_initial(a, 0).unwrap();
    model.add_accepting(a, 1).unwrap();
    let g = tm.mk_var("t", tm.sorts.bool_sort);
    model
        .add_transition(a, 0, 1, Label::Symbol(0), g, &mut tm)
        .unwrap();
    let accepts0 = model.accepts(a, &[0], &mut tm).unwrap();
    let accepts00 = model.accepts(a, &[0, 0], &mut tm).unwrap();
    let mut solver = Solver::new();
    solver.register_fsm(model, &mut tm).unwrap();

    // Demand acceptance of "0" and rejection of "00": needs t true.
    solver.assert(accepts0, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    solver.push();
    solver.assert(tm.mk_not(accepts00), &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    // Contradiction under the scope: "0" rejected too.
    solver.push();
    solver.assert(tm.mk_not(accepts0), &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
    solver.pop();
    // Back to satisfiable.
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    solver.pop();
    // Root: acceptance of "0" alone, still satisfiable after retraction.
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
    // Asserting ¬accepts("0") at root contradicts the earlier root-level
    // accepts("0") — unsat, and it stays unsat (root assertions are
    // permanent until reset).
    solver.assert(tm.mk_not(accepts0), &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
}

/// Certification and proof boundaries: registered FSM constraints are
/// unproved client callbacks; certified checks must fail closed to
/// Unknown.
#[test]
fn certified_mode_fails_closed() {
    let mut tm = TermManager::new();
    let mut model = FsmModel::new(&tm);
    let a = model.new_automaton(2, 1).unwrap();
    model.set_initial(a, 0).unwrap();
    model.add_accepting(a, 1).unwrap();
    let g = tm.mk_var("t", tm.sorts.bool_sort);
    model
        .add_transition(a, 0, 1, Label::Symbol(0), g, &mut tm)
        .unwrap();
    let atom = model.accepts(a, &[0], &mut tm).unwrap();
    let mut certified = Solver::with_config(nixie_solver::SolverConfig::default().certified());
    certified.register_fsm(model, &mut tm).unwrap();
    certified.assert(atom, &mut tm);
    assert_eq!(
        certified.check(&mut tm),
        SolverResult::Unknown,
        "certified mode must fail closed for FSM callbacks"
    );
}
