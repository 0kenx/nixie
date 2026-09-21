#![allow(clippy::unwrap_used)]

//! Exhaustive small-NFA oracle tests for the FSM reduction.
//!
//! Three independent oracles, none of which shares machinery with the
//! product construction:
//!
//! - the **reference interpreter** (`FsmModel::accepts_under`: iterative
//!   `(state, position)` search, no graphs), for acceptance under total
//!   guard assignments;
//! - a test-local **per-target run oracle** (`run_exists`) checking runs
//!   that end at one *specific* state — the exact meaning of one product
//!   reach atom — used to validate every consequence the propagator emits
//!   over partial guard assignments against **all guard completions**;
//! - hand-computed structural cases for the corner semantics (empty word,
//!   epsilon cycles, parallel transitions, constant guards, ...).

use super::*;
use crate::user_propagator::UserPropagatorManager;

/// Tri-state for enumerating partial guard assignments.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Tri {
    Unfixed,
    T,
    F,
}

fn tri_vectors(k: usize) -> Vec<Vec<Tri>> {
    let mut out = vec![Vec::new()];
    for _ in 0..k {
        let mut next = Vec::new();
        for v in &out {
            for unit in [Tri::Unfixed, Tri::T, Tri::F] {
                let mut w = v.clone();
                w.push(unit);
                next.push(w);
            }
        }
        out = next;
    }
    out
}

/// Test-local run oracle: does some run consume `word` from the initial
/// state and end at exactly `target`, following only transitions whose
/// guards `truth` makes present? This is the meaning of the product reach
/// atom `reach((q0,0), (target, n))` — length-≥-1 paths — including the
/// `n = 0 ∧ target = q0` case, which requires an epsilon cycle through
/// the initial state (zero steps do not count).
fn run_exists(
    transitions: &[(u32, Label, u32, TermId, Option<bool>)],
    states: u32,
    initial: u32,
    word: &[u32],
    target: u32,
    truth: &dyn Fn(TermId) -> bool,
) -> bool {
    let n = word.len();
    let present = |t: &(u32, Label, u32, TermId, Option<bool>)| match t.4 {
        Some(v) => v,
        None => truth(t.3),
    };
    if n == 0 && target == initial {
        // Length-≥-1 requirement: an epsilon cycle through the initial
        // state — arriving back at `initial` via present epsilon edges.
        let mut visited = vec![false; states as usize];
        visited[initial as usize] = true;
        let mut queue = vec![initial];
        let mut head = 0;
        while let Some(&u) = queue.get(head) {
            head += 1;
            for t in transitions {
                if t.0 == u && t.1 == Label::Epsilon && present(t) {
                    if t.2 == initial {
                        return true;
                    }
                    if !visited[t.2 as usize] {
                        visited[t.2 as usize] = true;
                        queue.push(t.2);
                    }
                }
            }
        }
        return false;
    }
    // General case: (state, position) closure; answer is membership of
    // `(target, n)` (which differs from the start, so membership implies
    // at least one step).
    let mut seen = vec![vec![false; n + 1]; states as usize];
    let mut worklist = vec![(initial, 0u32)];
    seen[initial as usize][0] = true;
    let mut head = 0;
    while let Some(&(state, pos)) = worklist.get(head) {
        head += 1;
        for t in transitions {
            if t.0 != state || !present(t) {
                continue;
            }
            let next = match t.1 {
                Label::Symbol(s) => {
                    if pos as usize == n || word[pos as usize] != s {
                        continue;
                    }
                    pos + 1
                }
                Label::Epsilon => pos,
            };
            if !seen[t.2 as usize][next as usize] {
                if t.2 == target && next as usize == n {
                    return true;
                }
                seen[t.2 as usize][next as usize] = true;
                worklist.push((t.2, next));
            }
        }
    }
    false
}

/// One replayed acceptance query: `(word, acceptance atom, per-accepting
/// state reach atoms)`.
type Queries = Vec<(Vec<u32>, TermId, Vec<(u32, TermId)>)>;

/// A declarative test automaton; guard variables are fresh `g<k>` terms.
struct Case {
    states: usize,
    alphabet: usize,
    initial: usize,
    accepting: &'static [usize],
    /// `(from, label, to, guard selection)`; guards are variable indexes or
    /// Boolean constants.
    transitions: Vec<(usize, Label, usize, GuardSel)>,
    words: Vec<Vec<u32>>,
}

#[derive(Clone, Copy, Debug)]
enum GuardSel {
    Var(usize),
    ConstTrue,
    ConstFalse,
}

impl Case {
    fn guard_count(&self) -> usize {
        self.transitions
            .iter()
            .filter_map(|t| match t.3 {
                GuardSel::Var(k) => Some(k),
                _ => None,
            })
            .max()
            .map_or(0, |m| m + 1)
    }

    /// Build the model; guard variables are minted by name, so rebuilding
    /// yields the same `TermId`s (name interning) — each replay uses one
    /// freshly built model, like the graph harness.
    fn build(&self, tm: &mut TermManager) -> (FsmModel, AutomatonHandle, Vec<TermId>) {
        let guard_vars: Vec<TermId> = (0..self.guard_count())
            .map(|i| tm.mk_var(&format!("g{i}"), tm.sorts.bool_sort))
            .collect();
        let mut model = FsmModel::new(tm);
        let a = model.new_automaton(self.states, self.alphabet).unwrap();
        model.set_initial(a, self.initial).unwrap();
        for &q in self.accepting {
            model.add_accepting(a, q).unwrap();
        }
        for &(from, label, to, sel) in &self.transitions {
            let guard = match sel {
                GuardSel::Var(k) => guard_vars[k],
                GuardSel::ConstTrue => tm.mk_bool(true),
                GuardSel::ConstFalse => tm.mk_bool(false),
            };
            model.add_transition(a, from, to, label, guard, tm).unwrap();
        }
        (model, a, guard_vars)
    }

    /// Flat transition list in the oracle's shape.
    fn flat(
        &self,
        guard_vars: &[TermId],
        tm: &TermManager,
    ) -> Vec<(u32, Label, u32, TermId, Option<bool>)> {
        self.transitions
            .iter()
            .map(|&(from, label, to, sel)| {
                let (guard, constant) = match sel {
                    GuardSel::Var(k) => (guard_vars[k], None),
                    GuardSel::ConstTrue => (tm.mk_bool(true), Some(true)),
                    GuardSel::ConstFalse => (tm.mk_bool(false), Some(false)),
                };
                (from as u32, label, to as u32, guard, constant)
            })
            .collect()
    }
}

fn guard_truth_fn<'a>(
    guard_vars: &'a [TermId],
    present: &'a [bool],
) -> impl Fn(TermId) -> bool + 'a {
    move |t: TermId| {
        guard_vars
            .iter()
            .position(|&g| g == t)
            .is_some_and(|k| present[k])
    }
}

/// Exhaustively replay every partial guard assignment through the
/// propagator and validate every emitted consequence against **all guard
/// completions** with the per-target run oracle — the FSM-level analogue
/// of `graph::tests`' consequence contract (it assumes nothing about the
/// graph suite). Also cross-checks, for every completion, that the
/// interpreter's acceptance equals the disjunction of the per-target run
/// oracles — the semantic heart of the reduction.
fn check_case(case: &Case) {
    let guard_count = case.guard_count();
    for states in tri_vectors(guard_count) {
        let mut tm = TermManager::new();
        let (mut model, a, guard_vars) = case.build(&mut tm);
        let mut queries: Queries = Vec::new();
        for word in &case.words {
            let atom = model.accepts(a, word, &mut tm).unwrap();
            let reach_atoms = model
                .acceptance_reach_atoms(a, word)
                .unwrap()
                .into_iter()
                .map(|(qf, atom)| (qf as u32, atom))
                .collect();
            queries.push((word.clone(), atom, reach_atoms));
        }
        let flat = case.flat(&guard_vars, &tm);
        let reg = model.registration();

        // 1. The disjunction construction is exactly acceptance, per
        //    completion, for every query word (uses the model before it is
        //    consumed by `into_propagator`).
        for mask in 0..(1usize << guard_count) {
            let present: Vec<bool> = (0..guard_count).map(|i| mask & (1 << i) != 0).collect();
            let truth = guard_truth_fn(&guard_vars, &present);
            for (word, _, reach_atoms) in &queries {
                let interpreter = model.accepts_under(a, word, &truth).unwrap();
                let disjunction = reach_atoms.iter().any(|&(qf, _)| {
                    run_exists(
                        &flat,
                        case.states as u32,
                        case.initial as u32,
                        word,
                        qf,
                        &truth,
                    )
                }) || (word.is_empty() && case.accepting.contains(&case.initial));
                assert_eq!(
                    interpreter, disjunction,
                    "reduction disagrees with interpreter (word={word:?}, guards={present:?})"
                );
            }
        }

        let (propagator, watches) = model.into_propagator();
        // `Solver::register_fsm` asserts the registration's true-variable;
        // the harness must simulate that assertion so constant-`true`
        // guards' product edges are present.
        let true_var = reg.true_var;
        let true_term = tm.mk_bool(true);
        let false_term = tm.mk_bool(false);
        let mut neg: FxHashMap<TermId, TermId> = FxHashMap::default();
        for &g in &guard_vars {
            neg.insert(g, tm.mk_not(g));
        }
        for (_, _, reach_atoms) in &queries {
            for &(_, atom) in reach_atoms {
                neg.insert(atom, tm.mk_not(atom));
            }
        }

        let mut manager = UserPropagatorManager::new();
        for &w in &watches {
            manager.watch_term(w);
        }
        manager.register_propagator(propagator);
        if let Some(tv) = true_var {
            manager.notify_fixed(tv, true_term);
        }
        for (k, &g) in guard_vars.iter().enumerate() {
            match states[k] {
                Tri::T => manager.notify_fixed(g, true_term),
                Tri::F => manager.notify_fixed(g, false_term),
                Tri::Unfixed => {}
            }
        }
        let _verdict = manager.final_check();
        let consequences = manager.get_consequences();

        // Literal semantics under a concrete guard completion.
        let literal_holds = |j: TermId, present: &[bool]| -> bool {
            if j == true_term || Some(j) == true_var {
                return true;
            }
            for (k, &g) in guard_vars.iter().enumerate() {
                if g == j {
                    return present[k];
                }
                if neg[&g] == j {
                    return !present[k];
                }
            }
            for (word, _, reach_atoms) in &queries {
                for &(qf, atom) in reach_atoms {
                    let truth = guard_truth_fn(&guard_vars, present);
                    let reaches = run_exists(
                        &flat,
                        case.states as u32,
                        case.initial as u32,
                        word,
                        qf,
                        &truth,
                    );
                    if atom == j {
                        return reaches;
                    }
                    if neg[&atom] == j {
                        return !reaches;
                    }
                }
            }
            panic!("unknown justification literal {j:?}");
        };

        // 2. Every consequence: justifications currently true, and valid
        //    in every completion that satisfies them.
        for consequence in &consequences {
            // Identify the consequence term: a reach atom, its negation, or
            // a conflict (false_term). Anything else is a bug.
            let mut resolved: Option<(usize, u32, bool)> = None; // (query, qf, polarity)
            'q: for (qi, (word, _, reach_atoms)) in queries.iter().enumerate() {
                let _ = word;
                for &(qf, atom) in reach_atoms {
                    if consequence.term == atom {
                        resolved = Some((qi, qf, true));
                        break 'q;
                    }
                    if consequence.term == neg[&atom] {
                        resolved = Some((qi, qf, false));
                        break 'q;
                    }
                }
            }
            if resolved.is_none() && consequence.term != false_term {
                panic!("consequence on unknown term {consequence:?}");
            }
            // Justifications currently true (guards and the asserted-true
            // variable; no reach atoms were fixed in this harness).
            for &j in &consequence.justification {
                let holds = j == true_term
                    || Some(j) == true_var
                    || guard_vars.iter().enumerate().any(|(k, &g)| {
                        (g == j && states[k] == Tri::T) || (neg[&g] == j && states[k] == Tri::F)
                    });
                assert!(
                    holds,
                    "justification {j:?} not currently true (guards={states:?}) in {consequence:?}"
                );
            }
            for mask in 0..(1usize << guard_count) {
                let present: Vec<bool> = (0..guard_count).map(|i| mask & (1 << i) != 0).collect();
                if !consequence
                    .justification
                    .iter()
                    .all(|&j| literal_holds(j, &present))
                {
                    continue;
                }
                match resolved {
                    Some((qi, qf, polarity)) => {
                        let truth = guard_truth_fn(&guard_vars, &present);
                        let reaches = run_exists(
                            &flat,
                            case.states as u32,
                            case.initial as u32,
                            &queries[qi].0,
                            qf,
                            &truth,
                        );
                        assert_eq!(
                            reaches, polarity,
                            "invalid consequence {consequence:?} under guards={present:?}"
                        );
                    }
                    None => {
                        panic!("satisfiable conflict {consequence:?} under guards={present:?}");
                    }
                }
            }
        }

        // 3. With all guards fixed, every still-unfixed reach atom must
        //    have propagated its determined value (biconditional).
        if states.iter().all(|&s| s != Tri::Unfixed) {
            let propagated: Vec<TermId> = consequences
                .iter()
                .map(|c| c.term)
                .chain(consequences.iter().map(|c| {
                    // normalize negated terms back to the atom
                    let mut base = c.term;
                    for (_, _, reach_atoms) in &queries {
                        for &(_, atom) in reach_atoms {
                            if base == neg[&atom] {
                                base = atom;
                            }
                        }
                    }
                    base
                }))
                .collect();
            for (word, _, reach_atoms) in &queries {
                let _ = word;
                for &(qf, atom) in reach_atoms {
                    assert!(
                        propagated.contains(&atom) || propagated.contains(&neg[&atom]),
                        "determined reach atom {atom:?} (target {qf}) did not propagate (guards={states:?})"
                    );
                }
            }
        }
    }
}

/// Chain with shared guard, optional skip and an epsilon back-edge:
/// `0 -(0,g0)-> 1`, `1 -(1,g1)-> 2`, `0 -(0,g0)-> 2` (guard shared with the
/// first transition), `2 -(eps,g2)-> 1`.
#[test]
fn oracle_chain_skip_epsilon() {
    check_case(&Case {
        states: 3,
        alphabet: 2,
        initial: 0,
        accepting: &[2],
        transitions: vec![
            (0, Label::Symbol(0), 1, GuardSel::Var(0)),
            (1, Label::Symbol(1), 2, GuardSel::Var(1)),
            (0, Label::Symbol(0), 2, GuardSel::Var(0)),
            (2, Label::Epsilon, 1, GuardSel::Var(2)),
        ],
        words: vec![vec![], vec![0], vec![0, 1], vec![1], vec![0, 0]],
    });
}

/// Epsilon cycle between initial and accepting state: the empty word is
/// accepted iff the forward epsilon guard holds.
#[test]
fn oracle_epsilon_cycle_empty_word() {
    check_case(&Case {
        states: 2,
        alphabet: 1,
        initial: 0,
        accepting: &[1],
        transitions: vec![
            (0, Label::Epsilon, 1, GuardSel::Var(0)),
            (1, Label::Epsilon, 0, GuardSel::Var(1)),
        ],
        words: vec![vec![], vec![0]],
    });
}

/// Parallel transitions with constant guards: a `true` guard makes the
/// word unconditionally accepted; a `false` guard is dead weight.
#[test]
fn oracle_parallel_and_constant_guards() {
    check_case(&Case {
        states: 2,
        alphabet: 1,
        initial: 0,
        accepting: &[1],
        transitions: vec![
            (0, Label::Symbol(0), 1, GuardSel::ConstTrue),
            (0, Label::Symbol(0), 1, GuardSel::Var(0)),
            (0, Label::Symbol(0), 1, GuardSel::ConstFalse),
        ],
        words: vec![vec![], vec![0], vec![0, 0]],
    });
}

/// Disconnected accepting state, multiple accepting states, self-loops.
#[test]
fn oracle_disconnected_multiple_accepting_self_loops() {
    check_case(&Case {
        states: 4,
        alphabet: 2,
        initial: 0,
        accepting: &[1, 3],
        transitions: vec![
            (0, Label::Symbol(0), 1, GuardSel::Var(0)),
            (1, Label::Symbol(1), 1, GuardSel::Var(1)),
            (1, Label::Symbol(0), 2, GuardSel::Var(2)),
            (0, Label::Symbol(1), 0, GuardSel::Var(3)),
        ],
        words: vec![
            vec![],
            vec![0],
            vec![0, 1],
            vec![0, 1, 1],
            vec![1],
            vec![0, 0],
        ],
    });
}

/// Guard reused across two automata in one model (one meaning), plus a
/// negated guard and a compound guard: interpreter semantics over all
/// assignments.
#[test]
fn shared_negated_and_compound_guards() {
    let mut tm = TermManager::new();
    let mut model = FsmModel::new(&tm);
    let a1 = model.new_automaton(2, 1).unwrap();
    model.set_initial(a1, 0).unwrap();
    model.add_accepting(a1, 1).unwrap();
    let a2 = model.new_automaton(2, 1).unwrap();
    model.set_initial(a2, 0).unwrap();
    model.add_accepting(a2, 1).unwrap();
    let g = tm.mk_var("g", tm.sorts.bool_sort);
    let h = tm.mk_var("h", tm.sorts.bool_sort);
    let not_g = tm.mk_not(g);
    let and_gh = tm.mk_and([g, h]);
    // a1: 0 -(0,g)-> 1 and 0 -(0,¬g)-> 1: "0" always accepted.
    model
        .add_transition(a1, 0, 1, Label::Symbol(0), g, &mut tm)
        .unwrap();
    model
        .add_transition(a1, 0, 1, Label::Symbol(0), not_g, &mut tm)
        .unwrap();
    // a2: 0 -(0,g∧h)-> 1: "0" accepted iff g∧h; the same g as a1.
    model
        .add_transition(a2, 0, 1, Label::Symbol(0), and_gh, &mut tm)
        .unwrap();
    let _accepts1 = model.accepts(a1, &[0], &mut tm).unwrap();
    let _accepts2 = model.accepts(a2, &[0], &mut tm).unwrap();

    for g_v in [false, true] {
        for h_v in [false, true] {
            // `truth` must interpret the compound guard terms (the
            // interpreter delegates non-constant guards to the caller).
            let truth = |t: TermId| -> bool {
                if t == g {
                    g_v
                } else if t == h {
                    h_v
                } else if t == not_g {
                    !g_v
                } else {
                    t == and_gh && g_v && h_v
                }
            };
            // a1 accepts "0" for every (g,h): g or ¬g is present.
            assert!(model.accepts_under(a1, &[0], &truth).unwrap());
            // a2 accepts "0" exactly under g∧h — the compound guard keeps
            // its ordinary Boolean meaning.
            assert_eq!(model.accepts_under(a2, &[0], &truth).unwrap(), g_v && h_v);
        }
    }
    // The registration carries no asserted-true variable (no constant-true
    // guards were used).
    let reg = model.registration();
    assert!(reg.true_var.is_none());
    assert_eq!(reg.bindings.len(), 2);
}

/// Malformed declarations and references are rejected explicitly, before
/// any constraint is installed.
#[test]
fn rejects_malformed_declarations() {
    let mut tm = TermManager::new();
    let mut model = FsmModel::new(&tm);
    // Zero states.
    assert!(model.new_automaton(0, 2).is_err());
    // Counts beyond u32.
    assert!(model.new_automaton(u32::MAX as usize + 1, 1).is_err());
    // Unknown handles.
    assert!(model.set_initial(AutomatonHandle::new(9), 0).is_err());
    let a = model.new_automaton(2, 2).unwrap();
    // Out-of-range states.
    assert!(model.set_initial(a, 2).is_err());
    assert!(model.add_accepting(a, 5).is_err());
    assert!(
        model
            .add_transition(a, 0, 2, Label::Symbol(0), tm.mk_bool(true), &mut tm)
            .is_err()
    );
    // Symbol beyond the alphabet.
    assert!(
        model
            .add_transition(
                a,
                0,
                1,
                Label::Symbol(2),
                tm.mk_var("g", tm.sorts.bool_sort),
                &mut tm
            )
            .is_err()
    );
    // Non-Boolean guard.
    let int_var = tm.mk_var("i", tm.sorts.int_sort);
    assert!(
        model
            .add_transition(a, 0, 1, Label::Symbol(0), int_var, &mut tm)
            .is_err()
    );
    // Unknown guard term.
    assert!(
        model
            .add_transition(a, 0, 1, Label::Symbol(0), TermId::new(999_999), &mut tm)
            .is_err()
    );
    // Missing initial state blocks acceptance queries.
    model.add_accepting(a, 1).unwrap();
    assert!(model.accepts(a, &[], &mut tm).is_err());
    model.set_initial(a, 0).unwrap();
    // Duplicate initial, duplicate accepting.
    assert!(model.set_initial(a, 1).is_err());
    assert!(model.add_accepting(a, 1).is_err());
    // Word symbols beyond the alphabet.
    assert!(model.accepts(a, &[7], &mut tm).is_err());
    // Accepting is fine now.
    assert!(model.accepts(a, &[], &mut tm).is_ok());
    // Unknown automaton for the query and interpreter.
    assert!(
        model
            .accepts(AutomatonHandle::new(9), &[], &mut tm)
            .is_err()
    );
}

/// A product whose vertex count overflows u32 is rejected before any
/// vertex is added (resource-failure handling: no partial loops).
#[test]
fn rejects_oversized_product() {
    let mut tm = TermManager::new();
    let mut model = FsmModel::new(&tm);
    // states = 3_000_000_000 (fits u32); word length 1 makes the product
    // 6_000_000_000 vertices > u32::MAX. The check fires before the
    // vertex loop, so this returns instantly rather than hanging.
    let a = model.new_automaton(3_000_000_000, 1).unwrap();
    model.set_initial(a, 0).unwrap();
    model.add_accepting(a, 1).unwrap();
    match model.accepts(a, &[0], &mut tm) {
        Err(FsmError(msg)) => assert_eq!(msg, "product graph too large"),
        other => panic!("expected oversized-product error, got {other:?}"),
    }
}

/// Query idempotence and naming rules.
#[test]
fn query_caching_and_names() {
    let mut tm = TermManager::new();
    let mut model = FsmModel::new(&tm);
    let a = model.new_automaton(2, 1).unwrap();
    model.set_initial(a, 0).unwrap();
    model.add_accepting(a, 1).unwrap();
    let g = tm.mk_var("g", tm.sorts.bool_sort);
    model
        .add_transition(a, 0, 1, Label::Symbol(0), g, &mut tm)
        .unwrap();
    // Same (automaton, word) -> same atom.
    let a1 = model.accepts(a, &[0], &mut tm).unwrap();
    let a2 = model.accepts(a, &[0], &mut tm).unwrap();
    assert_eq!(a1, a2);
    // A distinct word gets a distinct atom.
    let b = model.accepts(a, &[], &mut tm).unwrap();
    assert_ne!(a1, b);
    // Named query mints the named constant.
    let named = model
        .accepts_named(a, &[0], "accepts_zero", &mut tm)
        .unwrap();
    let named_term = tm.mk_var("accepts_zero", tm.sorts.bool_sort);
    assert_eq!(named, named_term);
    // A name cannot serve two queries.
    assert!(
        model
            .accepts_named(a, &[], "accepts_zero", &mut tm)
            .is_err()
    );
    // The un-named query still resolves to the original atom.
    assert_eq!(model.accepts(a, &[0], &mut tm).unwrap(), a1);
    // Reach-atom introspection: one disjunct for the single accepting
    // state; unknown word is an explicit error.
    let disjuncts = model.acceptance_reach_atoms(a, &[0]).unwrap();
    assert_eq!(disjuncts.len(), 1);
    assert_eq!(disjuncts[0].0, 1);
    assert!(model.acceptance_reach_atoms(a, &[0, 0]).is_err());
    // Registration binds both atoms.
    let reg = model.registration();
    assert_eq!(reg.bindings.len(), 3);
    assert!(reg.bindings.iter().any(|&(atom, _)| atom == a1));
    assert!(reg.bindings.iter().any(|&(atom, _)| atom == named));
}

/// An automaton with no accepting states accepts nothing, not even the
/// empty word: the definition lowers to the constant false.
#[test]
fn no_accepting_states_accepts_nothing() {
    let mut tm = TermManager::new();
    let mut model = FsmModel::new(&tm);
    let a = model.new_automaton(2, 1).unwrap();
    model.set_initial(a, 0).unwrap();
    let g = tm.mk_var("g", tm.sorts.bool_sort);
    model
        .add_transition(a, 0, 1, Label::Symbol(0), g, &mut tm)
        .unwrap();
    let truth = |_| true;
    assert!(!model.accepts_under(a, &[], &truth).unwrap());
    assert!(!model.accepts_under(a, &[0], &truth).unwrap());
    assert!(model.accepts(a, &[], &mut tm).is_ok());
    assert!(model.acceptance_reach_atoms(a, &[]).unwrap().is_empty());
}

/// An epsilon-only alphabet (alphabet size zero) accepts only via epsilon
/// paths, and non-empty words are rejected as out of range.
#[test]
fn epsilon_only_alphabet() {
    let mut tm = TermManager::new();
    let mut model = FsmModel::new(&tm);
    let a = model.new_automaton(3, 0).unwrap();
    model.set_initial(a, 0).unwrap();
    model.add_accepting(a, 2).unwrap();
    let g0 = tm.mk_var("e0", tm.sorts.bool_sort);
    let g1 = tm.mk_var("e1", tm.sorts.bool_sort);
    model
        .add_transition(a, 0, 1, Label::Epsilon, g0, &mut tm)
        .unwrap();
    model
        .add_transition(a, 1, 2, Label::Epsilon, g1, &mut tm)
        .unwrap();
    let truth = |t: TermId| t == g0 || t == g1;
    assert!(model.accepts_under(a, &[], &truth).unwrap());
    let truth_off = |t: TermId| t == g1;
    assert!(!model.accepts_under(a, &[], &truth_off).unwrap());
    // Any symbol is out of range for a zero-symbol alphabet.
    assert!(model.accepts(a, &[0], &mut tm).is_err());
    // Symbol transitions cannot even be declared.
    assert!(
        model
            .add_transition(a, 0, 1, Label::Symbol(0), g0, &mut tm)
            .is_err()
    );
}
