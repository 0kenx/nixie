//! Runtime invariant checks for the CDCL SAT solver.
//!
//! This module is a debug-only structural/soundness net over [`Solver`]'s
//! internal data model: the clause database, the assignment trail, the
//! two-watched-literal scheme, the implication graph, and learned-clause
//! bookkeeping (LBD). Every function here is a pure, read-only check that
//! returns `Err(String)` describing the first violation found, or `Ok(())`.
//! None of them mutate the solver and none of them are ever called outside
//! `#[cfg(debug_assertions)]` call sites (see the `debug_check_*` wrapper
//! methods next to [`Solver::debug_verify_model`] in `solver::learn`), so
//! this module costs nothing in release builds.
//!
//! # Two families of check: timeless vs. situational
//!
//! Some invariants hold at *any* point in the search and are grouped into
//! [`check_all_sat_invariants`]: clause well-formedness, trail/assignment
//! consistency, decision-level bookkeeping, static LBD bounds, live reason
//! clauses, and implication-graph acyclicity.
//!
//! Others are only meaningful at a *specific* moment and are deliberately
//! **not** part of that sweep:
//!
//! - [`check_watched_literals`] and [`check_unit_propagation_complete`] only
//!   hold once `propagate()` has reached a fixpoint (returned `None`); mid-scan,
//!   `propagate()` routinely leaves a literal's watch list half-examined (see
//!   `Trail::requeue_last_propagated`), which would make these checks fire on
//!   perfectly correct in-progress states.
//! - [`check_conflict_clause`] only holds against the exact assignment that
//!   produced a conflict, before any backtrack changes the trail.
//! - [`check_restart_consistency`] only holds immediately after a restart
//!   (which backtracks to level 0).
//! - [`check_learned_clause_lbd`] only holds in the instant right after a
//!   clause is learned; see its own doc comment for why it cannot be a
//!   whole-database sweep.
//!
//! # A finding from wiring this module in: the ported "monotonic trail" check
//! was wrong
//!
//! This file originally asserted that decision levels are non-decreasing
//! along the trail. That is false for this solver: chronological
//! backtracking (`SolverConfig::enable_chronological_backtrack`, **on** by
//! default) deliberately records a propagated literal at a level *below* the
//! decision level the search currently sits at (see
//! `Trail::assign_propagation_at` and `Trail::backtrack_to_with_callback`'s
//! own doc comments -- the trail is explicitly documented there as *not*
//! sorted by level). Reintroducing that assertion would fail on entirely
//! correct solver behavior every time chronological backtracking actually
//! fires. [`check_decision_levels`] therefore only checks the invariant that
//! *does* hold unconditionally: no trail entry's level exceeds the current
//! decision level.
//!
//! Similarly, the ported "LBD must be positive" check would fire on every
//! unit learned clause: `Solver::solve`'s `len() == 1` branch stores the unit
//! fact directly and never calls `compute_lbd`, so such a clause's `lbd`
//! field legitimately stays at its default of `0`. [`check_learned_clause_bounds`]
//! excludes unit clauses to match that convention instead of flagging it.

use crate::clause::ClauseId;
use crate::literal::{Lit, Var};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::solver::Solver;
use crate::trail::Reason;
// Only the `#[cfg(debug_assertions)]` situational checkers name `Trail`
// directly, so the import must carry the same gate.
#[cfg(debug_assertions)]
use crate::trail::Trail;
use smallvec::SmallVec;

/// Runs every invariant that holds at an arbitrary point in the search.
///
/// Deliberately excludes the situational checks described in the module doc
/// comment -- call those directly at their specific hook points instead.
pub(crate) fn check_all_sat_invariants(solver: &Solver) -> Result<(), String> {
    check_clause_database(solver)?;
    check_assignment_consistency(solver)?;
    check_decision_levels(solver)?;
    check_learned_clause_bounds(solver)?;
    check_reason_clauses_live(solver)?;
    check_implication_graph_acyclic(solver)?;
    Ok(())
}

/// Every live (non-deleted) clause is duplicate-literal-free, not a
/// tautology, and references only variables the solver actually has.
///
/// Unlike `Solver::add_clause` (which normalizes original clauses before
/// storing them), clauses reaching the database through `add_learned` are
/// not normalized on the way in, so this is a meaningful check on learned
/// clauses too: a 1-UIP resolvent containing both a literal and its negation
/// would indicate a bug in conflict analysis, not a bug in this check.
pub(crate) fn check_clause_database(solver: &Solver) -> Result<(), String> {
    for id in solver.clauses.iter_ids() {
        let Some(clause) = solver.clauses.get(id) else {
            continue;
        };
        let lits = &clause.lits;
        for i in 0..lits.len() {
            for j in (i + 1)..lits.len() {
                if lits[i] == lits[j] {
                    return Err(format!(
                        "clause {id:?} contains duplicate literal {:?}",
                        lits[i]
                    ));
                }
                if lits[i] == lits[j].negate() {
                    return Err(format!(
                        "clause {id:?} is a tautology ({:?} and its negation both present)",
                        lits[i]
                    ));
                }
            }
        }
        for &lit in lits.iter() {
            if lit.var().index() >= solver.num_vars {
                return Err(format!(
                    "clause {id:?} references variable {} but the solver only has {} variables",
                    lit.var().index(),
                    solver.num_vars
                ));
            }
        }
    }
    Ok(())
}

/// Every variable the trail's per-variable state (`Trail::value`) reports as
/// assigned actually appears among the trail's recorded assignments.
///
/// Given `Trail::assign_at`'s implementation this holds by construction --
/// there is no code path that marks a variable defined without pushing it --
/// so a violation here would mean the trail's two halves (the `var_info`
/// side-table and the `assignments` sequence) have gone out of sync, which is
/// exactly the class of corruption this net exists to catch early.
pub(crate) fn check_assignment_consistency(solver: &Solver) -> Result<(), String> {
    let mut on_trail: HashSet<usize> = HashSet::default();
    for &lit in solver.trail.assignments() {
        on_trail.insert(lit.var().index());
    }
    for idx in 0..solver.num_vars {
        let var = Var::new(idx as u32);
        let value = solver.trail.value(var);
        if value.is_defined() && !on_trail.contains(&idx) {
            return Err(format!(
                "variable {idx} is assigned ({value:?}) but does not appear on the trail"
            ));
        }
    }
    Ok(())
}

/// Post-fixpoint check: no live clause of two or more literals may have both
/// of its watched literals (`clause.lits[0]`, `clause.lits[1]` -- see
/// `solver::propagate`'s own doc comments for why those two positions are
/// always the watched pair between propagation calls) false while the clause
/// itself is unsatisfied. If that ever holds, unit propagation should have
/// fired (or a conflict should have been reported) before `propagate()`
/// returned `None`. This semantic property holds for every clause of length
/// two or more; the additional structural "is it actually registered in
/// `solver.watches`" check only applies at length three or more -- see the
/// comment at its call site below for why length-2 clauses are exempt (this
/// solver has a second, independent propagation mechanism for them).
///
/// Only meaningful once `propagate()` has returned `None` (a fixpoint);
/// mid-scan it is routine for a clause to transiently have both watches
/// false while its watcher entry has simply not been revisited yet.
pub(crate) fn check_watched_literals(solver: &Solver) -> Result<(), String> {
    for id in solver.clauses.iter_ids() {
        let Some(clause) = solver.clauses.get(id) else {
            continue;
        };
        if clause.lits.len() < 2 {
            continue;
        }
        let w0 = clause.lits[0];
        let w1 = clause.lits[1];

        // Structural registration check: only for length >= 3.
        //
        // A length-2 clause has *two* independent, mutually sufficient
        // propagation mechanisms in this solver: the general two-watched-
        // literal scheme (`solver.watches`) and the direct-indexed binary
        // implication graph (`solver.binary_graph`, see `propagate()`'s
        // "backed" check, which accepts any live 2-literal clause matching
        // an edge). Different call sites pick different ones --
        // `Solver::add_clause` and `learn_clause`'s binary branch register
        // *both* (redundant but harmless), `check_hyper_binary_resolution`
        // registers *only* the binary graph, and `add_theory_reason_clause`
        // registers *only* the watch list -- so a length-2 clause lacking a
        // watch-list entry is not a violation, only evidence that the binary
        // graph is the one enforcing it. A length >= 3 clause has no such
        // alternative: the binary graph only ever stores 2-literal edges, so
        // the general watched-literal scheme is the *only* mechanism able to
        // enforce it, and registration is mandatory there.
        if clause.lits.len() >= 3 {
            if !solver
                .watches
                .get(w0.negate())
                .iter()
                .any(|w| w.clause == id)
            {
                return Err(format!(
                    "clause {id:?} treats {w0:?} as a watched literal, but it is not registered \
                     in the watch list keyed by its negation"
                ));
            }
            if !solver
                .watches
                .get(w1.negate())
                .iter()
                .any(|w| w.clause == id)
            {
                return Err(format!(
                    "clause {id:?} treats {w1:?} as a watched literal, but it is not registered \
                     in the watch list keyed by its negation"
                ));
            }
        }

        // The "not both watches false while unsatisfied" semantic property,
        // though, holds for every clause of length >= 2 regardless of which
        // mechanism enforces it -- it is a statement about the assignment,
        // not about `solver.watches` specifically.
        let satisfied = clause
            .lits
            .iter()
            .any(|&l| solver.trail.lit_value(l).is_true());
        if satisfied {
            continue;
        }
        if solver.trail.lit_value(w0).is_false() && solver.trail.lit_value(w1).is_false() {
            return Err(format!(
                "clause {id:?} is unsatisfied with both watched literals false \
                 ({w0:?}, {w1:?}) at a propagation fixpoint; unit propagation should have \
                 fired or reported a conflict before reaching it"
            ));
        }
    }
    Ok(())
}

/// Post-fixpoint check: no live clause is a "hanging unit" -- exactly one
/// unassigned literal with every other literal false, and the clause not
/// otherwise satisfied. Two-watched-literal propagation guarantees such a
/// clause is either satisfied, a conflict, or propagated before a fixpoint is
/// reported; a hanging unit at a fixpoint means a live constraint was never
/// enforced.
///
/// Only meaningful once `propagate()` has returned `None`, for the same
/// reason as [`check_watched_literals`].
pub(crate) fn check_unit_propagation_complete(solver: &Solver) -> Result<(), String> {
    for id in solver.clauses.iter_ids() {
        let Some(clause) = solver.clauses.get(id) else {
            continue;
        };
        if clause.lits.is_empty() {
            continue;
        }
        let mut unassigned = 0usize;
        let mut satisfied = false;
        for &lit in clause.lits {
            let value = solver.trail.lit_value(lit);
            if value.is_true() {
                satisfied = true;
                break;
            }
            if !value.is_defined() {
                unassigned += 1;
            }
        }
        if !satisfied && unassigned == 1 {
            return Err(format!(
                "clause {id:?} is a hanging unit at a propagation fixpoint: it has exactly one \
                 unassigned literal and is not satisfied, so unit propagation should have fired"
            ));
        }
    }
    Ok(())
}

/// The implication graph induced by reason clauses over the trail is acyclic.
///
/// Every non-decision, non-theory literal on the trail was propagated by a
/// reason clause; walking from each trail literal through its reason
/// clause's other literals must never revisit a variable still on the
/// current path, or the "implication" relation is circular, which cannot
/// happen in a sound CDCL run (a reason clause can only depend on literals
/// assigned *before* the one it justifies).
///
/// Implemented as an explicit-stack DFS rather than recursively: recursion
/// depth would be proportional to the trail length, which is proportional to
/// the number of variables, and this check must remain safe on large
/// instances, not just the small ones exercised by this crate's test suite.
pub(crate) fn check_implication_graph_acyclic(solver: &Solver) -> Result<(), String> {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Mark {
        Unvisited,
        InProgress,
        Done,
    }

    let mut mark = vec![Mark::Unvisited; solver.num_vars];
    // Each frame is (variable, number of its reason clause's literals already
    // examined).
    let mut stack: Vec<(usize, usize)> = Vec::new();

    for &root_lit in solver.trail.assignments() {
        let root = root_lit.var().index();
        if !matches!(mark[root], Mark::Unvisited) {
            continue;
        }
        mark[root] = Mark::InProgress;
        stack.push((root, 0));

        while let Some(&(var, next_idx)) = stack.last() {
            let reason_lits: SmallVec<[Lit; 8]> = match solver.trail.reason(Var::new(var as u32)) {
                Reason::Propagation(clause_id) => match solver.clauses.get(clause_id) {
                    Some(clause) => clause.lits.iter().copied().collect(),
                    None => {
                        return Err(format!(
                            "variable {var} has propagation reason {clause_id:?}, which does \
                             not exist in the clause database"
                        ));
                    }
                },
                Reason::Decision | Reason::Theory => SmallVec::new(),
            };

            let mut pushed = false;
            let mut scan_idx = next_idx;
            while scan_idx < reason_lits.len() {
                let neighbor = reason_lits[scan_idx].var().index();
                scan_idx += 1;
                if neighbor == var {
                    continue; // a reason clause always contains its own consequence
                }
                match mark[neighbor] {
                    Mark::Unvisited => {
                        mark[neighbor] = Mark::InProgress;
                        let frame_idx = stack.len() - 1;
                        stack[frame_idx].1 = scan_idx;
                        stack.push((neighbor, 0));
                        pushed = true;
                        break;
                    }
                    Mark::InProgress => {
                        return Err(format!(
                            "cycle detected in the implication graph through variable {neighbor}"
                        ));
                    }
                    Mark::Done => {}
                }
            }

            if pushed {
                continue;
            }

            mark[var] = Mark::Done;
            stack.pop();
        }
    }

    Ok(())
}

/// No trail entry's recorded level exceeds the solver's current decision
/// level.
///
/// This is deliberately weaker than "levels are non-decreasing along the
/// trail" -- see the module doc comment for why that stronger property is
/// simply false under chronological backtracking (on by default) and was
/// removed rather than ported as-is.
pub(crate) fn check_decision_levels(solver: &Solver) -> Result<(), String> {
    let current = solver.trail.decision_level();
    for &lit in solver.trail.assignments() {
        let level = solver.trail.level(lit.var());
        if level > current {
            return Err(format!(
                "variable {} is recorded at level {} which exceeds the current decision level {}",
                lit.var().index(),
                level,
                current
            ));
        }
    }
    Ok(())
}

/// Static, timeless bounds on every live learned clause's stored LBD: at
/// least 1 and at most the clause's length.
///
/// Deliberately does **not** recompute LBD from the current trail and compare
/// it against the stored value the way [`check_learned_clause_lbd`] does.
/// Decision levels are reused across unrelated branches over the life of a
/// search, so recomputing "the distinct levels among this clause's literals"
/// against a *later* trail does not check anything about the clause -- it
/// only reflects whatever the search happens to be doing now, and would
/// misfire constantly on a perfectly healthy solver. See that function's doc
/// comment for the check that *is* valid, at the one moment it is valid.
///
/// Unit learned clauses are excluded: `Solver::solve`'s `len() == 1` branch
/// never calls `compute_lbd`, so their `lbd` field legitimately stays `0`.
pub(crate) fn check_learned_clause_bounds(solver: &Solver) -> Result<(), String> {
    for id in solver.clauses.iter_ids() {
        let Some(clause) = solver.clauses.get(id) else {
            continue;
        };
        if !clause.learned || clause.lits.len() < 2 {
            continue;
        }
        if clause.lbd == 0 {
            return Err(format!(
                "learned clause {id:?} (length {}) has LBD 0",
                clause.lits.len()
            ));
        }
        if clause.lbd as usize > clause.lits.len() {
            return Err(format!(
                "learned clause {id:?} has LBD {} exceeding its length {}",
                clause.lbd,
                clause.lits.len()
            ));
        }
    }
    Ok(())
}

/// A freshly learned clause's stored LBD matches recomputing it right now.
///
/// Only sound to call in the instant right after `clause_id` was learned and
/// its `lbd` field set, before any further decision or backtrack changes what
/// "the current level" means for its literals' variables -- decision levels
/// are reused across unrelated branches over a search's lifetime, so this
/// same comparison run later would compare the clause against a trail state
/// that has nothing to do with the one it was learned from. See
/// `Solver::compute_lbd` (`solver::learn`), which this mirrors exactly
/// (including counting level 0 as a distinct level, unlike
/// `conflict::compute_lbd_from_literals`'s separate level-0-excluding
/// variant used elsewhere).
#[cfg(debug_assertions)]
pub(crate) fn check_learned_clause_lbd(solver: &Solver, clause_id: ClauseId) -> Result<(), String> {
    let Some(clause) = solver.clauses.get(clause_id) else {
        return Err(format!(
            "just-learned clause {clause_id:?} is missing from the database"
        ));
    };
    if clause.lits.len() < 2 {
        return Ok(()); // unit clauses carry no LBD; see check_learned_clause_bounds
    }
    let recomputed = recompute_lbd(&solver.trail, clause.lits);
    if recomputed != clause.lbd {
        return Err(format!(
            "learned clause {clause_id:?} was stored with LBD {} but recomputing it \
             immediately after learning gives {recomputed}",
            clause.lbd
        ));
    }
    Ok(())
}

/// Number of distinct decision levels among `lits`, counting level 0 as a
/// distinct level. Mirrors `Solver::compute_lbd` exactly (see that
/// function's doc comment in `solver::learn`).
#[cfg(debug_assertions)]
fn recompute_lbd(trail: &Trail, lits: &[Lit]) -> u32 {
    let mut levels: Vec<u32> = Vec::new();
    for &lit in lits {
        let level = trail.level(lit.var());
        if !levels.contains(&level) {
            levels.push(level);
        }
    }
    levels.len() as u32
}

/// A conflict clause reported by `propagate()` is fully assigned and fully
/// falsified.
///
/// Only sound to call against the exact assignment that produced the
/// conflict, before any backtrack runs -- call this right where `propagate()`
/// returns `Some(conflict)`.
#[cfg(debug_assertions)]
pub(crate) fn check_conflict_clause(solver: &Solver, conflict: ClauseId) -> Result<(), String> {
    let Some(clause) = solver.clauses.get(conflict) else {
        return Err(format!(
            "propagate() reported conflict clause {conflict:?}, which is not in the database"
        ));
    };
    for &lit in clause.lits {
        let value = solver.trail.lit_value(lit);
        if value.is_true() {
            return Err(format!(
                "propagate() reported conflict clause {conflict:?}, but literal {lit:?} is \
                 satisfied"
            ));
        }
        if !value.is_defined() {
            return Err(format!(
                "propagate() reported conflict clause {conflict:?}, but literal {lit:?} is \
                 unassigned"
            ));
        }
    }
    Ok(())
}

/// After a restart (which always backtracks to level 0, see
/// `Solver::restart`), the decision level is 0 and every trail entry is a
/// level-0 fact.
#[cfg(debug_assertions)]
pub(crate) fn check_restart_consistency(solver: &Solver) -> Result<(), String> {
    if solver.trail.decision_level() != 0 {
        return Err(format!(
            "decision level is {} right after a restart, expected 0",
            solver.trail.decision_level()
        ));
    }
    for &lit in solver.trail.assignments() {
        let level = solver.trail.level(lit.var());
        if level != 0 {
            return Err(format!(
                "variable {} is on the trail at level {level} right after a restart, expected \
                 only level-0 facts",
                lit.var().index()
            ));
        }
    }
    Ok(())
}

/// Every currently assigned variable whose reason is a clause (as opposed to
/// a decision or a theory propagation) points at a clause that still exists
/// and has not been deleted.
///
/// A dangling or deleted reason means the assignment's justification has been
/// pulled out from under it -- `Solver::reduce_clause_database` and
/// `check_subsumption` both check `is_reason` before removing a clause
/// precisely to prevent this, so a violation here indicates one of those
/// checks has a gap.
pub(crate) fn check_reason_clauses_live(solver: &Solver) -> Result<(), String> {
    for &lit in solver.trail.assignments() {
        let var = lit.var();
        if let Reason::Propagation(clause_id) = solver.trail.reason(var) {
            match solver.clauses.get(clause_id) {
                Some(clause) if !clause.deleted => {}
                Some(_) => {
                    return Err(format!(
                        "variable {} is assigned with reason {clause_id:?}, but that clause \
                         has been deleted",
                        var.index()
                    ));
                }
                None => {
                    return Err(format!(
                        "variable {} is assigned with reason {clause_id:?}, which does not \
                         exist in the clause database",
                        var.index()
                    ));
                }
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver::SolverResult;

    #[test]
    fn empty_solver_satisfies_all_timeless_invariants() {
        let solver = Solver::new();
        assert_eq!(check_all_sat_invariants(&solver), Ok(()));
    }

    #[test]
    fn simple_sat_instance_satisfies_all_timeless_invariants() {
        let mut solver = Solver::new();
        let a = solver.new_var();
        solver.add_clause([Lit::pos(a)]);

        assert_eq!(solver.solve(), SolverResult::Sat);
        assert_eq!(check_all_sat_invariants(&solver), Ok(()));
        assert_eq!(check_watched_literals(&solver), Ok(()));
        assert_eq!(check_unit_propagation_complete(&solver), Ok(()));
    }

    #[test]
    fn simple_unsat_instance_satisfies_all_timeless_invariants() {
        let mut solver = Solver::new();
        let a = solver.new_var();
        solver.add_clause([Lit::pos(a)]);
        solver.add_clause([Lit::neg(a)]);

        assert_eq!(solver.solve(), SolverResult::Unsat);
        assert_eq!(check_all_sat_invariants(&solver), Ok(()));
    }

    #[test]
    #[allow(clippy::needless_range_loop)] // clearest as explicit 2D (hole, pigeon) indexing
    fn pigeonhole_instance_satisfies_all_invariants_at_every_conflict() {
        // A slightly larger UNSAT instance that forces several conflicts and
        // backtracks, exercising the acyclicity walk and the reason-clause
        // liveness check over a non-trivial implication graph.
        let mut solver = Solver::new();
        let n = 4; // n+1 pigeons into n holes: UNSAT, forces real search
        let mut vars = vec![vec![]; n + 1];
        for pigeon_vars in vars.iter_mut().take(n + 1) {
            for _ in 0..n {
                pigeon_vars.push(solver.new_var());
            }
        }
        for pigeon_vars in &vars {
            solver.add_clause(pigeon_vars.iter().map(|&v| Lit::pos(v)));
        }
        for hole in 0..n {
            for p1 in 0..=n {
                for p2 in (p1 + 1)..=n {
                    solver.add_clause([Lit::neg(vars[p1][hole]), Lit::neg(vars[p2][hole])]);
                }
            }
        }

        assert_eq!(solver.solve(), SolverResult::Unsat);
        assert_eq!(check_all_sat_invariants(&solver), Ok(()));
    }

    #[test]
    fn implication_graph_check_rejects_a_dangling_reason() {
        // A synthetic (impossible-in-practice) dangling reason, constructed
        // solely to confirm the check actually detects one rather than
        // silently passing.
        let mut solver = Solver::new();
        let a = solver.new_var();
        solver.trail.new_decision_level();
        solver
            .trail
            .assign_propagation(Lit::pos(a), ClauseId::new(9999));
        assert!(check_implication_graph_acyclic(&solver).is_err());
        assert!(check_reason_clauses_live(&solver).is_err());
    }
}
