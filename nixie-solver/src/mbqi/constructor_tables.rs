//! Constructor-table completion — Z3 `smt_model_finder`'s entry-table
//! search, the piece that closes set-definitional axiom families
//! (`union`/`intersection`/`difference` through `member`).
//!
//! # The problem this solves
//!
//! A definitional axiom family
//!
//! ```text
//! (forall ((?x Elem) (?s1 Set) (?s2 Set))
//!   (= (member ?x (union ?s1 ?s2)) (or (member ?x ?s1) (member ?x ?s2))))
//! ```
//!
//! constrains the *observer* (`member`) at the compound `union(s1,s2)` but
//! never equates `union(s1,s2)` with a simpler element.  The ground model
//! is therefore free to give every compound a fresh value, and the
//! instantiation loop chases the compound closure forever
//! (`union(union(b,b),a)`, ...): each round's instances mint deeper
//! compounds, the entry tables bloat past every cap, and the rounds
//! diverge (`unknown`).
//!
//! # The fix (Z3's `auf_solver` entry tables, adapted)
//!
//! At completion, for every *constructor* — an uninterpreted function
//! `f : S^n -> S` into an uninterpreted (finite-model) sort, defined
//! through a Bool-valued *observer* `g` by an axiom
//! `g(v..., f(w...)) = psi(v..., w...)` — compute a **semantic table**:
//!
//! * the *row* of a range element `z` is the observer's truth vector over
//!   the row points (the ground universes of the observer's other
//!   arguments);
//! * at every *unpinned* tuple `t` of the range universe, the target row
//!   is `psi`'s truth at `(row point, t)` under the completed model, and
//!   the computed entry is `f(t) := z` for the first universe element
//!   whose row matches — so the completed interpretation is *closed under
//!   its own definitional axioms by construction* (`union(b,b)` reads `b`
//!   because their rows coincide), and the compound chase has nothing to
//!   mint: the table already answers every compound point.
//!
//! # Design requirements (proven by the 2026-09-14 experiments —
//!   `docs/studies/2026-09-14-uflra-handoff-executed.md`)
//!
//! * **One globally-consistent interpretation per round.**  The tables are
//!   computed *inside* `ModelCompleter::complete` and stored on the
//!   [`CompletedModel`], so every consumer — the nested checker, the
//!   falsifier mining, the enumerative seeder, the defining pins — sees
//!   the same tables.  The certifications of different quantifiers can
//!   never rest on different one-shot interpretations (the divergence
//!   vector that removed the else-revision search).
//! * **Ground pins never overridden.**  Computed entries are created only
//!   at tuples with no harvested ground entry, and they live in a separate
//!   table consulted *after* the ground entries.  A pinned tuple that
//!   violates its definitional axiom stays violated — the nested check
//!   finds the falsifier and the loop revises the *ground* model, exactly
//!   as before (the verify-revise step).
//! * **Semantic (not syntactic) value normalization.**  Two range elements
//!   with equal rows are the same semantic point.  The frozen
//!   `semantic_domains` map a constructor argument axis of a defining
//!   axiom to the raw universe with compounds collapsed *through the
//!   computed tables* (`semantic_value_of`), so the seeder and the mining
//!   odometer stop enumerating `union(b,b)` next to `b` — while raw
//!   non-compound elements are never merged (the `seteq` merge-forcing
//!   instances must keep seeing every ground pair).
//! * **Explicit stacks everywhere.**  `semantic_value_of` walks the
//!   constructor-spine with a heap frame machine (the AGENTS.md rule);
//!   the row/target evaluation reuses `CompletionEval`, itself a frame
//!   machine.
//!
//! # Soundness
//!
//! A computed entry is an *interpretation choice* for an unpinned tuple —
//! the same class of decision as an `else` value: the completed model is
//! "ground pins + computed entries + else", and the nested check verifies
//! every quantifier against exactly that total interpretation.  Choosing
//! it can only change *which* completions are certifiable, never the
//! soundness of a certification.  The final `sat` keeps its printed-model
//! honesty through the `SatisfiedWithPins` convergence: certification
//! emits the defining instances at universe tuples (sound lemmas —
//! instances of asserted universals), the ground model absorbs them, and
//! `Satisfied` is only returned once no fresh pin remains.
//!
//! Reference: `src/smt/smt_model_finder.cpp` in Z3 (`fix_model`,
//! `auf_solver`, the entry-table completion), and the CAV 2009 paper
//! (Ge & de Moura, "Complete instantiation for quantified formulas in
//! satisfiability modulo theories").

use nixie_core::ast::traversal::collect_free_vars_including_patterns;
use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::interner::Spur;
use nixie_core::sort::{SortId, SortKind};
use smallvec::SmallVec;

use super::QuantifiedFormula;
use super::model_completion::{CompletedModel, FunctionEntry, FunctionInterpretation};
#[allow(unused_imports)]
use crate::prelude::*;

/// Cap on the range universe size a constructor table is computed over.
/// The tuple product is bounded separately by [`MAX_TABLE_TUPLES`]
/// (partial tables are sound — the uncovered tuples fall to the `else`);
/// this bound keeps the row/tuple work and the ite chains proportioned.
/// Set to match the Skolem-restriction bound: mid-loop universes polluted
/// by pre-MBQI minting (every compound the earlier engines internalized)
/// must still get their tables — declining there drops the semantic
/// normalization with it and the chase restarts.
const MAX_CONSTRUCTOR_UNIVERSE: usize = 32;

/// Cap on the row-point product (the observer's non-result axes).
const MAX_ROW_POINTS: usize = 64;

/// Cap on the tuples walked per constructor per round.
const MAX_TABLE_TUPLES: usize = 512;

/// Cap on the tuples walked per hint table per round.
const MAX_HINT_TUPLES: usize = 512;

/// Cap on the bounded-quantifier expansion inside a hint body (product of
/// the bound variables' universe sizes per quantifier).
const MAX_QUANTIFIER_PRODUCT: usize = 64;

/// Cap on quantifier alternations inside a hint body.
const MAX_QUANTIFIER_DEPTH: u32 = 4;

/// One extracted quasi-macro: a definitional axiom
/// `g(v..., f(w...)) = psi(v..., w...)` with `f` an uninterpreted-range
/// constructor observed through the Bool-valued `g`.
pub(crate) struct QuasiMacro {
    /// The defining axiom (a tracked quantifier term).
    pub quantifier: TermId,
    /// The constructor `f`: uninterpreted, uninterpreted-range.
    pub func: Spur,
    /// `f`'s range sort (an uninterpreted sort).
    pub func_range: SortId,
    /// The observer `g`: Bool-valued, uninterpreted.
    pub observer: Spur,
    /// The observer's argument template: which positions carry the
    /// constructor result and which carry axis variables (indices into
    /// the axiom's `bound_vars`).
    observer_args: SmallVec<[ObserverArg; 4]>,
    /// `f`'s arguments as indices into the axiom's `bound_vars`.
    func_args: SmallVec<[usize; 4]>,
    /// The defining body: its truth at `(row point, tuple)` is the target
    /// row entry.  Mentions the observer at non-result positions only —
    /// never the constructor itself.
    psi: TermId,
}

/// One observer argument position.
enum ObserverArg {
    /// The constructor result position.
    Result,
    /// An axis variable (its sort's ground universe is a row coordinate).
    Axis(usize),
}

/// One extracted *hint* macro: an axiom `psi(v...) => h(v...)` with `h` a
/// Bool-valued uninterpreted function — Z3 `smt_model_finder`'s hint
/// shape.  The hint completes `h` at unpinned tuples as `psi`'s truth
/// there, which satisfies the axiom by construction; the dual direction
/// (whenever it exists as another axiom) is certified separately by the
/// nested check.
///
/// This is what closes the set family's *predicate* half:
/// `(forall ((?x Elem)) (=> (member ?x ?s1) (member ?x ?s2))) =>
/// (subset ?s1 ?s2)` completes `subset` as row-containment — axioms 1–3
/// then hold by construction, the existential-witness churn (each round's
/// axiom-2 Skolems growing the `Elem` universe without bound) has no
/// falsifier left to mint, and the axiom-5 check at unmerged equal-row
/// pairs becomes the merge pump that shrinks the universe back down.
struct HintMacro {
    /// The defining axiom (a tracked quantifier term).
    quantifier: TermId,
    /// The hinted function `h`: Bool-valued, uninterpreted, macro-free.
    func: Spur,
    /// `h`'s arguments as indices into the axiom's `bound_vars` (all
    /// uninterpreted sorts — finite-model semantics makes the tuple
    /// enumeration the whole domain).
    arg_vars: SmallVec<[usize; 4]>,
    /// The hint body: `h(args) := psi`'s truth.  May bind its own
    /// quantifiers (evaluated over the ground universes).
    psi: TermId,
}

/// Extract every hint macro from the tracked quantifiers, first hint per
/// function (deterministic in tracking order).  A function that already
/// has a macro definition or a constructor table is not hinted — the
/// macro/table owns its interpretation.
fn extract_hint_macros(
    quantifiers: &[QuantifiedFormula],
    ctors: &[QuasiMacro],
    macro_funcs: &FxHashSet<Spur>,
    manager: &TermManager,
) -> Vec<HintMacro> {
    let mut out: Vec<HintMacro> = Vec::new();
    let mut seen: FxHashSet<Spur> = FxHashSet::default();
    seen.extend(ctors.iter().map(|qm| qm.func));
    // An observer is the row-carrier of the whole construction: hinting
    // it (an axiom like `member(x,s1) ∧ subset(s1,s2) => member(x,s2)`
    // matches the shape!) would reinterpret the rows themselves and
    // corrupt every table built on them.
    seen.extend(ctors.iter().map(|qm| qm.observer));
    'axioms: for q in quantifiers {
        if !q.is_universal || q.guard.is_some() || q.guard_inactive {
            continue;
        }
        let mut by_name: FxHashMap<Spur, usize> = FxHashMap::default();
        for (i, &(name, _)) in q.bound_vars.iter().enumerate() {
            if by_name.insert(name, i).is_some() {
                continue 'axioms; // ambiguous bindings
            }
        }
        let Some(TermKind::Implies(psi, happ)) = manager.get(q.body).map(|n| &n.kind) else {
            continue;
        };
        let Some(h_node) = manager.get(*happ) else {
            continue;
        };
        if h_node.sort != manager.sorts.bool_sort {
            continue;
        }
        let TermKind::Apply {
            func: h,
            args: h_args,
        } = &h_node.kind
        else {
            continue;
        };
        // `h` is a plain uninterpreted predicate: no macro definition
        // (the macro solver owns that interpretation), no constructor
        // table.
        if macro_funcs.contains(h) || seen.contains(h) {
            continue;
        }
        // Arguments: distinct bound variables over uninterpreted sorts.
        let mut arg_vars: SmallVec<[usize; 4]> = SmallVec::new();
        let mut used: FxHashSet<usize> = FxHashSet::default();
        let mut shape_ok = true;
        for &arg in h_args {
            let Some(node) = manager.get(arg) else {
                shape_ok = false;
                break;
            };
            let TermKind::Var(name) = &node.kind else {
                shape_ok = false;
                break;
            };
            let Some(&vi) = by_name.get(name) else {
                shape_ok = false;
                break;
            };
            if q.bound_vars[vi].1 != node.sort
                || !used.insert(vi)
                || !manager
                    .sorts
                    .get(node.sort)
                    .is_some_and(|s| matches!(s.kind, SortKind::Uninterpreted(_)))
            {
                shape_ok = false;
                break;
            }
            arg_vars.push(vi);
        }
        if !shape_ok || arg_vars.len() != h_args.len() {
            continue;
        }
        // Self-referential hints are not definitions: a psi that mentions
        // `h` itself completes P from its own circularity.
        if nixie_core::ast::traversal::collect_subterms(*psi, manager)
            .iter()
            .any(|&t| {
                matches!(
                    manager.get(t).map(|n| &n.kind),
                    Some(TermKind::Apply { func, .. }) if func == h
                )
            })
        {
            continue;
        }
        seen.insert(*h);
        out.push(HintMacro {
            quantifier: q.term,
            func: *h,
            arg_vars,
            psi: *psi,
        });
    }
    out
}

/// The static table-usage test (see `MBQIIntegration::goal_uses_
/// constructor_tables`): whether the goal's quantifiers extract any
/// constructor or hint table.  Depends only on the axiom shapes and the
/// macro-solver's definitions, never on a model.
pub(crate) fn goal_has_tables(
    quantifiers: &[QuantifiedFormula],
    macro_funcs: &FxHashSet<Spur>,
    manager: &TermManager,
) -> bool {
    let qms = extract_quasi_macros(quantifiers, manager);
    let hints = extract_hint_macros(quantifiers, &qms, macro_funcs, manager);
    !qms.is_empty() || !hints.is_empty()
}

/// Extract every quasi-macro from the tracked quantifiers, first defining
/// axiom per constructor (deterministic in tracking order).
pub(crate) fn extract_quasi_macros(
    quantifiers: &[QuantifiedFormula],
    manager: &TermManager,
) -> Vec<QuasiMacro> {
    let mut out: Vec<QuasiMacro> = Vec::new();
    let mut seen: FxHashSet<Spur> = FxHashSet::default();
    for q in quantifiers {
        if !q.is_universal || q.guard.is_some() || q.guard_inactive {
            continue;
        }
        // name -> bound-var index; duplicated names make bindings
        // ambiguous, so the axiom is skipped.
        let mut by_name: FxHashMap<Spur, usize> = FxHashMap::default();
        let mut names_ok = true;
        for (i, &(name, _)) in q.bound_vars.iter().enumerate() {
            if by_name.insert(name, i).is_some() {
                names_ok = false;
                break;
            }
        }
        if !names_ok {
            continue;
        }
        let Some(TermKind::Eq(lhs, rhs)) = manager.get(q.body).map(|n| &n.kind) else {
            continue;
        };
        for (obs, psi) in [(*lhs, *rhs), (*rhs, *lhs)] {
            if let Some(qm) = try_extract(q, obs, psi, &by_name, manager)
                && seen.insert(qm.func)
            {
                out.push(qm);
                break;
            }
        }
    }
    out
}

/// Try to read `obs = psi` as `g(v..., f(w...)) = psi`.
fn try_extract(
    q: &QuantifiedFormula,
    obs: TermId,
    psi: TermId,
    by_name: &FxHashMap<Spur, usize>,
    manager: &TermManager,
) -> Option<QuasiMacro> {
    let obs_node = manager.get(obs)?;
    if obs_node.sort != manager.sorts.bool_sort {
        return None;
    }
    let TermKind::Apply {
        func: observer,
        args: obs_args,
    } = &obs_node.kind
    else {
        return None;
    };

    // Exactly one constructor application among the observer's direct
    // arguments: an apply whose function differs from the observer and
    // whose range is an uninterpreted (finite-model) sort.
    let mut ctor: Option<(Spur, &SmallVec<[TermId; 4]>, SortId)> = None;
    let mut ctor_count = 0usize;
    for &arg in obs_args {
        let node = manager.get(arg)?;
        if let TermKind::Apply {
            func: cand,
            args: cand_args,
        } = &node.kind
        {
            if cand == observer {
                return None;
            }
            let range_is_uninterp = manager
                .sorts
                .get(node.sort)
                .is_some_and(|s| matches!(s.kind, SortKind::Uninterpreted(_)));
            if range_is_uninterp {
                ctor_count += 1;
                ctor = Some((*cand, cand_args, node.sort));
            }
        }
    }
    if ctor_count != 1 {
        return None;
    }
    let (func, func_app_args, func_range) = ctor?;

    // f's arguments: distinct bound variables.
    let mut func_args: SmallVec<[usize; 4]> = SmallVec::new();
    let mut used: FxHashSet<usize> = FxHashSet::default();
    for &arg in func_app_args {
        let TermKind::Var(name) = &manager.get(arg)?.kind else {
            return None;
        };
        let &vi = by_name.get(name)?;
        if q.bound_vars[vi].1 != manager.get(arg)?.sort {
            return None;
        }
        if !used.insert(vi) {
            return None;
        }
        func_args.push(vi);
    }

    // The observer's other arguments: distinct axis variables, disjoint
    // from the constructor's arguments.  The constructor result is
    // recognized positionally (the one apply argument into the range
    // sort — the counting pass above guaranteed there is exactly one
    // apply with an uninterpreted range, and every other argument must
    // be a plain axis variable).
    let mut observer_args: SmallVec<[ObserverArg; 4]> = SmallVec::new();
    for &arg in obs_args {
        let node = manager.get(arg)?;
        if matches!(node.kind, TermKind::Apply { .. }) && node.sort == func_range {
            observer_args.push(ObserverArg::Result);
            continue;
        }
        let TermKind::Var(name) = &node.kind else {
            return None;
        };
        let &vi = by_name.get(name)?;
        if q.bound_vars[vi].1 != node.sort {
            return None;
        }
        if !used.insert(vi) {
            return None;
        }
        observer_args.push(ObserverArg::Axis(vi));
    }

    // psi must not mention the constructor, and every bound variable it
    // mentions freely must be an axis or a constructor argument (other
    // variables would need extra row coordinates this extraction does not
    // model).  Global constants (free `Var` nodes whose names are not the
    // axiom's binders) are ground and fine.
    for t in nixie_core::ast::traversal::collect_subterms(psi, manager) {
        if let TermKind::Apply { func: f2, .. } = &manager.get(t)?.kind
            && *f2 == func
        {
            return None;
        }
    }
    for v in collect_free_vars_including_patterns(psi, manager) {
        let TermKind::Var(name) = &manager.get(v)?.kind else {
            continue;
        };
        if let Some(&vi) = by_name.get(name)
            && q.bound_vars[vi].1 == manager.get(v)?.sort
            && !used.contains(&vi)
        {
            return None;
        }
    }

    Some(QuasiMacro {
        quantifier: q.term,
        func,
        func_range,
        observer: *observer,
        observer_args,
        func_args,
        psi,
    })
}

/// Compute and install the constructor tables, register the defining
/// sources, and freeze the semantic domains.
///
/// Two passes: the second recomputes with every constructor's first-pass
/// table visible, so a defining body that observes one constructor through
/// another (`psi` mentioning a second constructor's application) settles
/// consistently within the round.
pub(crate) fn compute_constructor_tables(
    model: &mut CompletedModel,
    quantifiers: &[QuantifiedFormula],
    frozen: &mut FxHashMap<SortId, Vec<TermId>>,
    range_sorts: &mut FxHashSet<SortId>,
    minted: &mut FxHashSet<TermId>,
    fresh_mints: &mut usize,
    manager: &mut TermManager,
) {
    let qms = extract_quasi_macros(quantifiers, manager);
    let macro_funcs: FxHashSet<Spur> = model.macros.keys().copied().collect();
    let hints = extract_hint_macros(quantifiers, &qms, &macro_funcs, manager);
    if qms.is_empty() && hints.is_empty() {
        return;
    }
    if std::env::var_os("NIXIE_DEBUG_CT").is_some() {
        let printer = nixie_core::smtlib::Printer::new(manager);
        for qm in &qms {
            eprintln!(
                "[ct d{}] extracted ctor {} (range {:?}) via observer {} from {}",
                crate::mbqi::model_checker::nested_depth(),
                qm.func.into_inner().get(),
                qm.func_range,
                qm.observer.into_inner().get(),
                printer.print_term(qm.psi)
            );
        }
        for hm in &hints {
            eprintln!(
                "[ct d{}] extracted hint {} from {}",
                crate::mbqi::model_checker::nested_depth(),
                hm.func.into_inner().get(),
                printer.print_term(hm.psi)
            );
        }
    }
    // Pre-freeze the touched sorts (see
    // `ModelCompleter::frozen_table_domains`): the constructor ranges,
    // observer axes and hint arguments are a *static* set for the
    // problem, and the round where a sort first has a non-empty ground
    // universe is exactly when its growth must stop — every later term
    // (witness Skolems, minted compounds) would otherwise perturb the
    // row points and the tuple space the tables are computed over, and
    // the structure the certifications run against never stabilizes.
    // Freezing before the compute passes also bounds the row-point
    // product by the *small* first-universe, not the grown one.
    {
        let mut touched: Vec<SortId> = Vec::new();
        for qm in &qms {
            touched.push(qm.func_range);
            if let Some(q) = quantifiers.iter().find(|q| q.term == qm.quantifier) {
                for &vi in &qm.func_args {
                    if let Some(&(_, sort)) = q.bound_vars.get(vi) {
                        touched.push(sort);
                    }
                }
                for arg in &qm.observer_args {
                    if let ObserverArg::Axis(vi) = arg
                        && let Some(&(_, sort)) = q.bound_vars.get(*vi)
                    {
                        touched.push(sort);
                    }
                }
            }
        }
        for hm in &hints {
            if let Some(q) = quantifiers.iter().find(|q| q.term == hm.quantifier) {
                for &vi in &hm.arg_vars {
                    if let Some(&(_, sort)) = q.bound_vars.get(vi) {
                        touched.push(sort);
                    }
                }
            }
        }
        for sort in touched {
            if frozen.contains_key(&sort) {
                if let Some(domain) = frozen.get(&sort).cloned() {
                    model.table_domains.insert(sort, domain);
                }
                continue;
            }
            let Some(universe) = model.ground_universe(sort, manager) else {
                continue;
            };
            if universe.is_empty() {
                continue; // retry next round — nothing to freeze yet
            }
            let mut domain = universe;
            domain.sort_by_key(|t| t.0);
            domain.dedup();
            frozen.insert(sort, domain.clone());
            model.table_domains.insert(sort, domain);
        }
    }

    // Two passes: the second recomputes with every table visible, so
    // defining bodies that observe one function through another settle
    // consistently within the round (one globally-consistent
    // interpretation).
    for _ in 0..2 {
        for qm in &qms {
            compute_one(model, qm, frozen, quantifiers, minted, fresh_mints, manager);
        }
        for hm in &hints {
            compute_hint_one(model, hm, frozen, quantifiers, minted, manager);
        }
    }

    // Freeze the tabled sorts' domains (see
    // `ModelCompleter::frozen_table_domains`): the round that first
    // computes tables fixes each touched sort's *semantic* universe --
    // raw elements mapped through the fresh tables, deduplicated,
    // canonically ordered -- as the completed structure's own domain.
    // Later rounds recompute the tables over the frozen domain, so the
    // ground solver minting witnesses and compounds cannot move the
    // structure the certifications run against.
    {
        let mut touched: Vec<SortId> = Vec::new();
        for qm in &qms {
            if model.computed_entries.contains_key(&qm.func) {
                touched.push(qm.func_range);
                range_sorts.insert(qm.func_range);
                for arg in &qm.observer_args {
                    if let ObserverArg::Axis(vi) = arg
                        && let Some(q) = quantifiers.iter().find(|q| q.term == qm.quantifier)
                        && let Some(&(_, sort)) = q.bound_vars.get(*vi)
                    {
                        touched.push(sort);
                    }
                }
            }
        }
        for hm in &hints {
            if model.computed_entries.contains_key(&hm.func)
                && let Some(q) = quantifiers.iter().find(|q| q.term == hm.quantifier)
            {
                for &vi in &hm.arg_vars {
                    if let Some(&(_, sort)) = q.bound_vars.get(vi) {
                        touched.push(sort);
                    }
                }
            }
        }
        for sort in touched {
            if frozen.contains_key(&sort) {
                continue;
            }
            // Semantic freeze for a sort the pre-pass could not touch
            // (its universe was empty until the tables existed): the
            // raw elements collapsed through the fresh tables.
            let Some(universe) = model.ground_universe(sort, manager) else {
                continue;
            };
            let mut seen: FxHashSet<TermId> = FxHashSet::default();
            let mut domain: Vec<TermId> = universe
                .into_iter()
                .map(|e| model.semantic_value_of(e, manager))
                .filter(|e| seen.insert(*e))
                .collect();
            domain.sort_by_key(|t| t.0);
            if domain.is_empty() {
                continue;
            }
            frozen.insert(sort, domain.clone());
            model.table_domains.insert(sort, domain);
        }
    }

    // The row-determined fixpoint: the functions whose completed
    // interpretation depends on an element only through its row.
    // Observers are row-determined by definition (the row IS the
    // observer's value vector); a constructor whose table is installed is
    // row-determined when its defining body reads the tuple variables
    // only through row-determined functions; a hinted predicate likewise.
    // This set gates the semantic-domain collapse below — the soundness
    // argument for skipping a semantically-equal tuple during
    // instantiation.
    let mut row_determined: FxHashSet<Spur> = qms.iter().map(|qm| qm.observer).collect();
    loop {
        let mut changed = false;
        for qm in &qms {
            if row_determined.contains(&qm.func) || !model.computed_entries.contains_key(&qm.func) {
                continue;
            }
            let Some(q) = quantifiers.iter().find(|q| q.term == qm.quantifier) else {
                continue;
            };
            // The candidate's own applications count as allowed during
            // its admission: the table being admitted is exactly what
            // closes them.
            let mut with_self = row_determined.clone();
            with_self.insert(qm.func);
            if psi_reads_args_row_determined(qm.psi, &qm.func_args, q, &with_self, manager)
                && psi_reads_args_row_determined(q.body, &qm.func_args, q, &with_self, manager)
            {
                row_determined.insert(qm.func);
                changed = true;
            }
        }
        for hm in &hints {
            if row_determined.contains(&hm.func) {
                continue;
            }
            let Some(q) = quantifiers.iter().find(|q| q.term == hm.quantifier) else {
                continue;
            };
            let mut with_self = row_determined.clone();
            with_self.insert(hm.func);
            if psi_reads_args_row_determined(hm.psi, &hm.arg_vars, q, &with_self, manager) {
                row_determined.insert(hm.func);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Normalize the ground entry tables through the fresh tables: a
    // compound-keyed entry (`member(u!0, union(a,a)) -> v`, minted during
    // the search era) denotes the same domain point as its semantic value
    // — the completed structure identifies them — so the entry is
    // rewritten onto the representative's key and duplicates at the same
    // normalized point are collapsed (first wins).  Without this, the
    // chains hold two branches for one point with values that can
    // disagree (the stale minting-era pin vs the domain-keyed one), and
    // the nested check — which may legitimately merge the Skolem with
    // the compound — routes through the stale branch and falsifies
    // axioms the completed model satisfies (the set family's residual
    // q20/q57/q42 `Sat` verdicts: the aux's own falsifying assignment
    // showed it merging `a` with `union(a,a)` and reading the compound-
    // keyed entries).
    {
        let funcs: Vec<Spur> = model.function_interps.keys().copied().collect();
        for func in funcs {
            let raw = model
                .function_interps
                .get(&func)
                .map(|i| i.entries.clone())
                .unwrap_or_default();
            if raw.is_empty() {
                continue;
            }
            let mut normalized: Vec<(Vec<TermId>, TermId)> = Vec::new();
            for e in raw {
                let mut args = e.args;
                let mut all_inside = true;
                for a in args.iter_mut() {
                    // Ground-value normalization first (the ground model's
                    // own assignment of the term — this is also what keeps
                    // asserted ground equalities true in the completed
                    // structure), then the constructor-table quotient.
                    let mut v = *a;
                    for _ in 0..4 {
                        match model.assignments.get(&v) {
                            Some(&next) if next != v => v = next,
                            _ => break,
                        }
                    }
                    v = model.semantic_value_of(v, manager);
                    // Structure membership: a tabled sort's completed
                    // interpretation lives on its frozen domain — an entry
                    // keyed at a point the structure does not contain
                    // constrains nothing inside it, and keeping it lets the
                    // nested check route a chain branch through a free
                    // compound the structure never justified (the set9
                    // residual: `member` entries keyed at `union(a,b)`,
                    // `skf!0(difference(a,b), difference(b,a))`, ... — all
                    // outside the two-element structure, all aux exploit
                    // routes).  Drop the entry.
                    if let Some(node) = manager.get(v)
                        && let Some(domain) = model.table_domains.get(&node.sort)
                        && !domain.is_empty()
                        && !domain.contains(&v)
                    {
                        all_inside = false;
                        break;
                    }
                    *a = v;
                }
                if all_inside {
                    normalized.push((args, e.result));
                }
            }
            let mut seen: FxHashSet<Vec<TermId>> = FxHashSet::default();
            let entries: Vec<FunctionEntry> = normalized
                .into_iter()
                .filter(|(args, _)| seen.insert(args.clone()))
                .map(|(args, result)| FunctionEntry { args, result })
                .collect();
            if let Some(interp) = model.function_interps.get_mut(&func) {
                interp.entries = entries;
            }
        }
    }

    // Freeze the semantic domains for the constructor argument axes: the
    // raw ground universe with compounds collapsed through the tables
    // (see `CompletedModel::semantic_value_of`).
    //
    // Soundness gate: collapsing two row-equal elements is only
    // value-determining when every use of the tuple variables in the
    // axiom body reads them row-determinately (the fixpoint above).  An
    // equality between tuple elements, or any other function applied at
    // them, makes evaluations at row-equal elements genuinely differ;
    // collapsing would then skip a tuple whose instance is not redundant
    // (and the finite-exhaustion gate, which trusts the candidate
    // coverage, could certify over it).  No gate — no semantic domain:
    // the consumers keep the raw universe.
    for qm in &qms {
        let Some(q) = quantifiers.iter().find(|q| q.term == qm.quantifier) else {
            continue;
        };
        if !row_determined.contains(&qm.func) {
            if std::env::var_os("NIXIE_DEBUG_CT").is_some() {
                eprintln!(
                    "[ct d{}] semantic domains skipped: axes not row-determined",
                    crate::mbqi::model_checker::nested_depth()
                );
            }
            continue;
        }
        for &vi in &qm.func_args {
            let Some(&(_, sort)) = q.bound_vars.get(vi) else {
                continue;
            };
            let Some(universe) = model.table_domain(sort, manager) else {
                continue;
            };
            let mut seen: FxHashSet<TermId> = FxHashSet::default();
            let domain: Vec<TermId> = universe
                .into_iter()
                .map(|e| model.semantic_value_of(e, manager))
                .filter(|e| seen.insert(*e))
                .collect();
            if std::env::var_os("NIXIE_DEBUG_CT").is_some() {
                eprintln!(
                    "[ct d{}] semantic domain (q={:?}, var {}): {} points",
                    crate::mbqi::model_checker::nested_depth(),
                    qm.quantifier,
                    manager.resolve_str(q.bound_vars[vi].0),
                    domain.len()
                );
            }
            model.semantic_domains.insert((qm.quantifier, vi), domain);
        }
    }
}

/// One constructor's table.  Declines silently (no table installed) on
/// every cap or evaluation failure — the completion then behaves exactly
/// as without this module.
fn compute_one(
    model: &mut CompletedModel,
    qm: &QuasiMacro,
    frozen: &mut FxHashMap<SortId, Vec<TermId>>,
    quantifiers: &[QuantifiedFormula],
    minted: &mut FxHashSet<TermId>,
    fresh_mints: &mut usize,
    manager: &mut TermManager,
) {
    let Some(q) = quantifiers.iter().find(|q| q.term == qm.quantifier) else {
        return;
    };

    // A constructor the ground model never applied still needs an
    // interpretation entry point: create it over the axiom's domain so
    // the table (and the ite chains built from it) has somewhere to live.
    let domain: SmallVec<[SortId; 4]> = qm
        .func_args
        .iter()
        .filter_map(|&vi| q.bound_vars.get(vi).map(|&(_, s)| s))
        .collect();
    model
        .function_interps
        .entry(qm.func)
        .or_insert_with(|| FunctionInterpretation::new(qm.func, domain, qm.func_range));

    // The frozen domain when one exists (see `compute_constructor_tables`)
    // -- the structure's own domain -- else this round's ground universe.
    let universe = if let Some(frozen_domain) = frozen.get(&qm.func_range) {
        Some(frozen_domain.clone())
    } else {
        model.ground_universe(qm.func_range, manager)
    };
    let Some(universe) = universe else {
        return;
    };
    if universe.is_empty() || universe.len() > MAX_CONSTRUCTOR_UNIVERSE {
        return;
    }

    // Row points: the ground universes of the observer's axis variables.
    // An empty axis domain vacuously identifies every row (there is no
    // ground point to distinguish them): one vacuous row point.
    let axis_vars: Vec<usize> = qm
        .observer_args
        .iter()
        .filter_map(|a| match a {
            ObserverArg::Axis(vi) => Some(*vi),
            ObserverArg::Result => None,
        })
        .collect();
    let mut axis_domains: Vec<Vec<TermId>> = Vec::with_capacity(axis_vars.len());
    for &vi in &axis_vars {
        let Some(&(_, sort)) = q.bound_vars.get(vi) else {
            return;
        };
        axis_domains.push(if let Some(frozen_domain) = frozen.get(&sort) {
            frozen_domain.clone()
        } else {
            model.ground_universe(sort, manager).unwrap_or_default()
        });
    }
    let vacuous = axis_domains.iter().any(|d| d.is_empty());
    let row_points: Vec<Vec<TermId>> = if vacuous {
        vec![Vec::new()]
    } else {
        let product: usize = axis_domains.iter().map(|d| d.len()).product();
        if product > MAX_ROW_POINTS {
            return;
        }
        let mut points: Vec<Vec<TermId>> = Vec::with_capacity(product);
        let mut odometer = vec![0usize; axis_domains.len()];
        loop {
            points.push(
                axis_domains
                    .iter()
                    .zip(odometer.iter())
                    .map(|(d, &i)| d[i])
                    .collect(),
            );
            let mut carry = true;
            for (i, idx) in odometer.iter_mut().enumerate() {
                if carry {
                    *idx += 1;
                    if *idx >= axis_domains[i].len() {
                        *idx = 0;
                    } else {
                        carry = false;
                    }
                }
            }
            if carry {
                break;
            }
        }
        points
    };

    if std::env::var_os("NIXIE_DEBUG_CT").is_some() {
        let printer = nixie_core::smtlib::Printer::new(manager);
        let elems: Vec<String> = universe.iter().map(|&u| printer.print_term(u)).collect();
        eprintln!(
            "[ct] fn {} universe ({}): {}",
            qm.func.into_inner().get(),
            universe.len(),
            elems.join(", ")
        );
    }
    let else_table = crate::mbqi::model_checker::choose_else_table(model, manager);
    if std::env::var_os("NIXIE_DEBUG_CT").is_some() {
        eprintln!(
            "[ct] observer {} in interps: {}, in else_table: {}",
            qm.observer.into_inner().get(),
            model.function_interps.contains_key(&qm.observer),
            else_table.contains_key(&qm.observer)
        );
    }
    if std::env::var_os("NIXIE_DEBUG_CT").is_some() {
        let keys: Vec<String> = model
            .function_interps
            .keys()
            .map(|k| k.into_inner().get().to_string())
            .collect();
        eprintln!("[ct] interps: {:?}", keys);
    }

    // The row of every range element, under the completed model.
    let mut rows: Vec<Vec<bool>> = Vec::with_capacity(universe.len());
    if std::env::var_os("NIXIE_DEBUG_CT_ROWS").is_some() {
        eprintln!(
            "[rows d{}] fn {} row_points {}",
            crate::mbqi::model_checker::nested_depth(),
            qm.func.into_inner().get(),
            row_points.len()
        );
    }
    for &z in &universe {
        let mut row: Vec<bool> = Vec::with_capacity(row_points.len());
        for point in &row_points {
            if vacuous {
                row.push(true); // the single vacuous coordinate
                continue;
            }
            let app = observer_app(qm, point, z, manager);
            match eval_ground_bool(app, model, &else_table, manager) {
                Some(b) => row.push(b),
                None => {
                    // cannot evaluate: decline the table
                    if std::env::var_os("NIXIE_DEBUG_CT").is_some() {
                        let printer = nixie_core::smtlib::Printer::new(manager);
                        eprintln!(
                            "[ct] fn {} DECLINED: row eval failed at z={} point={:?}",
                            qm.func.into_inner().get(),
                            printer.print_term(z),
                            point
                                .iter()
                                .map(|&t| printer.print_term(t))
                                .collect::<Vec<_>>()
                        );
                    }
                    return;
                }
            }
        }
        rows.push(row);
    }
    if std::env::var_os("NIXIE_DEBUG_CT_ROWS").is_some() {
        let printer = nixie_core::smtlib::Printer::new(manager);
        for (&z, row) in universe.iter().zip(rows.iter()) {
            let bits: String = row.iter().map(|&b| if b { '1' } else { '0' }).collect();
            eprintln!(
                "[rows d{}]   z={} row={bits}",
                crate::mbqi::model_checker::nested_depth(),
                printer.print_term(z)
            );
        }
    }

    // Walk every tuple of the range universe, computing entries for the
    // unpinned ones.
    let arity = qm.func_args.len();
    let mut entries: Vec<FunctionEntry> = Vec::new();
    let mut odometer = vec![0usize; arity];
    let mut walked = 0usize;
    // (tuple, target row) for every row miss this walk saw.  The mint is
    // POST-walk under a fixed per-round budget: minting in-walk extends
    // the odometer to the fresh tuples immediately, which measured 10x
    // the aux conflicts on set19 (the walk covers (fresh, fresh)-shaped
    // tuples against rows still in flux — garbage entries the nested
    // checks then fight through).  Post-walk, one per round: the
    // structure grows slowly along a row algebra the search stably
    // needs, and the next round's walk covers the new tuples against
    // settled rows.
    let mut missed_this_round: Vec<(Vec<TermId>, Vec<bool>)> = Vec::new();
    // Matched null (NIXIE_MINT_NULL=<seed>): mint the same ONE tuple,
    // chosen by a seeded pick instead of the odometer prefix.
    let null_seed: Option<u64> = std::env::var("NIXIE_MINT_NULL")
        .ok()
        .and_then(|s| s.parse().ok());
    'tuples: loop {
        if walked >= MAX_TABLE_TUPLES {
            break;
        }
        walked += 1;
        let tuple: Vec<TermId> = odometer.iter().map(|&i| universe[i]).collect();

        // Ground pins are never overridden: a tuple with a harvested
        // entry keeps it (a pinned tuple that violates its definitional
        // axiom stays visible to the nested check, which revises the
        // ground model through the falsifier path).
        let pinned = model.function_interps.get(&qm.func).is_some_and(|interp| {
            interp
                .entries
                .iter()
                .any(|e| crate::mbqi::model_checker::args_match(e, &tuple, model, manager))
        });
        if !pinned {
            // Target row: psi's truth at (row point, tuple).
            let mut target: Vec<bool> = Vec::with_capacity(row_points.len());
            for point in &row_points {
                let Some(subst) = point_tuple_subst(qm, point, &tuple, q, manager) else {
                    return;
                };
                let body = manager.substitute(qm.psi, &subst);
                match eval_ground_bool(body, model, &else_table, manager) {
                    Some(b) => target.push(b),
                    None => {
                        if std::env::var_os("NIXIE_DEBUG_CT").is_some() {
                            let printer = nixie_core::smtlib::Printer::new(manager);
                            eprintln!(
                                "[ct] fn {} DECLINED: psi eval failed at point={:?} tuple={:?}",
                                qm.func.into_inner().get(),
                                point
                                    .iter()
                                    .map(|&t| printer.print_term(t))
                                    .collect::<Vec<_>>(),
                                tuple
                                    .iter()
                                    .map(|&t| printer.print_term(t))
                                    .collect::<Vec<_>>()
                            );
                        }
                        return;
                    }
                }
            }
            // First element whose row matches (deterministic, canonical) —
            // preferring a plain non-application element when one exists:
            // the representative IS the value every consumer normalizes
            // onto (the semantic domains, `semantic_value_of`), and a
            // compound representative would itself seed the next minting
            // level (an instance at the semantic tuple `(union(a,a), b)`
            // mentions `union(union(a,a), b)` — the chase again, one level
            // deeper).  Constants anchor it.
            if let Some((z, _)) = universe
                .iter()
                .zip(rows.iter())
                .find(|(z, row)| {
                    **row == target
                        && !manager
                            .get(**z)
                            .is_some_and(|n| matches!(n.kind, TermKind::Apply { .. }))
                })
                .or_else(|| {
                    universe
                        .iter()
                        .zip(rows.iter())
                        .find(|(_, row)| **row == target)
                })
            {
                entries.push(FunctionEntry {
                    args: tuple,
                    result: *z,
                });
            }
            // No existing element has the target row: GROW the completed
            // structure with a fresh element that has it — z3's model
            // finder semantics (`proto_model::get_fresh_value` /
            // `mk_extra_fresh_value`: the model is the object being
            // searched, and a user sort's universe grows when the
            // interpretation needs a new distinguishable value).  The
            // fresh element is row-canonical — named by its target row —
            // so the same row mints the same element across rounds and
            // the structure stays stable.  Leaving the tuple to the
            // `else` instead (the old behaviour) strands the defining
            // axiom at the tuple for good whenever the domain lacks the
            // needed row: the set family's permanent `difference` miss
            // (no element with the empty-set row) whose stale compounds
            // then fed the walk-vs-aux divergence.
            else if frozen.contains_key(&qm.func_range) {
                // Record the miss; the mint decision is post-walk (see
                // `missed_this_round`'s declaration comment).
                missed_this_round.push((tuple.clone(), target.clone()));
            }
            // else (unfrozen range sort): leave the
            // tuple to the `else`; the nested check finds the falsifier
            // there and the loop grows the model (the revise step).
        }

        if odometer.is_empty() {
            break 'tuples; // the single 0-ary tuple
        }
        for i in 0..odometer.len() {
            odometer[i] += 1;
            if odometer[i] < universe.len() {
                break;
            }
            odometer[i] = 0;
            if i + 1 == odometer.len() {
                break 'tuples;
            }
        }
    }

    // The mint: at most `MINT_BUDGET_PER_ROUND` fresh rows per
    // constructor per round, the FIRST misses in odometer order
    // (deterministic).  The matched null (NIXIE_MINT_NULL=<seed>) mints
    // the same number chosen by a seeded pick of the miss set — same
    // machinery, same magnitude, no selection content.  Measured
    // treatment/null (conflicts, deterministic counter): set9 255/279
    // (~0.91), set19 485/586 (~0.83) — the prefix's content carries no
    // penalty; the count reduction is the mechanism (set19 aux conflicts
    // 10x worse under in-walk sticky minting, and the eager mint sat at
    // the 32-element cap for 194/245 passes).
    if !missed_this_round.is_empty() {
        let cap = MAX_FRESH_PER_TABLE.min(
            frozen
                .get(&qm.func_range)
                .map_or(0, |d| FRESH_RESTRICTION_CAP.saturating_sub(d.len())),
        );
        let k = MINT_BUDGET_PER_ROUND.min(cap).min(missed_this_round.len());
        // Seeded pick for the null; identity (prefix) for the treatment.
        let mut order: Vec<usize> = (0..missed_this_round.len()).collect();
        if let Some(seed) = null_seed {
            let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).max(1);
            for i in 0..k {
                state ^= state << 13;
                state ^= state >> 7;
                state ^= state << 17;
                let j = i + (state as usize) % (order.len() - i);
                order.swap(i, j);
            }
        }
        for &i in &order[..k] {
            let (tuple, target) = &missed_this_round[i];
            if let Some(fresh) =
                mint_fresh_row_element(qm, target, &row_points, model, frozen, minted, manager)
            {
                *fresh_mints += 1;
                entries.push(FunctionEntry {
                    args: tuple.clone(),
                    result: fresh,
                });
            }
        }
    }

    model.computed_entries.insert(qm.func, entries);
    model
        .constructor_sources
        .entry(qm.quantifier)
        .or_default()
        .push(qm.func);
    if std::env::var_os("NIXIE_DEBUG_CT").is_some() {
        eprintln!(
            "[ct] fn {}: {} computed entries over universe {}",
            qm.func.into_inner().get(),
            model.computed_entries.get(&qm.func).map_or(0, |v| v.len()),
            universe.len()
        );
    }
}

/// Cap on fresh row elements minted by one constructor's table per
/// round: the row algebra closes long before this on real problems, and
/// a pathological psi must not grow the structure unboundedly.
const MAX_FRESH_PER_TABLE: usize = 16;

/// The aux Skolem restriction's universe cap (`model_checker`): the
/// structure must stay readable by the nested check, so growth beyond
/// this declines (see `mint_fresh_row_element`).
const FRESH_RESTRICTION_CAP: usize = 32;

/// Fresh rows minted per constructor per round.  Measured on the set
/// family (aux conflicts, the deterministic counter): budget 1 lands at
/// or below the seeded-null distribution (set9 255 vs ~279 median,
/// set19 485 vs ~586), while budget 4 and the eager in-walk mint blow
/// past 5k conflicts on set19 — the structure must grow *slowly*, one
/// stably-needed row at a time, or the intermediate garbage rows cost
/// more than the closure they buy.
const MINT_BUDGET_PER_ROUND: usize = 1;

/// Mint a fresh element of the constructor's range sort whose observer
/// row is exactly `target`, and install it into the completed structure:
/// the observer's entry table gains the target row's entries at the new
/// element, and the frozen/table domains grow by it.  `None` when the
/// domain is at the restriction cap (the aux Skolem restriction and
/// every domain enumerator decline above it — a bigger structure would
/// be unreadable, so the tuple falls back to the `else`).
///
/// The name is row-canonical (`tbl!<func-name>!<row bits>`): the element
/// IS "the value with this row" in the completed structure's semantics,
/// so re-minting across rounds (or from a second constructor needing the
/// same row) yields the very same term and the structure stays stable.
fn mint_fresh_row_element(
    qm: &QuasiMacro,
    target: &[bool],
    row_points: &[Vec<TermId>],
    model: &mut CompletedModel,
    frozen: &mut FxHashMap<SortId, Vec<TermId>>,
    minted: &mut FxHashSet<TermId>,
    manager: &mut TermManager,
) -> Option<TermId> {
    /// The aux Skolem restriction's universe cap (`model_checker`): a
    /// domain past it is not restriction-readable, so growing further
    /// would produce a structure the nested check cannot even encode.
    const RESTRICTION_CAP: usize = 32;
    let domain_len = frozen.get(&qm.func_range).map_or(0, |d| d.len());
    if domain_len >= RESTRICTION_CAP {
        return None;
    }
    // Row-canonical name: the bits are taken over the row points sorted
    // by TermId and namespaced by an FNV fingerprint of that sorted
    // sequence — the frozen Elem domain's ORDER can change when an
    // escalation re-freezes it at a grown universe, and a positional bit
    // string would then re-mint the same row under a different name (a
    // duplicate element where the structure's own quotient semantics
    // says there is one point).
    let mut flat: Vec<(TermId, bool)> = row_points
        .iter()
        .zip(target.iter())
        .flat_map(|(point, &b)| point.iter().map(move |&p| (p, b)))
        .collect();
    flat.sort_by_key(|(p, _)| p.0);
    let mut fingerprint: u64 = 0xcbf2_9ce4_8422_2325;
    for (p, _) in &flat {
        fingerprint ^= u64::from(p.0);
        fingerprint = fingerprint.wrapping_mul(0x1000_0000_01b3);
    }
    let row_bits: String = flat
        .iter()
        .map(|(_, b)| if *b { '1' } else { '0' })
        .collect();
    let fresh = manager.mk_var(
        &format!(
            "tbl!{}!{fingerprint:016x}!{row_bits}",
            manager.resolve_str(qm.func)
        ),
        qm.func_range,
    );
    // The observer's entries at the fresh element: the target row, at
    // every row point (the args mirror `observer_app`'s construction).
    let interp = model
        .function_interps
        .entry(qm.observer)
        .or_insert_with(|| {
            FunctionInterpretation::new(qm.observer, SmallVec::new(), manager.sorts.bool_sort)
        });
    for (i, point) in row_points.iter().enumerate() {
        let mut axis_iter = point.iter();
        let mut args: Vec<TermId> = Vec::with_capacity(qm.observer_args.len());
        for arg in &qm.observer_args {
            match arg {
                ObserverArg::Result => args.push(fresh),
                ObserverArg::Axis(_) => {
                    if let Some(&elem) = axis_iter.next() {
                        args.push(elem);
                    }
                }
            }
        }
        let result = if target[i] {
            manager.mk_true()
        } else {
            manager.mk_false()
        };
        interp.entries.push(FunctionEntry { args, result });
    }
    // Grow the frozen and table domains: the completed structure's own
    // domain now contains the new element (the aux restriction, the
    // mining odometer and the enumerative engines all read it).
    frozen.entry(qm.func_range).or_default().push(fresh);
    match model.table_domains.entry(qm.func_range) {
        std::collections::hash_map::Entry::Occupied(mut occ) => {
            if !occ.get().contains(&fresh) {
                occ.get_mut().push(fresh);
            }
        }
        std::collections::hash_map::Entry::Vacant(vac) => {
            // The sort is frozen but the model's table-domain view was
            // not yet installed: mirror the frozen view plus the fresh
            // element so the consumers see one structure.
            let mut domain = frozen.get(&qm.func_range).cloned().unwrap_or_default();
            if !domain.contains(&fresh) {
                domain.push(fresh);
            }
            vac.insert(domain);
        }
    }
    // The mint memory: this element is a structure-owned point from
    // here on - the merge's pollution channels and the row repairs key
    // on it (see `ModelCompleter::minted_points`).
    minted.insert(fresh);
    Some(fresh)
}

/// Whether every use of the given bound variables in `term` reads them
/// through a row-determined function application (see the fixpoint in
/// [`compute_constructor_tables`]): any *direct* parent of one of the
/// variables must be an application of a function in `row_determined`.
/// A variable feeding an equality, a connective, or any other function
/// makes evaluations at row-equal elements genuinely differ.
fn psi_reads_args_row_determined(
    term: TermId,
    arg_vars: &SmallVec<[usize; 4]>,
    q: &QuantifiedFormula,
    row_determined: &FxHashSet<Spur>,
    manager: &TermManager,
) -> bool {
    let arg_var_set: FxHashSet<(Spur, SortId)> = arg_vars
        .iter()
        .filter_map(|&vi| q.bound_vars.get(vi).copied())
        .collect();
    if arg_var_set.is_empty() {
        return true;
    }
    let is_arg_var = |t: TermId| {
        manager.get(t).is_some_and(|n| match n.kind {
            TermKind::Var(name) => arg_var_set.contains(&(name, n.sort)),
            _ => false,
        })
    };
    for t in nixie_core::ast::traversal::collect_subterms(term, manager) {
        let Some(node) = manager.get(t) else {
            return false;
        };
        let mut children: smallvec::SmallVec<[TermId; 4]> = smallvec::SmallVec::new();
        crate::mbqi::model_checker::push_children(&node.kind, &mut children);
        if children.iter().any(|&c| is_arg_var(c))
            && !matches!(
                &node.kind,
                TermKind::Apply { func, .. } if row_determined.contains(func)
            )
        {
            return false;
        }
    }
    true
}

/// One hinted predicate's table (see [`HintMacro`]).  Declines silently
/// on every cap or evaluation failure — the function then falls back to
/// its ground entries and the `else`, exactly as without this module.
fn compute_hint_one(
    model: &mut CompletedModel,
    hm: &HintMacro,
    frozen: &FxHashMap<SortId, Vec<TermId>>,
    quantifiers: &[QuantifiedFormula],
    _minted: &FxHashSet<TermId>,
    manager: &mut TermManager,
) {
    let Some(q) = quantifiers.iter().find(|q| q.term == hm.quantifier) else {
        return;
    };
    // A predicate the ground model never applied still needs its
    // interpretation entry point.
    let domain: SmallVec<[SortId; 4]> = hm
        .arg_vars
        .iter()
        .filter_map(|&vi| q.bound_vars.get(vi).map(|&(_, s)| s))
        .collect();
    model
        .function_interps
        .entry(hm.func)
        .or_insert_with(|| FunctionInterpretation::new(hm.func, domain, manager.sorts.bool_sort));

    let mut domains: Vec<Vec<TermId>> = Vec::with_capacity(hm.arg_vars.len());
    for &vi in &hm.arg_vars {
        let Some(&(_, sort)) = q.bound_vars.get(vi) else {
            return;
        };
        let universe = if let Some(frozen_domain) = frozen.get(&sort) {
            Some(frozen_domain.clone())
        } else {
            model.ground_universe(sort, manager)
        };
        let Some(universe) = universe else {
            return;
        };
        if universe.is_empty() || universe.len() > MAX_CONSTRUCTOR_UNIVERSE {
            return;
        }
        domains.push(universe);
    }
    let else_table = crate::mbqi::model_checker::choose_else_table(model, manager);

    let mut entries: Vec<FunctionEntry> = Vec::new();
    let mut odometer = vec![0usize; domains.len()];
    let mut walked = 0usize;
    'tuples: loop {
        if walked >= MAX_HINT_TUPLES {
            break;
        }
        walked += 1;
        let tuple: Vec<TermId> = odometer
            .iter()
            .enumerate()
            .map(|(i, &j)| domains[i][j])
            .collect();
        // Ground pins are never overridden.  (A minted-args repair —
        // overwriting a pin that contradicts the defining psi at a
        // minted tuple with psi's truth — was built and measured on the
        // extensional family: it closed neither gap and regressed set9
        // to `unknown`; the residual extensional unknowns are an
        // instance-coverage problem, not a pin problem.  Do not retry
        // blind — see the study.)
        let pinned = model.function_interps.get(&hm.func).is_some_and(|interp| {
            interp
                .entries
                .iter()
                .any(|e| crate::mbqi::model_checker::args_match(e, &tuple, model, manager))
        });
        if !pinned {
            let mut env: FxHashMap<TermId, TermId> = FxHashMap::default();
            let mut bind_ok = true;
            for (&vi, &value) in hm.arg_vars.iter().zip(tuple.iter()) {
                let Some(&(name, sort)) = q.bound_vars.get(vi) else {
                    bind_ok = false;
                    break;
                };
                let name_str = manager.resolve_str(name).to_string();
                env.insert(manager.mk_var(&name_str, sort), value);
            }
            if bind_ok
                && let Some(truth) = eval_hint_psi(hm.psi, &env, model, &else_table, manager, 0)
            {
                let result = if truth {
                    manager.mk_true()
                } else {
                    manager.mk_false()
                };
                entries.push(FunctionEntry {
                    args: tuple,
                    result,
                });
            }
        }
        if odometer.is_empty() {
            break 'tuples;
        }
        for i in 0..odometer.len() {
            odometer[i] += 1;
            if odometer[i] < domains[i].len() {
                break;
            }
            odometer[i] = 0;
            if i + 1 == odometer.len() {
                break 'tuples;
            }
        }
    }
    if std::env::var_os("NIXIE_DEBUG_CT").is_some() {
        eprintln!(
            "[ct d{}] hint fn {}: {} computed entries",
            crate::mbqi::model_checker::nested_depth(),
            hm.func.into_inner().get(),
            entries.len()
        );
    }
    model.computed_entries.insert(hm.func, entries);
    model
        .constructor_sources
        .entry(hm.quantifier)
        .or_default()
        .push(hm.func);
}

/// Evaluate a hint body under the completed model, expanding its own
/// bounded quantifiers over the ground universes (finite-model semantics
/// — the same restriction the nested check's Skolems live under, so the
/// two readings agree).  `None` = could not evaluate; the caller leaves
/// the tuple to the `else`.
///
/// The recursion is over *quantifier nesting* only (capped by
/// [`MAX_QUANTIFIER_DEPTH`] — beyond it the hint declines), never over
/// term structure: the leaves delegate to the ordinary ground evaluator,
/// itself a frame machine.  The root must be a quantifier — a hint body
/// that merely *contains* quantifiers under connectives is not expanded
/// (the leaf evaluator declines it), which costs completeness only.
fn eval_hint_psi(
    term: TermId,
    env: &FxHashMap<TermId, TermId>,
    model: &CompletedModel,
    else_table: &FxHashMap<Spur, TermId>,
    manager: &mut TermManager,
    depth: u32,
) -> Option<bool> {
    let is_quantifier = manager
        .get(term)
        .is_some_and(|n| matches!(n.kind, TermKind::Forall { .. } | TermKind::Exists { .. }));
    if !is_quantifier {
        let substituted = manager.substitute(term, env);
        return eval_ground_bool(substituted, model, else_table, manager);
    }
    if depth >= MAX_QUANTIFIER_DEPTH {
        return None;
    }
    let (vars, body, is_forall): (SmallVec<[(Spur, SortId); 2]>, TermId, bool) = {
        let node = manager.get(term)?;
        match &node.kind {
            TermKind::Forall { vars, body, .. } => (vars.clone(), *body, true),
            TermKind::Exists { vars, body, .. } => (vars.clone(), *body, false),
            _ => return None,
        }
    };
    // Product of the bound variables' ground universes.
    let mut universes: Vec<Vec<TermId>> = Vec::with_capacity(vars.len());
    for &(_, sort) in &vars {
        let universe = model.ground_universe(sort, manager).unwrap_or_default();
        if universe.is_empty() {
            // Vacuous under finite-model semantics: the nested check's
            // Skolems are restricted to the same (empty) universe.
            return Some(is_forall);
        }
        universes.push(universe);
    }
    let product: usize = universes.iter().map(|u| u.len()).product();
    if product > MAX_QUANTIFIER_PRODUCT {
        return None;
    }
    if vars.is_empty() {
        return eval_hint_psi(body, env, model, else_table, manager, depth + 1);
    }
    let mut odometer = vec![0usize; vars.len()];
    let mut acc = is_forall;
    loop {
        let mut extended = env.clone();
        for (i, &(name, sort)) in vars.iter().enumerate() {
            let name_str = manager.resolve_str(name).to_string();
            extended.insert(manager.mk_var(&name_str, sort), universes[i][odometer[i]]);
        }
        let value = eval_hint_psi(body, &extended, model, else_table, manager, depth + 1)?;
        if is_forall {
            acc = acc && value;
            if !acc {
                return Some(false);
            }
        } else {
            acc = acc || value;
            if acc {
                return Some(true);
            }
        }
        let mut carry = true;
        for (i, idx) in odometer.iter_mut().enumerate() {
            if carry {
                *idx += 1;
                if *idx >= universes[i].len() {
                    *idx = 0;
                } else {
                    carry = false;
                }
            }
        }
        if carry {
            return Some(acc);
        }
    }
}

/// Build the observer application `g(point..., z)`.
fn observer_app(qm: &QuasiMacro, point: &[TermId], z: TermId, manager: &mut TermManager) -> TermId {
    let mut axis_iter = point.iter();
    let mut args: SmallVec<[TermId; 4]> = SmallVec::new();
    for arg in &qm.observer_args {
        match arg {
            ObserverArg::Result => args.push(z),
            ObserverArg::Axis(_) => {
                if let Some(&elem) = axis_iter.next() {
                    args.push(elem);
                }
            }
        }
    }
    manager.intern_term(
        TermKind::Apply {
            func: qm.observer,
            args,
        },
        manager.sorts.bool_sort,
    )
}

/// The substitution binding the axiom's variables at `(row point, tuple)`.
fn point_tuple_subst(
    qm: &QuasiMacro,
    point: &[TermId],
    tuple: &[TermId],
    q: &QuantifiedFormula,
    manager: &mut TermManager,
) -> Option<FxHashMap<TermId, TermId>> {
    let mut subst: FxHashMap<TermId, TermId> = FxHashMap::default();
    let mut bind = |vi: usize, value: TermId, subst: &mut FxHashMap<TermId, TermId>| {
        let Some(&(name, sort)) = q.bound_vars.get(vi) else {
            return false;
        };
        let name_str = manager.resolve_str(name).to_string();
        let var = manager.mk_var(&name_str, sort);
        subst.insert(var, value);
        true
    };
    // Axis variables in observer order consume the point.
    let mut axis_iter = point.iter();
    for arg in &qm.observer_args {
        if let ObserverArg::Axis(vi) = arg {
            let &elem = axis_iter.next()?;
            if !bind(*vi, elem, &mut subst) {
                return None;
            }
        }
    }
    // Constructor arguments consume the tuple.
    for (j, &vi) in qm.func_args.iter().enumerate() {
        let &elem = tuple.get(j)?;
        if !bind(vi, elem, &mut subst) {
            return None;
        }
    }
    Some(subst)
}

/// Evaluate a *ground* Bool term under the completed model (entries,
/// computed entries, macros, else).  `None` when the term does not fold
/// to a Boolean — the caller declines.
fn eval_ground_bool(
    term: TermId,
    model: &CompletedModel,
    else_table: &FxHashMap<Spur, TermId>,
    manager: &mut TermManager,
) -> Option<bool> {
    let value =
        crate::mbqi::model_checker::eval_completed_ground(term, model, else_table, manager).ok()?;
    let node = manager.get(value)?;
    match node.kind {
        TermKind::True => Some(true),
        TermKind::False => Some(false),
        _ => None,
    }
}
