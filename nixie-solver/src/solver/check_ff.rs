//! Eager whole-problem finite-field dispatch (`QF_FF`, Phase 3 of
//! `docs/FF_THEORY_DESIGN.md` §7): decides pure conjunctive goals by
//! handing every field's literal slice to
//! [`nixie_theories::ff_theory::check_conjunction`], modelled on
//! `dispatch_nl_solver`. Goals with Boolean structure beyond a
//! conjunction of literals are *declined* here (`None`) — the CDCL(T)
//! path takes them (Phase 4), and its honesty gate answers `Unknown`
//! for the FF atoms it does not own.

use crate::prelude::*;
use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::sort::SortKind;
use nixie_core::sort::field::FieldId;
use nixie_sat::{Lit, Solver as SatSolver, Var};
use nixie_theories::ff_theory::{FfOutcome, check_conjunction, validate_model};
use num_bigint::BigUint;

use super::Solver;
use super::types::{Model, SolverResult};

/// The FF dispatch's per-field step budget. A tick counter (encoding
/// steps, S-pairs, reductions, search nodes, root-finding work); never
/// wall-clock.
const FF_BUDGET_STEPS: u64 = 1 << 24;

impl Solver {
    /// Whether any assertion mentions finite-field structure.
    fn goal_uses_finite_fields(&self, manager: &TermManager) -> bool {
        self.assertions.iter().any(|&a| term_uses_ff(a, manager))
    }

    /// The set of distinct fields the assertions mention (a mixed-field
    /// goal checks each field's slice independently — no inference
    /// relates 𝔽_p and 𝔽_q).
    fn goal_fields(&self, manager: &TermManager) -> Vec<FieldId> {
        let mut fields: Vec<FieldId> = Vec::new();
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut stack: Vec<TermId> = self.assertions.clone();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            let Some(term) = manager.get(t) else {
                continue;
            };
            match &term.kind {
                TermKind::FfConst { field, .. } => {
                    if !fields.contains(field) {
                        fields.push(*field);
                    }
                }
                // A `QF_UFFF` application contributes exactly its RESULT
                // field. Its arguments may belong to other fields, whose
                // slices own them; descending here would pull the literal
                // into the wrong field's check.
                TermKind::Apply { .. } => {
                    if let Some(SortKind::FiniteField(id)) =
                        manager.sorts.get(term.sort).map(|s| s.kind.clone())
                        && !fields.contains(&id)
                    {
                        fields.push(id);
                    }
                }
                _ => {
                    stack.extend(nixie_core::ast::get_children(&term.kind));
                }
            }
        }
        fields.sort_by_key(|f| f.raw());
        fields
    }

    /// Decide a conjunctive `QF_FF` goal eagerly.
    ///
    /// Returns `None` when the goal is not this dispatcher's to answer:
    /// no FF structure, quantifiers present, or an assertion that is not
    /// (a conjunction of) FF literals — those fall through to CDCL(T),
    /// whose honesty gate keeps the answer `Unknown` until Phase 4.
    pub(super) fn dispatch_ff_solver(&mut self, manager: &mut TermManager) -> Option<SolverResult> {
        if !self.goal_uses_finite_fields(manager) {
            return None;
        }
        if self.has_quantifiers {
            return None;
        }
        // `QF_UFFF` (Phase 6 remainder): an uninterpreted application
        // with an FF result sort is not pure-FF structure — route the
        // whole goal to the polite-combination loop (FF ⊕ EUF), which
        // owns both the congruence reasoning and the arrangement search
        // over the shared FF-sorted terms. The pure paths below are
        // untouched.
        if goal_uses_ff_uf(&self.assertions, manager) {
            if self.goal_fields(manager).iter().any(|&f| {
                manager
                    .sorts
                    .field_desc(f)
                    .and_then(|d| d.binary())
                    .is_some()
            }) {
                return Some(SolverResult::Unknown);
            }
            return self.dpll_ufff(manager);
        }

        // Shape gate: every assertion must be built from FF atoms with
        // Boolean structure only (`and`/`or`/`not`/`ite`/`xor`/`=>`/
        // `distinct`, `=`, `true`/`false`). A foreign-theory leaf anywhere
        // declines the whole goal (the honesty gate answers `unknown`);
        // pure conjunctions take the fast path below; anything with real
        // Boolean structure goes to the lazy DPLL(T).
        let mut has_structure = false;
        for &a in &self.assertions {
            let term = manager.get(a)?;
            // A literal is exactly {true, false, `=`, `not =`} — anything
            // else (including `not (distinct ...)`, which is a
            // *disjunction* of equalities) is Boolean structure for the
            // DPLL(T) path.
            let is_literal = matches!(
                &term.kind,
                TermKind::True | TermKind::False | TermKind::Eq(_, _)
            ) || matches!(
                &term.kind,
                TermKind::Not(inner)
                    if matches!(
                        manager.get(*inner).map(|t| &t.kind),
                        Some(TermKind::Eq(_, _))
                    )
            );
            let _ = &term;
            if is_literal {
                // A top-level foreign equality is still a foreign leaf.
                // Boolean structure in another assertion must not send it
                // to DPLL(FF) as an unconstrained propositional atom.
                if !is_ff_literal(a, manager) {
                    return None;
                }
            } else {
                has_structure = true;
                // Structure is allowed only over FF atoms; verify the
                // whole sub-DAG before committing (a mixed leaf under
                // the structure would otherwise be abstracted into a
                // free Boolean — exactly the false-`sat` shape).
                if !dag_is_ff_boolean(a, manager) {
                    return None;
                }
            }
        }
        if has_structure {
            return self.dpll_ff(manager);
        }

        // Flatten the assertions into literals (and-conjunctions only;
        // `true` contributes nothing).
        let mut literals: Vec<TermId> = Vec::new();
        for &assertion in &self.assertions {
            let term = manager.get(assertion)?;
            match &term.kind {
                TermKind::True => {}
                TermKind::And(children) => {
                    let mut work: Vec<TermId> = children.iter().rev().copied().collect();
                    while let Some(t) = work.pop() {
                        let node = manager.get(t)?;
                        match &node.kind {
                            TermKind::True => {}
                            TermKind::And(inner) => {
                                work.extend(inner.iter().rev().copied());
                            }
                            _ => literals.push(t),
                        }
                    }
                }
                _ => literals.push(assertion),
            }
        }

        for &lit in &literals {
            if !is_ff_literal(lit, manager) {
                return None;
            }
        }

        let fields = self.goal_fields(manager);
        if fields.is_empty() {
            return None;
        }

        // Multiplexed per field: the conjunction splits across fields.
        let mut combined_model = Model::new();
        let mut core: Vec<usize> = Vec::new();
        for field in fields {
            // The slice for this field: literals mentioning it (plus
            // globally-true literals, which check_conjunction skips).
            let slice: Vec<TermId> = literals
                .iter()
                .copied()
                .filter(|&l| literal_mentions_field(l, field, manager))
                .collect();
            let outcome = check_conjunction(manager, field, &slice, FF_BUDGET_STEPS);
            match outcome {
                FfOutcome::Model(model) => {
                    // Step 5: validate, always. A failing validation is an
                    // internal error — fall through to the honest Unknown
                    // of the CDCL path, never a `Sat`.
                    if validate_model(manager, field, &slice, &model).is_err() {
                        return None;
                    }
                    for (var, value) in model.assignments() {
                        let value_term = manager.mk_ff_const(field, into_bigint(value)).ok()?;
                        combined_model.set(*var, value_term);
                    }
                }
                FfOutcome::Unsat(ff_core) => {
                    // Map the slice indices back to the global literal list
                    // — the certificate's literal indices remap the same
                    // way, so the stored object stays verifiable against
                    // the literals it names.
                    for &i in &ff_core.fact_indices {
                        if let Some(&lit) = slice.get(i) {
                            if let Some(global) = literals.iter().position(|&l| l == lit) {
                                core.push(global);
                            }
                        }
                    }
                    let certificate = ff_core.certificate.map(|cert| {
                        let remapped = match &cert {
                            nixie_theories::ff_theory::FfCertificate::IdealMembership {
                                field,
                                generators,
                                cofactors,
                            } => {
                                let gens = generators
                                    .iter()
                                    .map(|(lit, poly)| {
                                        let global = lit.and_then(|i| {
                                            slice.get(i).and_then(|&l| {
                                                literals.iter().position(|&x| x == l)
                                            })
                                        });
                                        (global, poly.clone())
                                    })
                                    .collect();
                                nixie_theories::ff_theory::FfCertificate::IdealMembership {
                                    field: *field,
                                    generators: gens,
                                    cofactors: cofactors.clone(),
                                }
                            }
                            nixie_theories::ff_theory::FfCertificate::Cardinality {
                                field,
                                literal,
                                k,
                            } => {
                                let global = slice
                                    .get(*literal)
                                    .and_then(|&l| literals.iter().position(|&x| x == l))
                                    .unwrap_or(*literal);
                                nixie_theories::ff_theory::FfCertificate::Cardinality {
                                    field: *field,
                                    literal: global,
                                    k: *k,
                                }
                            }
                            // The case tree's atoms are the replayed
                            // generator list of the SLICE — the slice
                            // itself is carried as the certificate's
                            // literal list, so no remapping is needed.
                            tree @ nixie_theories::ff_theory::FfCertificate::CaseTree { .. } => {
                                tree.clone()
                            }
                        };
                        (remapped, literals.clone())
                    });
                    // An empty core cannot happen (check_conjunction
                    // guarantees one), but an unwarranted whole-goal Unsat
                    // is worse than a missed dispatch: only answer Unsat
                    // with a nonempty core.
                    if !core.is_empty() {
                        self.install_ff_core(&literals, &core);
                        self.ff_certificate = certificate;
                        return Some(SolverResult::Unsat);
                    }
                    return None;
                }
                FfOutcome::Exhausted { certificate } => {
                    // The branching closed the search space: genuine
                    // UNSAT with the §8 case-tree certificate when the
                    // search recorded one (the literals list stays the
                    // slice the certificate replays against). Certified
                    // mode accepts it after replay verification; the
                    // certificate-less cases (enumeration paths, aborted
                    // tracking) still decline honestly.
                    self.install_ff_core(&literals, &[]);
                    self.ff_certificate = certificate.map(|cert| (cert, literals.clone()));
                    return Some(SolverResult::Unsat);
                }
                FfOutcome::OutOfBudget { where_ } => {
                    tracing::debug!("ff dispatch: budget exhausted at {where_}");
                    return None;
                }
                FfOutcome::InvalidModel(reason) => {
                    tracing::warn!("ff dispatch declined: {reason}");
                    return None;
                }
            }
        }
        self.model = Some(combined_model);
        Some(SolverResult::Sat)
    }

    /// Record the unsat core as the asserted-literal subset (the solver's
    /// core mechanism consumes named assertions; the literal indices here
    /// feed diagnostics and the future CDCL(T) lemma path).
    fn install_ff_core(&mut self, literals: &[TermId], core: &[usize]) {
        // Phase 3: cores are recorded for `get-unsat-core` support in the
        // solver's named-assertion machinery when it lands with Phase 4's
        // trail wiring. The literal list is kept out of hot paths.
        let _ = (literals, core);
    }
}

/// Exact `BigUint → BigInt` (the residue is already in `[0, p)`).
fn into_bigint(v: &BigUint) -> num_bigint::BigInt {
    num_bigint::BigInt::from_biguint(num_bigint::Sign::Plus, v.clone())
}

/// Whether a term's DAG contains finite-field structure (explicit stack).
fn term_uses_ff(root: TermId, manager: &TermManager) -> bool {
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut stack = vec![root];
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        let Some(term) = manager.get(t) else {
            continue;
        };
        match &term.kind {
            TermKind::FfConst { .. }
            | TermKind::FfAdd(_)
            | TermKind::FfMul(_)
            | TermKind::FfNeg(_)
            | TermKind::FfBitsum(_) => return true,
            TermKind::Var(_) => {
                if matches!(
                    manager.sorts.get(term.sort).map(|s| &s.kind),
                    Some(SortKind::FiniteField(_))
                ) {
                    return true;
                }
            }
            _ => stack.extend(nixie_core::ast::get_children(&term.kind)),
        }
    }
    false
}

/// Whether a term is an FF literal: `=`, `not =`, `true`, `false` — the
/// signature has exactly one predicate.
fn is_ff_literal(lit: TermId, manager: &TermManager) -> bool {
    let Some(term) = manager.get(lit) else {
        return false;
    };
    match &term.kind {
        TermKind::True | TermKind::False => true,
        TermKind::Eq(a, b) => {
            // An FF equality: at least one side mentions FF structure and,
            // when so, both sides are pure FF terms (the parser rejects
            // mixed sorts, so the second clause is a shape guard). A
            // non-FF equality (Int, BV, …) declines: not this dispatcher's.
            let fa = term_uses_ff(*a, manager);
            let fb = term_uses_ff(*b, manager);
            if !fa && !fb {
                return false;
            }
            is_pure_ff(*a, manager) && is_pure_ff(*b, manager)
        }
        TermKind::Not(inner) => {
            let Some(t) = manager.get(*inner) else {
                return false;
            };
            matches!(t.kind, TermKind::Eq(_, _)) && is_ff_literal(*inner, manager)
        }
        _ => false,
    }
}

/// Whether a term is built ONLY from FF structure (no foreign-theory
/// leaves) — an `=` mixing an FF side with a non-FF side is a type error
/// the parser rejects, so this is a shape guard, not a semantic one.
fn is_pure_ff(root: TermId, manager: &TermManager) -> bool {
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut stack = vec![root];
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        let Some(term) = manager.get(t) else {
            return false;
        };
        match &term.kind {
            TermKind::FfConst { .. }
            | TermKind::FfAdd(_)
            | TermKind::FfMul(_)
            | TermKind::FfNeg(_)
            | TermKind::FfBitsum(_) => {}
            TermKind::Var(_) => {
                if !matches!(
                    manager.sorts.get(term.sort).map(|s| &s.kind),
                    Some(SortKind::FiniteField(_))
                ) {
                    return false;
                }
            }
            _ => return false,
        }
    }
    true
}

/// Whether a literal's DAG mentions a specific field.
fn literal_mentions_field(lit: TermId, field: FieldId, manager: &TermManager) -> bool {
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut stack = vec![lit];
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        let Some(term) = manager.get(t) else {
            continue;
        };
        if let TermKind::FfConst { field: id, .. } = &term.kind {
            if *id == field {
                return true;
            }
            // A literal naming another field still belongs to that other
            // field's slice; keep walking for this one only if some
            // subterm names it.
        }
        // FF-sorted variables: resolve their field through the sort.
        if let TermKind::Var(_) = &term.kind
            && let Some(SortKind::FiniteField(id)) =
                manager.sorts.get(term.sort).map(|s| s.kind.clone())
            && id == field
        {
            return true;
        }
        // A `QF_UFFF` application mentions exactly its result field (the
        // arguments are opaque here; foreign-field arguments belong to
        // their own slices).
        if let TermKind::Apply { .. } = &term.kind
            && let Some(SortKind::FiniteField(id)) =
                manager.sorts.get(term.sort).map(|s| s.kind.clone())
            && id == field
        {
            return true;
        }
        if let TermKind::Apply { .. } = &term.kind {
            continue;
        }
        stack.extend(nixie_core::ast::get_children(&term.kind));
    }
    false
}

// ================= Phase 4: lazy DPLL(T) over FF atoms =================
//
// Goals with Boolean structure over FF atoms: Tseitin-abstract each FF
// equality into a SAT variable, solve the propositional skeleton with
// `nixie-sat` (clause learning for free), and check each candidate
// assignment's literal set with the Phase-3 conjunction procedure. A
// refuted assignment contributes a blocking clause over its atom
// polarities; finitely many assignments terminate the loop.
//
// This is the CDCL(T) shape with the FF theory as a black-box leaf — the
// full incremental theory-solver trail is Phase 5+, and the design
// explicitly allows the eager whole-problem form for `check`.

impl Solver {
    /// The lazy DPLL(T) loop. Returns `None` (→ `Unknown`) on budget or
    /// on a shape it does not own; the honesty gate covers the `None`.
    fn dpll_ff(&mut self, manager: &mut TermManager) -> Option<SolverResult> {
        // Cardinality guard (§7) BEFORE the distinct terms are expanded
        // into pairwise disequalities (after expansion the count is
        // invisible): k pairwise-distinct terms of 𝔽_p need k ≤ p.
        // SOUND ONLY on the asserted conjunct spine — a `distinct` under
        // `or`/`not` is a SAT decision, not a fact, and refuting it would
        // refute goals like `(not (distinct x y z))` over 𝔽₂ (satisfiable
        // by any repeated assignment). Off-spine distincts are handled by
        // the theory loop, which enumeration decides soundly at the tiny
        // fields where k can exceed p at all.
        if let Some((distinct_term, field, k)) =
            asserted_spine_distinct_exceeds_field(manager, &self.assertions)
        {
            // Pigeonhole UNSAT with its checkable certificate: the
            // literal index names the distinct inside `self.assertions`.
            let literal = self
                .assertions
                .iter()
                .position(|&a| a == distinct_term)
                .unwrap_or(0);
            self.ff_certificate = Some((
                nixie_theories::ff_theory::FfCertificate::Cardinality { field, literal, k },
                self.assertions.clone(),
            ));
            return Some(SolverResult::Unsat);
        }

        // 1. Collect the FF atoms (equalities between pure-FF terms) and
        //    mint a SAT variable per atom.
        let mut atoms: Vec<TermId> = Vec::new();
        let mut atom_var: FxHashMap<TermId, Var> = FxHashMap::default();
        let mut sat = SatSolver::new();
        for &assertion in &self.assertions {
            collect_ff_atoms(assertion, manager, &mut atoms);
        }
        atoms.sort_unstable();
        atoms.dedup();
        for &atom in &atoms {
            let var = sat.new_var();
            atom_var.insert(atom, var);
        }

        // 2. Tseitin-encode each assertion over the atom variables. The
        //    encoder borrows `sat`; the loop below uses the clauses it
        //    left behind, so the borrow ends here.
        let mut unit_lits: Vec<Lit> = Vec::with_capacity(self.assertions.len());
        {
            let mut encoder = FfTseitin {
                sat: &mut sat,
                atom_var: &mut atom_var,
            };
            for &assertion in &self.assertions {
                match encoder.encode(assertion, manager) {
                    Some(l) => unit_lits.push(l),
                    None => {
                        return None;
                    }
                }
            }
        }
        // Atoms may have grown (distinct expansions register fresh
        // equalities); rebuild the ordered list for the assignment loop.
        let mut atoms: Vec<TermId> = atom_var.keys().copied().collect();
        atoms.sort_unstable();
        for lit in unit_lits {
            if !sat.add_clause([lit]) {
                return Some(SolverResult::Unsat);
            }
        }

        // Extension enumeration has a deterministic outer Boolean-case cap
        // in addition to the per-conjunction arithmetic budget.
        let mut binary_cases = self
            .goal_fields(manager)
            .iter()
            .any(|&f| {
                manager
                    .sorts
                    .field_desc(f)
                    .and_then(|d| d.binary())
                    .is_some()
            })
            .then_some(1024u32);
        // 3. The lazy loop.
        loop {
            if let Some(left) = &mut binary_cases {
                *left = left.checked_sub(1)?;
            }
            match sat.solve() {
                nixie_sat::SolverResult::Unsat => {
                    // Every Boolean assignment is refuted: UNSAT. (No
                    // traced core on this path — Phase 6.)
                    return Some(SolverResult::Unsat);
                }
                nixie_sat::SolverResult::Unknown => return None,
                nixie_sat::SolverResult::Sat => {
                    // The literal set this Boolean model induces.
                    let mut slice: Vec<TermId> = Vec::new();
                    let mut blocking: Vec<Lit> = Vec::new();
                    for &atom in &atoms {
                        let var = atom_var[&atom];
                        let value = sat.model_value(var);
                        use nixie_sat::LBool;
                        match value {
                            LBool::True => {
                                slice.push(atom);
                                blocking.push(Lit::neg(var));
                            }
                            LBool::False => {
                                let neg = manager.mk_not(atom);
                                slice.push(neg);
                                blocking.push(Lit::pos(var));
                            }
                            LBool::Undef => {
                                // Unassigned atom: unconstrained by the
                                // skeleton; treat as true for the theory
                                // check (any value works for a full
                                // assignment — but the blocking clause
                                // must not assume it, so this arm is
                                // conservative: include it positively and
                                // block on it too).
                                slice.push(atom);
                                blocking.push(Lit::neg(var));
                            }
                        }
                    }
                    // Group by field and check each slice.
                    let fields = {
                        let mut fs: Vec<FieldId> = Vec::new();
                        for &l in &slice {
                            for f in fields_of_literal(l, manager) {
                                if !fs.contains(&f) {
                                    fs.push(f);
                                }
                            }
                        }
                        fs.sort_by_key(|f| f.raw());
                        fs
                    };
                    let mut any_refuted = false;
                    let mut model = Model::new();
                    for field in fields {
                        let field_slice: Vec<TermId> = slice
                            .iter()
                            .copied()
                            .filter(|&l| literal_mentions_field(l, field, manager))
                            .collect();
                        match check_conjunction(manager, field, &field_slice, FF_BUDGET_STEPS) {
                            FfOutcome::Model(ff_model) => {
                                if validate_model(manager, field, &field_slice, &ff_model).is_err()
                                {
                                    return None;
                                }
                                for (var_term, value) in ff_model.assignments() {
                                    let value_term =
                                        manager.mk_ff_const(field, into_bigint(value)).ok()?;
                                    model.set(*var_term, value_term);
                                }
                            }
                            FfOutcome::Unsat(_) | FfOutcome::Exhausted { .. } => {
                                any_refuted = true;
                                break;
                            }
                            FfOutcome::OutOfBudget { .. } | FfOutcome::InvalidModel(_) => {
                                return None;
                            }
                        }
                    }
                    if any_refuted {
                        // Learn: not this exact assignment.
                        if !sat.add_clause(blocking) {
                            return Some(SolverResult::Unsat);
                        }
                        continue;
                    }
                    // SAT: install atom truths too, so `get-value` on the
                    // Boolean atoms answers.
                    for &atom in &atoms {
                        let var = atom_var[&atom];
                        let truth = matches!(sat.model_value(var), nixie_sat::LBool::True);
                        model.set(atom, manager.mk_bool(truth));
                    }
                    self.model = Some(model);
                    return Some(SolverResult::Sat);
                }
            }
        }
    }
}

/// The cardinality guard's DPLL-side arm: a `distinct` over more terms
/// than its field's order, reachable only through the asserted conjunct
/// spine (top-level assertions and their `and` conjuncts — never under
/// `or`/`not`/`ite`, where the distinct's truth is undecided).
fn asserted_spine_distinct_exceeds_field(
    manager: &TermManager,
    assertions: &[TermId],
) -> Option<(TermId, FieldId, usize)> {
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(t) = stack.pop() {
        let Some(term) = manager.get(t) else {
            continue;
        };
        match &term.kind {
            TermKind::True => {}
            TermKind::And(children) => stack.extend(children.iter().copied()),
            TermKind::Distinct(args) => {
                let field: Option<FieldId> = args.iter().find_map(|&a| {
                    let arg = manager.get(a)?;
                    match manager.sorts.get(arg.sort).map(|s| s.kind.clone()) {
                        Some(SortKind::FiniteField(id)) => Some(id),
                        _ => None,
                    }
                });
                if let Some(field) = field {
                    let all_here = args.iter().all(|&a| {
                        manager
                            .get(a)
                            .and_then(|t| manager.sorts.get(t.sort).map(|s| s.kind.clone()))
                            .is_some_and(|k| matches!(k, SortKind::FiniteField(id) if id == field))
                    });
                    if all_here
                        && let Some(modulus) = manager.sorts.field_table().modulus(field)
                        && num_bigint::BigUint::from(args.len()) > *modulus
                    {
                        return Some((t, field, args.len()));
                    }
                }
            }
            _ => {}
        }
    }
    None
}

/// Collect every FF equality atom (`=` between pure-FF terms) in a DAG.
fn collect_ff_atoms(root: TermId, manager: &TermManager, atoms: &mut Vec<TermId>) {
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut stack = vec![root];
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        let Some(term) = manager.get(t) else {
            continue;
        };
        match &term.kind {
            TermKind::Eq(a, b) => {
                if is_ff_combinand(*a, manager)
                    && is_ff_combinand(*b, manager)
                    && !atoms.contains(&t)
                {
                    atoms.push(t);
                }
            }
            TermKind::True
            | TermKind::False
            | TermKind::FfConst { .. }
            | TermKind::FfAdd(_)
            | TermKind::FfMul(_)
            | TermKind::FfNeg(_)
            | TermKind::FfBitsum(_)
            | TermKind::Var(_) => {}
            _ => stack.extend(nixie_core::ast::get_children(&term.kind)),
        }
    }
}

/// Whether a whole Boolean DAG is built only from FF atoms and Boolean
/// structure — the DPLL(T) precondition (a foreign leaf would become a
/// free Boolean: a false-`sat` factory).
fn dag_is_ff_boolean(root: TermId, manager: &TermManager) -> bool {
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut stack = vec![root];
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        let Some(term) = manager.get(t) else {
            return false;
        };
        match &term.kind {
            TermKind::True | TermKind::False => {}
            TermKind::Eq(a, b) => {
                if !is_pure_ff(*a, manager) || !is_pure_ff(*b, manager) {
                    return false;
                }
            }
            TermKind::Not(_)
            | TermKind::And(_)
            | TermKind::Or(_)
            | TermKind::Xor(_, _)
            | TermKind::Implies(_, _)
            | TermKind::Ite(_, _, _) => {
                stack.extend(nixie_core::ast::get_children(&term.kind));
            }
            TermKind::Distinct(args) => {
                for &a in args {
                    if !is_pure_ff(a, manager) {
                        return false;
                    }
                }
            }
            _ => return false,
        }
    }
    true
}

/// The fields a literal can mention.
fn fields_of_literal(lit: TermId, manager: &TermManager) -> Vec<FieldId> {
    let mut fields: Vec<FieldId> = Vec::new();
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut stack = vec![lit];
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        let Some(term) = manager.get(t) else {
            continue;
        };
        if let TermKind::FfConst { field, .. } = &term.kind {
            if !fields.contains(field) {
                fields.push(*field);
            }
        }
        if let TermKind::Var(_) = &term.kind
            && let Some(SortKind::FiniteField(id)) =
                manager.sorts.get(term.sort).map(|s| s.kind.clone())
            && !fields.contains(&id)
        {
            fields.push(id);
        }
        // A `QF_UFFF` application contributes its result field only.
        if let TermKind::Apply { .. } = &term.kind
            && let Some(SortKind::FiniteField(id)) =
                manager.sorts.get(term.sort).map(|s| s.kind.clone())
            && !fields.contains(&id)
        {
            fields.push(id);
            continue;
        }
        if let TermKind::Apply { .. } = &term.kind {
            continue;
        }
        stack.extend(nixie_core::ast::get_children(&term.kind));
    }
    fields
}

/// Tseitin encoder for the Boolean skeleton over FF atom variables.
struct FfTseitin<'a> {
    sat: &'a mut SatSolver,
    atom_var: &'a mut FxHashMap<TermId, Var>,
}

impl<'a> FfTseitin<'a> {
    /// The SAT variable of an FF atom, registering it on first sight
    /// (distinct expansions mint equalities after collection).
    fn atom_lit(&mut self, eq: TermId) -> Option<Var> {
        if let Some(&v) = self.atom_var.get(&eq) {
            return Some(v);
        }
        let v = self.sat.new_var();
        self.atom_var.insert(eq, v);
        Some(v)
    }

    /// Encode a Boolean term to a literal (`None` = unsupported shape).
    fn encode(&mut self, t: TermId, manager: &mut TermManager) -> Option<Lit> {
        enum Frame {
            Expand(TermId),
            Combine(CombineKind, usize),
        }
        #[allow(dead_code)]
        enum CombineKind {
            Not,
            And(usize),
            Or(usize),
            Xor,
            Implies,
            Ite,
        }
        let mut results: Vec<Lit> = Vec::new();
        let mut stack: Vec<Frame> = vec![Frame::Expand(t)];
        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Expand(x) => {
                    let term = manager.get(x)?;
                    match &term.kind {
                        TermKind::True => results.push(Lit::pos(self.sat.new_var_forced_true())),
                        TermKind::False => results.push(Lit::neg(self.sat.new_var_forced_true())),
                        TermKind::Eq(a, b) => {
                            // Check independently of the dispatch shape gate:
                            // every atom must belong to an actual field slice.
                            let field = ff_sort_field(manager, *a)?;
                            if ff_sort_field(manager, *b) != Some(field) {
                                return None;
                            }
                            let var = self.atom_lit(x)?;
                            results.push(Lit::pos(var));
                        }
                        // Combine frames record their arity; the operands
                        // are taken from `results` (the operand stack) at
                        // combine time — children popped in order.
                        TermKind::Not(_) => {
                            stack.push(Frame::Combine(CombineKind::Not, 1));
                            stack.push(Frame::Expand(term_arg(term, 0)?));
                        }
                        TermKind::And(children) => {
                            stack.push(Frame::Combine(
                                CombineKind::And(children.len()),
                                children.len(),
                            ));
                            for &c in children.iter().rev() {
                                stack.push(Frame::Expand(c));
                            }
                        }
                        TermKind::Or(children) => {
                            stack.push(Frame::Combine(
                                CombineKind::Or(children.len()),
                                children.len(),
                            ));
                            for &c in children.iter().rev() {
                                stack.push(Frame::Expand(c));
                            }
                        }
                        TermKind::Xor(a, b) => {
                            stack.push(Frame::Combine(CombineKind::Xor, 2));
                            stack.push(Frame::Expand(*b));
                            stack.push(Frame::Expand(*a));
                        }
                        TermKind::Implies(a, b) => {
                            stack.push(Frame::Combine(CombineKind::Implies, 2));
                            stack.push(Frame::Expand(*b));
                            stack.push(Frame::Expand(*a));
                        }
                        TermKind::Ite(c, a, b) => {
                            stack.push(Frame::Combine(CombineKind::Ite, 3));
                            stack.push(Frame::Expand(*b));
                            stack.push(Frame::Expand(*a));
                            stack.push(Frame::Expand(*c));
                        }
                        TermKind::Distinct(args) => {
                            if let Some(&first) = args.first() {
                                let field = ff_sort_field(manager, first)?;
                                if args
                                    .iter()
                                    .any(|&a| ff_sort_field(manager, a) != Some(field))
                                {
                                    return None;
                                }
                            }
                            // distinct(a0…an) = ∧_{i<j} ¬(ai = aj): encode
                            // pairwise, registering each pair's equality
                            // as a (lazily created) atom.
                            let pairs: Vec<(TermId, TermId)> = args
                                .iter()
                                .enumerate()
                                .flat_map(|(i, &a)| args[i + 1..].iter().map(move |&b| (a, b)))
                                .collect();
                            stack.push(Frame::Combine(CombineKind::And(pairs.len()), pairs.len()));
                            for (a, b) in pairs.iter().rev() {
                                // Each conjunct is ¬(a = b): expand the
                                // equality first (it pops first), then a
                                // Not combine over its literal.
                                stack.push(Frame::Combine(CombineKind::Not, 1));
                                stack.push(Frame::Expand(manager.mk_eq(*a, *b)));
                            }
                        }
                        _ => return None,
                    }
                }
                Frame::Combine(kind, n) => {
                    if results.len() < n {
                        return None;
                    }
                    // The children were pushed in reverse so they pop in
                    // order; split off the last n as [a0, a1, ...].
                    let operands: SmallVec<[Lit; 4]> =
                        results.split_off(results.len() - n).into_iter().collect();
                    match kind {
                        CombineKind::Not => {
                            let l = operands[0];
                            results.push(l.negate());
                        }
                        CombineKind::And(_) => {
                            let v = self.sat.new_var();
                            for &l in &operands {
                                // v -> l : ¬v ∨ l
                                self.sat.add_clause([Lit::neg(v), l]);
                            }
                            // l0 ∧ .. ∧ ln -> v
                            let mut clause: SmallVec<[Lit; 4]> =
                                operands.iter().map(|l| l.negate()).collect();
                            clause.push(Lit::pos(v));
                            self.sat.add_clause(clause);
                            results.push(Lit::pos(v));
                        }
                        CombineKind::Or(_) => {
                            let v = self.sat.new_var();
                            for &l in &operands {
                                // l -> v : ¬l ∨ v
                                self.sat.add_clause([l.negate(), Lit::pos(v)]);
                            }
                            let mut clause: SmallVec<[Lit; 4]> = operands.clone();
                            clause.push(Lit::neg(v));
                            self.sat.add_clause(clause);
                            results.push(Lit::pos(v));
                        }
                        CombineKind::Xor => {
                            let b = operands[1];
                            let a = operands[0];
                            let v = self.sat.new_var();
                            // v ↔ a ⊕ b, both directions.
                            self.sat.add_clause([Lit::neg(v), a, b]);
                            self.sat.add_clause([Lit::neg(v), a.negate(), b.negate()]);
                            self.sat.add_clause([Lit::neg(v), a.negate(), b]);
                            self.sat.add_clause([Lit::neg(v), a, b.negate()]);
                            self.sat.add_clause([Lit::pos(v), a.negate(), b]);
                            self.sat.add_clause([Lit::pos(v), a, b.negate()]);
                            self.sat.add_clause([Lit::pos(v), a, b]);
                            self.sat.add_clause([Lit::pos(v), a.negate(), b.negate()]);
                            results.push(Lit::pos(v));
                        }
                        CombineKind::Implies => {
                            // operands = [a, b] (a → b).
                            let b = operands[1];
                            let a = operands[0];
                            let v = self.sat.new_var();
                            // v = (a → b): ¬v → a, ¬v → ¬b, and the defining
                            // direction a ∧ ¬b → ¬v.
                            self.sat.add_clause([Lit::neg(v), a]);
                            self.sat.add_clause([Lit::neg(v), b.negate()]);
                            self.sat.add_clause([a.negate(), b, Lit::pos(v)]);
                            results.push(Lit::pos(v));
                        }
                        CombineKind::Ite => {
                            // operands = [c, a, b] (children expanded in
                            // reverse push order: c, then a, then b).
                            let c = operands[0];
                            let a = operands[1];
                            let b = operands[2];
                            let v = self.sat.new_var();
                            // c ∧ a -> v ; c ∧ ¬a -> ¬v ; ¬c∧¬v->a etc. Use the
                            // standard three-clause form plus completion.
                            self.sat.add_clause([c.negate(), a.negate(), Lit::pos(v)]);
                            self.sat.add_clause([c, b.negate(), Lit::neg(v)]);
                            self.sat.add_clause([c.negate(), a, Lit::neg(v)]);
                            self.sat.add_clause([c, b, Lit::pos(v)]);
                            results.push(Lit::pos(v));
                        }
                    }
                }
            }
        }
        if results.len() != 1 {
            return None;
        }
        results.pop()
    }
}

/// Helper trait shims to keep the encoder readable.
trait SatExt {
    fn new_var_forced_true(&mut self) -> Var;
}

impl SatExt for SatSolver {
    fn new_var_forced_true(&mut self) -> Var {
        let v = self.new_var();
        self.add_clause([Lit::pos(v)]);
        v
    }
}

fn term_arg(term: &nixie_core::ast::Term, i: usize) -> Option<TermId> {
    nixie_core::ast::get_children(&term.kind).get(i).copied()
}

use smallvec::SmallVec;

// ============ Phase 6 remainder: `QF_UFFF` (FF ⊕ EUF) ============
//
// Polite combination over shared FF-sorted terms (FF_THEORY_DESIGN §7).
// EUF is smooth and finitely witnessable, so `T_FF ⊕ EUF` is decided by
// searching arrangements: which shared FF-sorted terms are equal. The
// architecture, layered on the Phase-4 lazy DPLL(T):
//
//   * the SAT skeleton abstracts every FF equality atom (Tseitin, as in
//     `dpll_ff`) — including equalities whose sides mention uninterpreted
//     applications with FF result sorts;
//   * per Boolean model, a batch congruence closure
//     (`nixie_theories::ff_euf`) merges the asserted equalities and
//     propagates congruences (`x = y ⟹ f(x) = f(y)`); its merge classes
//     become extra literals fed to the FF conjunction procedure, which
//     sees each application as an opaque variable;
//   * the FF procedure's model induces an arrangement of the shared
//     terms. If that arrangement violates function-hood (equal argument
//     values, different results) the search SPLITS — the valid
//     disjunction `f(a) = f(b) ∨ ⋁ᵢ aᵢ ≠ bᵢ` — and backtracks through
//     the cases with an explicit stack (never native recursion);
//   * a node whose FF slices are UNSAT refutes the Boolean model
//     (every literal fed to the slices is a consequence of the model's
//     atoms plus the node's case assumptions) — the assignment gets a
//     blocking clause, and exhausting the skeleton is UNSAT;
//   * cardinality is guarded at both ends: the spine guard below (a
//     top-level `distinct` over more terms than the field's order, with
//     its pigeonhole certificate) and, per Boolean model, the interface
//     guard (a `distinct` whose entire pairwise disequality set the
//     model asserts, over k > p terms — the polite-combination clause
//     `k pairwise-distinct shared terms need k ≤ p`, vacuous at ZK
//     primes, decisive at 𝔽₂/𝔽₃).
//
// Certificates: an UNSAT on this path stores no FF certificate (the
// refutation runs through the Boolean skeleton and congruence lemmas).
// Certified mode still decides some of them: its independent Boolean
// checker classifies FF equalities as EUF atoms and runs its own
// VERIFIED congruence-blocking loop, so pure-congruence refutations
// certify through that; refutations that need the field arithmetic (or
// the interface pigeonhole off-spine) have nothing to check and
// downgrade to `unknown` — by design, exactly as for Phase 4's pure-FF
// Boolean path.

/// Total case-tree node budget per `check`, shared across every Boolean
/// assignment's arrangement search AND the destructive refutation
/// minimizer (each node runs a closure and one FF conjunction check per
/// field). A tick counter; never wall-clock.
const FF_UFFF_TOTAL_NODES: u64 = 256;

/// Per-node FF conjunction budget for the combination loop. The eager
/// path's full [`FF_BUDGET_STEPS`] buys Gröbner cascades the arrangement
/// search cannot amortize — one node's algebra is re-done per case, so a
/// node that grinds starves every other Boolean assignment. This cap
/// keeps a node's algebra bounded; the goals that need more degrade to
/// an honest `unknown` (the pure-`QF_FF` path still runs at full
/// budget).
const FF_UFFF_NODE_BUDGET: u64 = 1 << 17;

/// One arrangement decision: `a = b` (positive) or `a ≠ b`.
#[derive(Clone, Copy, Debug)]
struct UfffChoice {
    a: TermId,
    b: TermId,
    positive: bool,
}

/// The candidate model a case node produced: per-field term values plus
/// the application inventory (term, function, argument terms) the
/// completion pass and function-hood scan consume.
#[derive(Default)]
struct UfffModel {
    per_field: Vec<(FieldId, FxHashMap<TermId, BigUint>)>,
    apps: Vec<(TermId, nixie_core::interner::Spur, SmallVec<[TermId; 4]>)>,
}

impl UfffModel {
    /// The value of a term in its own field's map.
    fn value_of(&self, term: TermId, field: FieldId) -> Option<&BigUint> {
        self.per_field
            .iter()
            .find(|(f, _)| *f == field)
            .and_then(|(_, map)| map.get(&term))
    }
}

/// The verdict of one case node.
enum UfffNode {
    /// A congruence-consistent arrangement: the model stands.
    Model(UfffModel),
    /// The literals plus this node's assumptions are jointly unsat. The
    /// hint (root nodes only, where the path is empty and the refuted
    /// FF core names only assignment literals) is the subset of the
    /// assignment's literals the core actually used — a conflict clause
    /// that small keeps the SAT loop from enumerating assignments one
    /// Hamiltonian path at a time.
    Refuted {
        /// Assignment literals sufficient for the refutation (`None`
        /// when the refutation leaned on case assumptions or derived
        /// literals — block on the whole assignment then).
        hint: Option<Vec<TermId>>,
    },
    /// Function-hood violated: try these case splits in order.
    Split(Vec<UfffChoice>),
    /// Budget or shape: honest `unknown`.
    Unknown,
}

impl Solver {
    /// The `QF_UFFF` loop. Returns `None` (→ `Unknown`) on budget or a
    /// shape it does not own; the honesty gate above covers the `None`.
    fn dpll_ufff(&mut self, manager: &mut TermManager) -> Option<SolverResult> {
        // Shape gate: Boolean structure over FF-or-UF atoms only. A
        // foreign leaf anywhere declines (a mixed goal is the main
        // CDCL(T) path's to answer, and its honesty gate says unknown).
        for &a in &self.assertions {
            if !dag_is_ufff_boolean(a, manager) {
                return None;
            }
        }

        // The spine cardinality guard (§7), BEFORE distinct expansion
        // makes the count invisible — same contract as `dpll_ff`'s, with
        // the certificate the certified gate re-verifies.
        if let Some((distinct_term, field, k)) =
            asserted_spine_distinct_exceeds_field(manager, &self.assertions)
        {
            let literal = self
                .assertions
                .iter()
                .position(|&a| a == distinct_term)
                .unwrap_or(0);
            self.ff_certificate = Some((
                nixie_theories::ff_theory::FfCertificate::Cardinality { field, literal, k },
                self.assertions.clone(),
            ));
            return Some(SolverResult::Unsat);
        }

        // 1. Atoms + distinct families (Tseitin expands the latter into
        //    pairwise equalities, registering them as atoms on demand).
        let mut atoms: Vec<TermId> = Vec::new();
        for &assertion in &self.assertions {
            collect_ff_atoms(assertion, manager, &mut atoms);
        }
        atoms.sort_unstable();
        atoms.dedup();
        let mut distincts: Vec<SmallVec<[TermId; 4]>> = Vec::new();
        for &assertion in &self.assertions {
            collect_ff_distincts(assertion, manager, &mut distincts);
        }
        let distinct_families = ufff_distinct_families(manager, &distincts);

        // 2. Tseitin-encode the skeleton over the atom variables.
        let mut atom_var: FxHashMap<TermId, Var> = FxHashMap::default();
        let mut sat = SatSolver::new();
        for &atom in &atoms {
            let var = sat.new_var();
            atom_var.insert(atom, var);
        }
        let mut unit_lits: Vec<Lit> = Vec::with_capacity(self.assertions.len());
        {
            let mut encoder = FfTseitin {
                sat: &mut sat,
                atom_var: &mut atom_var,
            };
            for &assertion in &self.assertions {
                match encoder.encode(assertion, manager) {
                    Some(l) => unit_lits.push(l),
                    None => return None,
                }
            }
        }
        let mut atoms: Vec<TermId> = atom_var.keys().copied().collect();
        atoms.sort_unstable();
        atoms.dedup();
        for lit in unit_lits {
            if !sat.add_clause([lit]) {
                return Some(SolverResult::Unsat);
            }
        }

        // 3. The lazy loop: SAT proposes an atom assignment, the
        //    combination layer checks it. One shared node budget covers
        //    the whole check (a pathological arrangement search must
        //    degrade to `unknown`, not grind).
        let mut node_budget: u64 = FF_UFFF_TOTAL_NODES;
        loop {
            match sat.solve() {
                nixie_sat::SolverResult::Unsat => {
                    // Every Boolean assignment refuted: UNSAT, with no
                    // certificate (see the section comment).
                    self.ff_certificate = None;
                    return Some(SolverResult::Unsat);
                }
                nixie_sat::SolverResult::Unknown => return None,
                nixie_sat::SolverResult::Sat => {
                    let mut slice: Vec<TermId> = Vec::new();
                    let mut blocking: Vec<Lit> = Vec::new();
                    let mut lit_to_sat: FxHashMap<TermId, Lit> = FxHashMap::default();
                    for &atom in &atoms {
                        let var = atom_var[&atom];
                        use nixie_sat::LBool;
                        match sat.model_value(var) {
                            LBool::True | LBool::Undef => {
                                slice.push(atom);
                                lit_to_sat.insert(atom, Lit::neg(var));
                                blocking.push(Lit::neg(var));
                            }
                            LBool::False => {
                                let neg = manager.mk_not(atom);
                                slice.push(neg);
                                lit_to_sat.insert(neg, Lit::pos(var));
                                blocking.push(Lit::pos(var));
                            }
                        }
                    }

                    // Interface cardinality guard: a distinct family the
                    // current model asserts IN FULL over k > p terms of
                    // one field is pigeonhole-unsatisfiable.
                    if ufff_interface_cardinality_refutes(&distinct_families, &slice) {
                        if !sat.add_clause(blocking) {
                            return Some(SolverResult::Unsat);
                        }
                        continue;
                    }

                    match ufff_case_search(manager, &atoms, &slice, &mut node_budget) {
                        UfffSearch::Model(model) => {
                            // Completion (unconstrained terms get
                            // function-hood-preserving defaults) — a
                            // completion failure is an honest Unknown.
                            let completed = match ufff_complete(manager, &self.assertions, model) {
                                Some(c) => c,
                                None => {
                                    tracing::warn!("ufff: model completion failed");
                                    return None;
                                }
                            };
                            let mut model_out = Model::new();
                            for (field, map) in &completed.per_field {
                                for (&term, value) in map {
                                    let value_term =
                                        manager.mk_ff_const(*field, into_bigint(value)).ok()?;
                                    model_out.set(term, value_term);
                                }
                            }
                            for &atom in &atoms {
                                let var = atom_var[&atom];
                                let truth = matches!(sat.model_value(var), nixie_sat::LBool::True);
                                model_out.set(atom, manager.mk_bool(truth));
                            }
                            self.model = Some(model_out);
                            return Some(SolverResult::Sat);
                        }
                        UfffSearch::Refuted(hint) => {
                            // Conflict-directed blocking when the
                            // refutation named its literals; otherwise
                            // destructively minimize the assignment
                            // (each candidate subset is re-checked at
                            // the ROOT — no case assumptions — so the
                            // surviving subset really does refute).
                            let minimized: Option<Vec<TermId>> = match &hint {
                                Some(lits)
                                    if !lits.is_empty()
                                        && lits.iter().all(|l| lit_to_sat.contains_key(l)) =>
                                {
                                    Some(lits.clone())
                                }
                                _ => ufff_shrink_refutation(
                                    manager,
                                    &atoms,
                                    &slice,
                                    &mut node_budget,
                                ),
                            };
                            let clause: Vec<Lit> = match minimized {
                                Some(lits)
                                    if !lits.is_empty()
                                        && lits.iter().all(|l| lit_to_sat.contains_key(l)) =>
                                {
                                    lits.iter()
                                        .filter_map(|l| lit_to_sat.get(l))
                                        .copied()
                                        .collect()
                                }
                                _ => blocking,
                            };
                            if !sat.add_clause(clause) {
                                return Some(SolverResult::Unsat);
                            }
                        }
                        UfffSearch::Unknown => return None,
                    }
                }
            }
        }
    }
}

/// The outcome of the arrangement search for one Boolean assignment.
enum UfffSearch {
    Model(UfffModel),
    /// Refuted, with an optional conflict subset of the assignment's
    /// literals (see [`UfffNode::Refuted`]).
    Refuted(Option<Vec<TermId>>),
    Unknown,
}

/// The arrangement case tree, driven by an explicit stack (deep goals
/// must not overflow the native stack). Each choice point carries its
/// own path of case assumptions; a node verdict of `Split` installs the
/// children as the point's remaining choices and descends into the
/// first; a `Refuted` node pops and moves to the point's next choice;
/// exhausting the root refutes the assignment.
fn ufff_case_search(
    manager: &mut TermManager,
    atoms: &[TermId],
    lits: &[TermId],
    node_budget: &mut u64,
) -> UfffSearch {
    struct ChoicePoint {
        path: Vec<UfffChoice>,
        children: Vec<UfffChoice>,
        next: usize,
    }
    let mut stack: Vec<ChoicePoint> = vec![ChoicePoint {
        path: Vec::new(),
        children: Vec::new(),
        next: 0,
    }];
    loop {
        let Some(top) = stack.last() else {
            return UfffSearch::Refuted(None);
        };
        let path = top.path.clone();
        let is_root = path.is_empty();
        if *node_budget == 0 {
            tracing::debug!("ufff: global case-node budget exhausted");
            return UfffSearch::Unknown;
        }
        *node_budget -= 1;
        match ufff_solve_node(manager, atoms, lits, &path) {
            UfffNode::Model(model) => return UfffSearch::Model(model),
            UfffNode::Unknown => return UfffSearch::Unknown,
            UfffNode::Refuted { hint } => {
                // A ROOT refutation (no case assumptions) with a
                // complete hint ends the search with that conflict
                // subset; deeper refutations only close their subtree.
                if is_root && hint.is_some() {
                    return UfffSearch::Refuted(hint);
                }
                // This node failed: pop it; the parent choice point (if
                // any) tries its next alternative.
                stack.pop();
                while let Some(parent) = stack.last_mut() {
                    if parent.next < parent.children.len() {
                        let child = parent.children[parent.next];
                        parent.next += 1;
                        let mut path = parent.path.clone();
                        path.push(child);
                        stack.push(ChoicePoint {
                            path,
                            children: Vec::new(),
                            next: 0,
                        });
                        break;
                    }
                    stack.pop();
                }
            }
            UfffNode::Split(children) => {
                let Some(top) = stack.last_mut() else {
                    return UfffSearch::Unknown;
                };
                top.children = children;
                if top.next < top.children.len() {
                    let child = top.children[top.next];
                    top.next += 1;
                    let mut path = top.path.clone();
                    path.push(child);
                    stack.push(ChoicePoint {
                        path,
                        children: Vec::new(),
                        next: 0,
                    });
                }
            }
        }
    }
}

/// Destructive minimization of a root-level refutation: drop literals
/// one at a time, keeping each drop whose remaining set still refutes
/// at the ROOT (empty case path). Because every trial re-runs the full
/// node check — closure, derivation, FF checks — on exactly the
/// candidate set, the surviving subset is a genuine conflict clause,
/// not an extrapolation (an unsound shrink here would block satisfying
/// assignments and fabricate `unsat`). `None` when even the full set
/// stops refuting (cannot happen — the caller only shrinks sets that
/// just refuted — or the budget dies mid-shrink).
fn ufff_shrink_refutation(
    manager: &mut TermManager,
    atoms: &[TermId],
    lits: &[TermId],
    node_budget: &mut u64,
) -> Option<Vec<TermId>> {
    let mut cand: Vec<TermId> = lits.to_vec();
    let mut i = 0usize;
    while i < cand.len() {
        if *node_budget == 0 {
            // Budget out mid-shrink: return the full set — blocking on
            // it is always sound (it is the assignment itself).
            return Some(cand);
        }
        *node_budget -= 1;
        let mut trial = cand.clone();
        let _ = trial.swap_remove(i);
        match ufff_solve_node(manager, atoms, &trial, &[]) {
            UfffNode::Refuted { .. } => {
                cand = trial;
                // The swapped-in element now sits at i: re-test it.
            }
            _ => {
                i += 1;
            }
        }
    }
    Some(cand)
}

/// One node of the arrangement case tree: build the congruence closure
/// of the positive equalities (asserted atoms + case assumptions), check
/// every negative equality against it, feed the merge classes to the FF
/// conjunction procedure per field, then scan the resulting model for
/// function-hood violations.
fn ufff_solve_node(
    manager: &mut TermManager,
    atoms: &[TermId],
    lits: &[TermId],
    extras: &[UfffChoice],
) -> UfffNode {
    // 1. The closure: register every FF-sorted subterm of every atom,
    //    merge the positive equalities, close under congruence.
    let mut closure = nixie_theories::ff_euf::CongruenceClosure::new();
    for &atom in atoms {
        closure.register_dag(manager, atom);
    }
    for choice in extras {
        if choice.positive {
            closure.merge(choice.a, choice.b);
        }
    }
    let mut negatives: Vec<(TermId, TermId)> = Vec::new();
    for &lit in lits {
        if let Some(term) = manager.get(lit) {
            if let TermKind::Eq(a, b) = &term.kind {
                closure.merge(*a, *b);
            }
        }
    }
    for choice in extras.iter().filter(|c| !c.positive) {
        negatives.push((choice.a, choice.b));
    }
    for &lit in lits {
        if let Some(term) = manager.get(lit)
            && let TermKind::Not(inner) = &term.kind
            && let Some(inner_term) = manager.get(*inner)
            && let TermKind::Eq(a, b) = &inner_term.kind
        {
            negatives.push((*a, *b));
        }
    }
    closure.propagate();

    // 2. Disequality conflicts: an asserted/case disequality between
    //    merged terms refutes the node.
    for &(a, b) in &negatives {
        if closure.are_equal(a, b) == Some(true) {
            return UfffNode::Refuted { hint: None };
        }
    }

    // 3. The arrangement equalities the closure derived (congruence
    //    consequences), as literals: for each class, everyone equals the
    //    canonical (smallest) member. Already-asserted equalities are
    //    skipped (they are in the slices as atoms).
    let positive_set: FxHashSet<TermId> = lits
        .iter()
        .copied()
        .chain(
            extras
                .iter()
                .filter(|c| c.positive)
                .map(|c| manager.mk_eq(c.a, c.b)),
        )
        .collect();
    let mut derived: Vec<TermId> = Vec::new();
    for class in closure.nonsingleton_classes() {
        let Some((&canon, rest)) = class.split_first() else {
            continue;
        };
        for &t in rest {
            let eq = manager.mk_eq(t, canon);
            if eq != manager.true_id && !positive_set.contains(&eq) {
                derived.push(eq);
            }
        }
    }

    // 4. Per-field FF conjunction checks over the assignment's literals,
    //    the derived equalities, and the case assumptions.
    let mut fields: Vec<FieldId> = Vec::new();
    for &l in lits.iter().chain(derived.iter()) {
        for f in fields_of_literal(l, manager) {
            if !fields.contains(&f) {
                fields.push(f);
            }
        }
    }
    for choice in extras {
        for f in fields_of_term(choice.a, manager)
            .into_iter()
            .chain(fields_of_term(choice.b, manager))
        {
            if !fields.contains(&f) {
                fields.push(f);
            }
        }
    }
    fields.sort_by_key(|f| f.raw());

    let mut extra_lits: Vec<TermId> = Vec::new();
    for choice in extras {
        let eq = manager.mk_eq(choice.a, choice.b);
        extra_lits.push(if choice.positive {
            eq
        } else {
            manager.mk_not(eq)
        });
    }

    let mut model = UfffModel::default();
    let single_field = fields.len() <= 1;
    for field in fields {
        // The slice keeps provenance: `true` for entries that ARE
        // assignment literals (atoms or their negations), `false` for
        // derived equalities and case assumptions — only the former can
        // feed a blocking hint.
        let slice: Vec<(TermId, bool)> = lits
            .iter()
            .map(|&l| (l, true))
            .chain(derived.iter().map(|&d| (d, false)))
            .chain(extra_lits.iter().map(|&e| (e, false)))
            .filter(|&(l, _)| literal_mentions_field(l, field, manager))
            .collect();
        let slice_terms: Vec<TermId> = slice.iter().map(|&(l, _)| l).collect();
        match check_conjunction(manager, field, &slice_terms, FF_UFFF_NODE_BUDGET) {
            FfOutcome::Model(m) => {
                if validate_model(manager, field, &slice_terms, &m).is_err() {
                    tracing::warn!("ufff: FF model failed exact validation");
                    return UfffNode::Unknown;
                }
                let map = m.assignments().clone();
                model.per_field.push((field, map));
            }
            // The slice is a consequence set of (assignment ∧ path):
            // unsat refutes the node — sound to backtrack. On the ROOT
            // node (no case assumptions), when every core literal is an
            // assignment literal, the core is a conflict clause over the
            // assignment — hand it up as the blocking hint. Multi-field
            // caution: a derived equality in one field can rest on
            // another field's atoms through cross-field congruence, so
            // the hint is only built when the whole goal is single-field
            // OR the core touches no derived literal at all.
            FfOutcome::Unsat(core) => {
                let hint = if extras.is_empty()
                    && single_field
                    && core
                        .fact_indices
                        .iter()
                        .all(|&i| slice.get(i).is_some_and(|&(_, from_l)| from_l))
                {
                    Some(
                        core.fact_indices
                            .iter()
                            .filter_map(|&i| slice.get(i).map(|&(l, _)| l))
                            .collect(),
                    )
                } else {
                    None
                };
                return UfffNode::Refuted { hint };
            }
            FfOutcome::Exhausted { .. } => return UfffNode::Refuted { hint: None },
            FfOutcome::OutOfBudget { .. } | FfOutcome::InvalidModel(_) => {
                return UfffNode::Unknown;
            }
        }
    }

    // 5. The function-hood scan over the candidate arrangement: two
    //    applications of one function whose KNOWN argument values the
    //    model makes equal must have equal results. A violation splits
    //    on the valid disjunction `f(a) = f(b) ∨ ⋁ᵢ aᵢ ≠ bᵢ` — the
    //    children force either the results to merge or some argument
    //    pair to differ, and the FF check constrains whichever it picks.
    model.apps = closure
        .application_terms()
        .into_iter()
        .filter_map(|t| {
            closure
                .application_signature(t)
                .map(|(func, args)| (t, func, args))
        })
        .collect();
    // Group applications by function symbol (deterministic: TermId order).
    let mut by_func: FxHashMap<nixie_core::interner::Spur, Vec<TermId>> = FxHashMap::default();
    for (term, func, _) in &model.apps {
        by_func.entry(*func).or_default().push(*term);
    }
    let mut funcs: Vec<_> = by_func
        .into_iter()
        .map(|(func, mut terms)| {
            terms.sort_unstable();
            (func, terms)
        })
        .collect();
    funcs.sort_by_key(|(func, _)| func.into_inner());

    for (_func, terms) in &funcs {
        for w in 0..terms.len() {
            for v in (w + 1)..terms.len() {
                let a1 = terms[w];
                let a2 = terms[v];
                let (args1, args2) = match (
                    model.apps.iter().find(|(t, _, _)| *t == a1),
                    model.apps.iter().find(|(t, _, _)| *t == a2),
                ) {
                    (Some((_, _, x)), Some((_, _, y))) => (x, y),
                    _ => continue,
                };
                // Results: both must be assigned (applications of atoms
                // are always in some slice; a missing one means the atom
                // set and the field routing disagree — decline).
                let (f1, r1) = match field_and_value(manager, &model, a1) {
                    Some(x) => x,
                    None => continue,
                };
                let (f2, r2) = match field_and_value(manager, &model, a2) {
                    Some(x) => x,
                    None => continue,
                };
                if f1 != f2 || r1 == r2 {
                    continue;
                }
                // Arguments: break on the first KNOWN difference. A pair
                // with UNEVALUABLE arguments (terms no literal mentions —
                // unconstrained) is left to the completion pass, which
                // can always separate variable arguments by fresh
                // values; splitting on them would explore arrangements
                // the model does not care about.
                let mut equal_known = true;
                let mut any_unknown = false;
                for (&x, &y) in args1.iter().zip(args2.iter()) {
                    match (
                        eval_ff_term_in_model(manager, &model, x),
                        eval_ff_term_in_model(manager, &model, y),
                    ) {
                        (Some(vx), Some(vy)) if vx != vy => {
                            equal_known = false;
                            break;
                        }
                        (Some(_), Some(_)) => {}
                        _ => any_unknown = true,
                    }
                }
                if !equal_known || any_unknown {
                    continue; // arguments differ, or unconstrained.
                }
                // Violation: split, results-equal branch first.
                let mut children = vec![UfffChoice {
                    a: a1,
                    b: a2,
                    positive: true,
                }];
                for (&x, &y) in args1.iter().zip(args2.iter()) {
                    if x != y {
                        children.push(UfffChoice {
                            a: x,
                            b: y,
                            positive: false,
                        });
                    }
                }
                return UfffNode::Split(children);
            }
        }
    }
    UfffNode::Model(model)
}

/// A field-and-value pair helper for the scan.
fn field_and_value(
    manager: &TermManager,
    model: &UfffModel,
    term: TermId,
) -> Option<(FieldId, BigUint)> {
    let field = ff_sort_field(manager, term)?;
    let value = model.value_of(term, field).cloned()?;
    Some((field, value))
}

/// The field of a term's sort, when it is a finite field.
fn ff_sort_field(manager: &TermManager, term: TermId) -> Option<FieldId> {
    let t = manager.get(term)?;
    match manager.sorts.get(t.sort).map(|s| &s.kind) {
        Some(SortKind::FiniteField(id)) => Some(*id),
        _ => None,
    }
}

/// Evaluate an FF term under the candidate model (its own field's map).
fn eval_ff_term_in_model(
    manager: &TermManager,
    model: &UfffModel,
    term: TermId,
) -> Option<BigUint> {
    let field = ff_sort_field(manager, term)?;
    let map = &model.per_field.iter().find(|(f, _)| *f == field)?.1;
    nixie_theories::ff_theory::evaluate_term_exact(manager, field, term, map)
}

/// The fields a (possibly application-headed) term mentions.
fn fields_of_term(term: TermId, manager: &TermManager) -> Vec<FieldId> {
    let mut out = Vec::new();
    if let Some(f) = ff_sort_field(manager, term) {
        out.push(f);
    }
    out
}

/// Whether the goal mentions an uninterpreted application with an FF
/// result sort anywhere (explicit stack).
fn goal_uses_ff_uf(assertions: &[TermId], manager: &TermManager) -> bool {
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        let Some(term) = manager.get(t) else {
            continue;
        };
        match &term.kind {
            TermKind::Apply { .. } => {
                if ff_sort_field(manager, t).is_some() {
                    return true;
                }
                stack.extend(nixie_core::ast::get_children(&term.kind));
            }
            _ => stack.extend(nixie_core::ast::get_children(&term.kind)),
        }
    }
    false
}

/// An FF-sorted combinand: pure FF structure, or an uninterpreted
/// application with an FF result sort whose arguments are combinands of
/// their own fields. This is [`is_pure_ff`] widened by exactly the
/// `QF_UFFF` vocabulary.
fn is_ff_combinand(root: TermId, manager: &TermManager) -> bool {
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut stack = vec![root];
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        let Some(term) = manager.get(t) else {
            return false;
        };
        match &term.kind {
            TermKind::FfConst { .. }
            | TermKind::FfAdd(_)
            | TermKind::FfMul(_)
            | TermKind::FfNeg(_)
            | TermKind::FfBitsum(_) => {
                stack.extend(nixie_core::ast::get_children(&term.kind));
            }
            TermKind::Var(_) => {
                if !matches!(
                    manager.sorts.get(term.sort).map(|s| &s.kind),
                    Some(SortKind::FiniteField(_))
                ) {
                    return false;
                }
            }
            TermKind::Apply { args, .. } => {
                if ff_sort_field(manager, t).is_none() {
                    return false;
                }
                stack.extend(args.iter().copied());
            }
            _ => return false,
        }
    }
    true
}

/// Boolean DAG over FF-or-UF atoms — the `dpll_ufff` precondition (the
/// same contract as [`dag_is_ff_boolean`], widened to applications).
fn dag_is_ufff_boolean(root: TermId, manager: &TermManager) -> bool {
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut stack = vec![root];
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        let Some(term) = manager.get(t) else {
            return false;
        };
        match &term.kind {
            TermKind::True | TermKind::False => {}
            TermKind::Eq(a, b) => {
                if !is_ff_combinand(*a, manager) || !is_ff_combinand(*b, manager) {
                    return false;
                }
            }
            TermKind::Not(_)
            | TermKind::And(_)
            | TermKind::Or(_)
            | TermKind::Xor(_, _)
            | TermKind::Implies(_, _)
            | TermKind::Ite(_, _, _) => {
                stack.extend(nixie_core::ast::get_children(&term.kind));
            }
            TermKind::Distinct(args) => {
                for &a in args {
                    if !is_ff_combinand(a, manager) {
                        return false;
                    }
                }
            }
            _ => return false,
        }
    }
    true
}

/// Collect the argument lists of `distinct` terms over FF combinands
/// (explicit stack; the interface cardinality guard consumes them).
fn collect_ff_distincts(root: TermId, manager: &TermManager, out: &mut Vec<SmallVec<[TermId; 4]>>) {
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut stack = vec![root];
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        let Some(term) = manager.get(t) else {
            continue;
        };
        match &term.kind {
            TermKind::Distinct(args) => {
                if args.iter().all(|&a| is_ff_combinand(a, manager)) {
                    out.push(SmallVec::from_slice(args.as_slice()));
                }
                // Distinct arguments can carry structure (applications)
                // with no nested distinct; nothing further to collect.
            }
            TermKind::Eq(_, _) => {}
            TermKind::True | TermKind::False => {}
            TermKind::FfConst { .. }
            | TermKind::FfAdd(_)
            | TermKind::FfMul(_)
            | TermKind::FfNeg(_)
            | TermKind::FfBitsum(_)
            | TermKind::Var(_) => {}
            _ => stack.extend(nixie_core::ast::get_children(&term.kind)),
        }
    }
}

/// A `distinct` family the interface cardinality guard reasons about:
/// the term count and, per pair, the disequality literal that asserts
/// it. Pairs whose equality FOLDS at construction are `None`:
/// `mk_eq(c₁, c₂) → false` means the pair is validly distinct (counts
/// toward k, asserted by nothing); a pair folding to `true` makes the
/// whole family impossible to assert (its Tseitin encoding is
/// permanently false) — such families are dropped at construction and
/// never reach this type.
struct DistinctFamily {
    /// Whether k > p (the pigeonhole precondition; precomputed where
    /// the field table is reachable).
    pigeonhole: bool,
    /// One entry per unordered pair: the `not (a = b)` literal, or
    /// `None` when the equality is validly false (constants differing).
    pair_negs: Vec<Option<TermId>>,
}

/// Build the guard's families from the goal's `distinct` terms
/// (deterministic; pairs in index order). A family whose arguments are
/// not all of one field, or which contains an always-equal pair, is
/// dropped — the guard only reasons about pigeonhole, and an
/// always-equal pair refutes the distinct outright (the Tseitin
/// encoding already makes its branch unreachable), which is not this
/// guard's business.
fn ufff_distinct_families(
    manager: &mut TermManager,
    distincts: &[SmallVec<[TermId; 4]>],
) -> Vec<DistinctFamily> {
    let mut families = Vec::new();
    for args in distincts {
        let Some(first) = args.first() else {
            continue;
        };
        let Some(field) = ff_sort_field(manager, *first) else {
            continue;
        };
        if !args
            .iter()
            .all(|&a| ff_sort_field(manager, a) == Some(field))
        {
            continue;
        }
        let mut pair_negs = Vec::new();
        let mut impossible = false;
        for i in 0..args.len() {
            for j in (i + 1)..args.len() {
                let eq = manager.mk_eq(args[i], args[j]);
                if eq == manager.true_id {
                    // `a = b` valid: the distinct is false everywhere.
                    impossible = true;
                } else if eq == manager.false_id {
                    pair_negs.push(None);
                } else {
                    pair_negs.push(Some(manager.mk_not(eq)));
                }
            }
        }
        if impossible {
            continue;
        }
        let modulus = manager.sorts.field_table().modulus(field).cloned();
        let pigeonhole = modulus
            .as_ref()
            .is_some_and(|m| BigUint::from(args.len()) > *m);
        families.push(DistinctFamily {
            pigeonhole,
            pair_negs,
        });
    }
    families
}

/// The interface cardinality guard: some distinct family whose ENTIRE
/// pairwise disequality set the current Boolean model asserts, over
/// more terms than its field's order. Pigeonhole: k pairwise-distinct
/// elements of 𝔽p need k ≤ p — vacuous at ZK primes, decisive at 𝔽₂/𝔽₃
/// (where the alternative — the tiny-field enumerator finding it
/// through k·(k−1)/2 witness generators — already works, but this
/// decides it before any algebra runs, and covers mid-size primes the
/// enumerator cannot reach).
fn ufff_interface_cardinality_refutes(families: &[DistinctFamily], lits: &[TermId]) -> bool {
    let lit_set: FxHashSet<TermId> = lits.iter().copied().collect();
    families.iter().any(|family| {
        family.pigeonhole
            && family.pair_negs.iter().all(|pair| match pair {
                Some(neg) => lit_set.contains(neg),
                // A validly-distinct pair (constants differing) is
                // asserted by nothing and by everything.
                None => true,
            })
    })
}

/// Complete a candidate arrangement into a full model: unconstrained
/// FF-sorted terms get values, preserving function-hood (equal argument
/// values under one function symbol imply equal results). A completion
/// the pass cannot build returns `None` — the caller answers `Unknown`,
/// never a broken model.
fn ufff_complete(
    manager: &TermManager,
    assertions: &[TermId],
    mut model: UfffModel,
) -> Option<UfffModel> {
    // All FF-sorted terms of the goal (explicit stack).
    let mut terms: Vec<TermId> = Vec::new();
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        let Some(term) = manager.get(t) else {
            continue;
        };
        if ff_sort_field(manager, t).is_some() && !terms.contains(&t) {
            terms.push(t);
        }
        stack.extend(nixie_core::ast::get_children(&term.kind));
    }
    terms.sort_unstable();

    // Which terms were absent from the FF models (unconstrained: they
    // appear under no literal — validate_model guarantees every literal
    // leaf is assigned).
    let mut defaulted: FxHashSet<TermId> = FxHashSet::default();
    for &t in &terms {
        let Some(field) = ff_sort_field(manager, t) else {
            continue;
        };
        if model.value_of(t, field).is_none() {
            defaulted.insert(t);
            if let Some(map) = model.per_field.iter_mut().find(|(f, _)| *f == field) {
                map.1.insert(t, BigUint::default());
            } else {
                let mut map = FxHashMap::default();
                map.insert(t, BigUint::default());
                model.per_field.push((field, map));
            }
        }
    }

    // Function-hood repair over defaulted terms: for same-function
    // application pairs with differing results and (now) equal
    // arguments, make the arguments differ by reassigning a DEFAULTED
    // variable argument — defaulted terms are unconstrained, so moving
    // them breaks nothing. Compound arguments whose leaves are all
    // model-assigned cannot be moved: such a pair would have been a
    // Split in the scan; if one shows up here anyway, decline.
    let mut apps_by_func: FxHashMap<nixie_core::interner::Spur, Vec<TermId>> = FxHashMap::default();
    for (term, func, _) in &model.apps {
        apps_by_func.entry(*func).or_default().push(*term);
    }
    let mut funcs: Vec<_> = apps_by_func
        .into_iter()
        .map(|(func, mut ts)| {
            ts.sort_unstable();
            (func, ts)
        })
        .collect();
    funcs.sort_by_key(|(func, _)| func.into_inner());

    for (_func, apps) in &funcs {
        for w in 0..apps.len() {
            for v in (w + 1)..apps.len() {
                let (a1, a2) = (apps[w], apps[v]);
                let (args1, args2) = match (
                    model.apps.iter().find(|(t, _, _)| *t == a1),
                    model.apps.iter().find(|(t, _, _)| *t == a2),
                ) {
                    (Some((_, _, x)), Some((_, _, y))) => (x.clone(), y.clone()),
                    _ => continue,
                };
                let (f1, r1) = field_and_value(manager, &model, a1)?;
                let (f2, r2) = field_and_value(manager, &model, a2)?;
                if f1 != f2 || r1 == r2 {
                    continue;
                }
                let mut differs = false;
                let mut repair: Option<(FieldId, TermId)> = None;
                for (&x, &y) in args1.iter().zip(args2.iter()) {
                    let vx = eval_ff_term_in_model(manager, &model, x);
                    let vy = eval_ff_term_in_model(manager, &model, y);
                    match (vx, vy) {
                        (Some(vx), Some(vy)) if vx != vy => {
                            differs = true;
                            break;
                        }
                        _ => {
                            // Unevaluable or equal: a defaulted VARIABLE
                            // argument here is the repair handle.
                            if repair.is_none() {
                                for &candidate in &[x, y] {
                                    let is_var = manager
                                        .get(candidate)
                                        .is_some_and(|ct| matches!(ct.kind, TermKind::Var(_)));
                                    if is_var && defaulted.contains(&candidate) {
                                        if let Some(field) = ff_sort_field(manager, candidate) {
                                            repair = Some((field, candidate));
                                            // Keep scanning for a known
                                            // difference first.
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                if differs {
                    continue;
                }
                let Some((field, var)) = repair else {
                    // No handle: honest refusal.
                    tracing::warn!("ufff: no completion handle for a function-hood conflict");
                    return None;
                };
                let modulus = manager.sorts.field_table().modulus(field)?.clone();
                // A fresh value not used anywhere in this field.
                let map = &mut model.per_field.iter_mut().find(|(f, _)| *f == field)?.1;
                let used: FxHashSet<BigUint> = map.values().cloned().collect();
                let mut candidate = BigUint::from(0u8);
                while used.contains(&candidate) {
                    if candidate >= modulus {
                        // Field exhausted: cannot differ — refuted shape;
                        // decline (the SAT loop will block this assignment
                        // through the FF check on a re-run; here we can
                        // only be honest).
                        tracing::warn!("ufff: field exhausted at completion");
                        return None;
                    }
                    candidate += 1u8;
                }
                map.insert(var, candidate);
            }
        }
    }

    // Final gate — the completed arrangement must satisfy function-hood
    // everywhere and every negative literal of the assignment (the FF
    // models did; the defaults could only collide application arguments,
    // which the repair pass above handled, and unconstrained variables,
    // which appear in no literal). One full scan, then hand it back.
    for (_func, apps) in &funcs {
        for w in 0..apps.len() {
            for v in (w + 1)..apps.len() {
                let (a1, a2) = (apps[w], apps[v]);
                let (args1, args2) = match (
                    model.apps.iter().find(|(t, _, _)| *t == a1),
                    model.apps.iter().find(|(t, _, _)| *t == a2),
                ) {
                    (Some((_, _, x)), Some((_, _, y))) => (x, y),
                    _ => continue,
                };
                let (f1, r1) = field_and_value(manager, &model, a1)?;
                let (f2, r2) = field_and_value(manager, &model, a2)?;
                if f1 != f2 || r1 == r2 {
                    continue;
                }
                let mut differs = false;
                for (&x, &y) in args1.iter().zip(args2.iter()) {
                    match (
                        eval_ff_term_in_model(manager, &model, x),
                        eval_ff_term_in_model(manager, &model, y),
                    ) {
                        (Some(vx), Some(vy)) if vx != vy => {
                            differs = true;
                            break;
                        }
                        (Some(_), Some(_)) => {}
                        // An unevaluable argument after completion: a
                        // compound over leaves this pass does not own.
                        // Decline rather than guess.
                        _ => return None,
                    }
                }
                if !differs {
                    tracing::warn!("ufff: completion left a function-hood violation");
                    return None;
                }
            }
        }
    }
    Some(model)
}

#[cfg(test)]
mod fragment_tests {
    use super::*;

    #[test]
    fn field_boolean_encoder_rejects_foreign_atoms_without_a_dispatch_guard() {
        let mut manager = TermManager::new();
        let i = manager.mk_var("i", manager.sorts.int_sort);
        let one = manager.mk_int(1);
        let foreign = manager.mk_eq(i, one);
        let distinct = manager.mk_distinct([i, one]);
        for root in [foreign, distinct] {
            let mut sat = SatSolver::new();
            let mut atoms = FxHashMap::default();
            let mut encoder = FfTseitin {
                sat: &mut sat,
                atom_var: &mut atoms,
            };
            assert!(encoder.encode(root, &mut manager).is_none());
            assert!(atoms.is_empty());
        }
    }
}
