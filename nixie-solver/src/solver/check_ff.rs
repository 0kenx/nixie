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

        // Shape gate: every assertion must be built from FF atoms with
        // Boolean structure only (`and`/`or`/`not`/`ite`/`xor`/`=>`/
        // `distinct`, `=`, `true`/`false`). A foreign-theory leaf anywhere
        // declines the whole goal (the honesty gate answers `unknown`);
        // pure conjunctions take the fast path below; anything with real
        // Boolean structure goes to the lazy DPLL(T).
        let mut has_structure = false;
        for &a in &self.assertions {
            let term = manager.get(a)?;
            match &term.kind {
                TermKind::True | TermKind::False | TermKind::Eq(_, _) | TermKind::Not(_) => {}
                TermKind::And(_)
                | TermKind::Or(_)
                | TermKind::Ite(_, _, _)
                | TermKind::Xor(_, _)
                | TermKind::Implies(_, _)
                | TermKind::Distinct(_) => {
                    has_structure = true;
                    // Structure is allowed only over FF atoms; verify the
                    // whole sub-DAG before committing (a mixed leaf under
                    // the structure would otherwise be abstracted into a
                    // free Boolean — exactly the false-`sat` shape).
                    if !dag_is_ff_boolean(a, manager) {
                        return None;
                    }
                }
                _ => return None, // foreign theory or unowned shape
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
                        let value_term = manager
                            .mk_ff_const(field, into_bigint(value))
                            .expect("the field is interned and prime");
                        combined_model.set(*var, value_term);
                    }
                }
                FfOutcome::Unsat(ff_core) => {
                    // Map the slice indices back to the global literal list.
                    for &i in &ff_core.fact_indices {
                        if let Some(&lit) = slice.get(i) {
                            if let Some(global) = literals.iter().position(|&l| l == lit) {
                                core.push(global);
                            }
                        }
                    }
                    // An empty core cannot happen (check_conjunction
                    // guarantees one), but an unwarranted whole-goal Unsat
                    // is worse than a missed dispatch: only answer Unsat
                    // with a nonempty core.
                    if !core.is_empty() {
                        self.install_ff_core(&literals, &core);
                        return Some(SolverResult::Unsat);
                    }
                    return None;
                }
                FfOutcome::Exhausted => {
                    // The branching closed the search space: genuine UNSAT
                    // (no certificate available — see §8's branch-exhaustion
                    // case).
                    self.install_ff_core(&literals, &[]);
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
                unit_lits.push(encoder.encode(assertion, manager)?);
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

        // 3. The lazy loop.
        loop {
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
                                    let value_term = manager
                                        .mk_ff_const(field, into_bigint(value))
                                        .expect("interned prime field");
                                    model.set(*var_term, value_term);
                                }
                            }
                            FfOutcome::Unsat(_) | FfOutcome::Exhausted => {
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
                    self.ff_terms_unconstrained = false;
                    return Some(SolverResult::Sat);
                }
            }
        }
    }
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
                if is_pure_ff(*a, manager) && is_pure_ff(*b, manager) && !atoms.contains(&t) {
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
                        TermKind::Eq(..) => {
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
