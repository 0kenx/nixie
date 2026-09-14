//! The `QF_FF` decision procedure for a conjunction
//! (the OKTB23 core; `docs/FF_THEORY_DESIGN.md` §5).
//!
//! Input: the asserted literals over one field — `p(x⃗) = 0` and `q(x⃗) ≠ 0`:
//!
//! * **Step 1 — encode** (two passes, like cvc5's `cocoa_encoder`): equalities
//!   become generators `enc(a) − enc(b)`; disequalities become
//!   `(enc(a) − enc(b))·w − 1` with a fresh witness `w` (exact: in a field,
//!   `a ≠ b ⟺ a − b` is invertible); bitsum definitions get a fresh sum
//!   variable and their own generator set (a definition, not a fact —
//!   cores exclude them).
//! * **Step 2 — Gröbner** (degrevlex). Basis `{nonzero constant}` →
//!   **UNSAT**, core = the traced subset of asserted facts.
//! * **Step 3 — `FindZero`** (model construction): an explicit heap stack —
//!   never native recursion (`AGENTS.md` → deep input must not overflow
//!   the stack). At each node: every variable has a linear univariate
//!   `xᵢ − cᵢ` → model; otherwise a brancher: a super-linear univariate
//!   element → branch on its roots; zero-dimensional → branch on a
//!   variable's minimal polynomial; positive-dimensional → round-robin
//!   over values (complete but `p`-sized: at a 254-bit prime it will not
//!   finish, and the budget says so honestly).
//! * **Step 4 — the honesty gate**: [`FfOutcome`] separates `Exhausted`
//!   (search genuinely closed → UNSAT) from `OutOfBudget` (→ `Unknown`,
//!   never `Unsat`).
//! * **Step 5 — validate the model, always**: substitute and evaluate
//!   every asserted literal in 𝔽_p. A model that fails validation is an
//!   internal error surfaced as `Unknown` plus a loud diagnostic, never
//!   `Sat`.
//!
//! `p = 2` has no Montgomery form (the modulus is even), so small fields
//! fall back to **complete enumeration** over the term semantics — the
//! design's "brute enumeration is viable and complete at tiny fields",
//! on the same code path, not a second architecture.

use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::sort::SortKind;
use nixie_core::sort::field::FieldId;
use nixie_math::ff::field::{FieldCtx, Limbs};
use nixie_math::ff::grobner::{GrobnerBudget, GrobnerError, grobner_basis, minimal_polynomial};
use nixie_math::ff::poly::MPoly;
use nixie_math::ff::roots::{RootBudget, RootError, roots as uni_roots};
use nixie_math::ff::uni_poly::UniPoly;
use nixie_math::polynomial::{Monomial, Var};
use num_bigint::BigUint;
use num_traits::{One, Zero};
use rustc_hash::FxHashMap;

/// The verdict of a finite-field check. The last variants are the honesty
/// gate: a search that stopped because its budget ran out is **not** an
/// answer.
#[derive(Debug)]
pub enum FfOutcome {
    /// SAT with a model: variable term → field element (raw residue).
    Model(FfModel),
    /// UNSAT with a traced core: the indices (into the input literal list)
    /// of asserted facts whose generators appear with nonzero cofactor in
    /// the `1 ∈ I` certificate.
    Unsat(FfCore),
    /// The branching was exhaustive and empty: UNSAT is genuine.
    Exhausted,
    /// The budget ran out at `where_` → `Unknown`, never `Unsat`.
    OutOfBudget {
        /// Where the budget ran out.
        where_: &'static str,
    },
    /// The goal has a shape this procedure does not own (mixed logic,
    /// non-literal assertions) or a candidate model failed validation.
    /// `Unknown`, never a guess.
    InvalidModel(String),
}

/// A satisfying assignment.
#[derive(Debug, Clone)]
pub struct FfModel {
    /// Variable term → residue in `[0, p)`.
    values: FxHashMap<TermId, BigUint>,
}

impl FfModel {
    /// The residue assigned to a variable, if any.
    #[must_use]
    pub fn value_of(&self, var: TermId) -> Option<&BigUint> {
        self.values.get(&var)
    }

    /// All assignments (variable → residue).
    #[must_use]
    pub fn assignments(&self) -> &FxHashMap<TermId, BigUint> {
        &self.values
    }

    fn insert(&mut self, var: TermId, value: BigUint) {
        self.values.insert(var, value);
    }
}

/// An UNSAT core: indices into the asserted-literal list.
#[derive(Debug, Clone)]
pub struct FfCore {
    /// Indices of the asserted facts whose generators carry nonzero
    /// cofactor in the certificate. Definitional generators (bitsums,
    /// witnesses) are excluded by construction.
    pub fact_indices: Vec<usize>,
}

/// The eager whole-problem FF dispatcher: decides a conjunctive `QF_FF`
/// goal for one field. `assertions` must be literals (`=`, `not =`,
/// `true`, `false`) — the caller (the solver) routes only pure
/// conjunctive goals here, matching the design's Phase-3 scope.
///
/// `budget_steps` bounds every phase in tick counters (encoding steps,
/// S-pairs, reductions, search nodes, root finding) — never wall-clock.
#[must_use]
pub fn check_conjunction(
    manager: &TermManager,
    field: FieldId,
    assertions: &[TermId],
    budget_steps: u64,
) -> FfOutcome {
    let Some(modulus) = manager.sorts.field_table().modulus(field).cloned() else {
        return FfOutcome::InvalidModel("field has no prime modulus".to_string());
    };

    // An asserted `false` is UNSAT regardless of the path — and only this
    // fast path can name it as a single-literal core.
    if let Some(&false_lit) = assertions.iter().find(|&&a| a == manager.false_id) {
        let index = assertions.iter().position(|&a| a == false_lit).unwrap_or(0);
        return FfOutcome::Unsat(FfCore {
            fact_indices: vec![index],
        });
    }

    // Collect the field's variables first — needed by both paths, and the
    // enumeration cap decision is theirs to make.
    let vars = collect_field_variables(manager, field, assertions);
    match vars {
        Err(e) => FfOutcome::InvalidModel(e),
        Ok(vars) => {
            // Enumeration viability: p^n ≤ 2^22. Covers F_2 (n ≤ 22) and
            // the tiny odd primes the oracle tests exercise; declines the
            // 254-bit case to the GB path.
            let bits = modulus.bits() * vars.len().max(1) as u64;
            if bits <= 22 {
                enumerate(manager, field, &modulus, &vars, assertions, budget_steps)
            } else {
                let Ok(f) = FieldCtx::new(modulus) else {
                    return FfOutcome::InvalidModel(
                        "even modulus with too many variables for enumeration".to_string(),
                    );
                };
                grobner_path(manager, field, &f, assertions, budget_steps)
            }
        }
    }
}

/// The GB + FindZero path (odd primes).
fn grobner_path(
    manager: &TermManager,
    field: FieldId,
    f: &FieldCtx,
    assertions: &[TermId],
    budget_steps: u64,
) -> FfOutcome {
    // ---- Step 1: encode (two passes) ----
    let mut enc = Encoder::new(f, field);
    let mut generators: Vec<Generator> = Vec::new();
    for (index, &assertion) in assertions.iter().enumerate() {
        let Some(term) = manager.get(assertion) else {
            return FfOutcome::InvalidModel(format!("dangling term {assertion:?}"));
        };
        match &term.kind {
            TermKind::True => {}
            TermKind::False => {
                return FfOutcome::Unsat(FfCore {
                    fact_indices: vec![index],
                });
            }
            TermKind::Eq(a, b) => match enc.encode_pair(manager, *a, *b, budget_steps) {
                Some((pa, pb)) => generators.push(Generator::Fact {
                    index,
                    poly: pa.sub(f, &pb),
                }),
                None => return FfOutcome::OutOfBudget { where_: "encoding" },
            },
            TermKind::Not(inner) => {
                let Some(inner_term) = manager.get(*inner) else {
                    return FfOutcome::InvalidModel(format!("dangling term {inner:?}"));
                };
                match &inner_term.kind {
                    TermKind::Eq(a, b) => match enc.encode_pair(manager, *a, *b, budget_steps) {
                        Some((pa, pb)) => {
                            let w = enc.fresh_witness(*a, *b);
                            let mut w_poly = MPoly::zero();
                            w_poly.add_term(f, Monomial::from_var(w), &f.one());
                            let one = MPoly::constant(f, &f.one());
                            generators.push(Generator::Witness {
                                index,
                                poly: pa.sub(f, &pb).mul(f, &w_poly).sub(f, &one),
                            });
                        }
                        None => {
                            return FfOutcome::OutOfBudget { where_: "encoding" };
                        }
                    },
                    _ => {
                        return FfOutcome::InvalidModel(
                            "unsupported literal shape under not".to_string(),
                        );
                    }
                }
            }
            _ => {
                return FfOutcome::InvalidModel(
                    "non-literal assertion reached the FF check".to_string(),
                );
            }
        }
    }
    for poly in std::mem::take(&mut enc.bitsum_generators) {
        generators.push(Generator::Bitsum { poly });
    }

    let input_polys: Vec<MPoly> = generators
        .iter()
        .map(|g| match g {
            Generator::Fact { poly, .. }
            | Generator::Witness { poly, .. }
            | Generator::Bitsum { poly } => poly.clone(),
        })
        .collect();

    if input_polys.is_empty() {
        let mut model = FfModel {
            values: FxHashMap::default(),
        };
        for var in enc.var_terms() {
            model.insert(var, BigUint::from(0u8));
        }
        return FfOutcome::Model(model);
    }

    // ---- Step 2: Gröbner, degrevlex ----
    let mut gbudget = GrobnerBudget::new(budget_steps);
    match grobner_basis(f, &input_polys, &mut gbudget) {
        Err(GrobnerError::Budget) => FfOutcome::OutOfBudget {
            where_: "Gröbner basis",
        },
        Ok(basis) => {
            if basis.contains_nonzero_constant() {
                return traced_unsat(&generators, &basis);
            }
            // ---- Step 3: FindZero ----
            find_zero(f, &basis, &enc, budget_steps)
        }
    }
}

/// Extract the traced core from a `1 ∈ I` basis.
fn traced_unsat(
    generators: &[Generator],
    basis: &nixie_math::ff::grobner::GrobnerBasis,
) -> FfOutcome {
    let Some(witness) = basis.constant_witness() else {
        return FfOutcome::OutOfBudget {
            where_: "Gröbner basis",
        };
    };
    let mut fact_indices: Vec<usize> = Vec::new();
    for (gen_idx, generator) in generators.iter().enumerate() {
        let carries = witness.cofactors.get(gen_idx).is_some_and(|c| !c.is_zero());
        if carries {
            match generator {
                Generator::Fact { index, .. } | Generator::Witness { index, .. } => {
                    // A witness generator is *definitionally* tied to its
                    // disequality: the core must name the disequality too
                    // (its generator alone cannot produce 1 without the
                    // fact side).
                    fact_indices.push(*index);
                }
                Generator::Bitsum { .. } => {}
            }
        }
    }
    if fact_indices.is_empty() {
        // The certificate rests only on definitions — not reachable with
        // a sound encoder, but an empty core must never be returned as
        // "UNSAT by nothing": fall back to naming every fact.
        fact_indices = generators
            .iter()
            .filter_map(|g| match g {
                Generator::Fact { index, .. } | Generator::Witness { index, .. } => Some(*index),
                Generator::Bitsum { .. } => None,
            })
            .collect();
    }
    FfOutcome::Unsat(FfCore { fact_indices })
}

/// One encoded generator, with its provenance for core extraction.
enum Generator {
    /// An asserted equality's polynomial.
    Fact {
        /// Index of the asserted literal.
        index: usize,
        /// The polynomial.
        poly: MPoly,
    },
    /// A disequality witness generator `(a−b)·w − 1`.
    Witness {
        /// Index of the asserted disequality literal.
        index: usize,
        /// The polynomial.
        poly: MPoly,
    },
    /// A bitsum definition `s − Σ 2ⁱ bᵢ` (excluded from cores).
    Bitsum {
        /// The polynomial.
        poly: MPoly,
    },
}

// ================= Step 1: the encoder =================

/// Term → polynomial encoder. Pass 1 registers every FF-sorted variable
/// (assigning ring indices); pass 2 builds polynomials against that fixed
/// variable map — the two-pass discipline cvc5's `cocoa_encoder` uses,
/// because the ring's variables must be known before any polynomial is
/// built.
struct Encoder<'a> {
    f: &'a FieldCtx,
    field: FieldId,
    var_index: FxHashMap<TermId, Var>,
    next_var: Var,
    /// Bitsum definition generators accumulated during encoding.
    bitsum_generators: Vec<MPoly>,
    /// Fresh witness variables minted for disequalities (pair key → ring
    /// var), excluded from models.
    witnesses: FxHashMap<(TermId, TermId), Var>,
}

impl<'a> Encoder<'a> {
    fn new(f: &'a FieldCtx, field: FieldId) -> Self {
        Self {
            f,
            field,
            var_index: FxHashMap::default(),
            next_var: 0,
            bitsum_generators: Vec::new(),
            witnesses: FxHashMap::default(),
        }
    }

    /// All FF-sorted variable terms registered (index-sorted).
    fn var_terms(&self) -> Vec<TermId> {
        let mut terms: Vec<TermId> = self.var_index.keys().copied().collect();
        terms.sort_unstable();
        terms
    }

    fn is_field_sort(&self, manager: &TermManager, sort: nixie_core::sort::SortId) -> bool {
        matches!(
            manager.sorts.get(sort).map(|s| &s.kind),
            Some(SortKind::FiniteField(id)) if *id == self.field
        )
    }

    /// Pass 1 for one term: register FF variables (explicit stack — user
    /// terms can be arbitrarily deep).
    fn register_vars(
        &mut self,
        manager: &TermManager,
        root: TermId,
        budget: u64,
    ) -> Result<(), ()> {
        let mut visited: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
        let mut stack: Vec<TermId> = vec![root];
        let mut steps = 0u64;
        while let Some(t) = stack.pop() {
            steps += 1;
            if steps > budget {
                return Err(());
            }
            if !visited.insert(t) {
                continue;
            }
            let Some(term) = manager.get(t) else {
                continue;
            };
            if matches!(term.kind, TermKind::Var(_))
                && self.is_field_sort(manager, term.sort)
                && !self.var_index.contains_key(&t)
            {
                self.var_index.insert(t, self.next_var);
                self.next_var += 1;
            }
            stack.extend(nixie_core::ast::get_children(&term.kind));
        }
        Ok(())
    }

    /// Encode both sides of an equality (registering variables first).
    fn encode_pair(
        &mut self,
        manager: &TermManager,
        a: TermId,
        b: TermId,
        budget: u64,
    ) -> Option<(MPoly, MPoly)> {
        self.register_vars(manager, a, budget).ok()?;
        self.register_vars(manager, b, budget).ok()?;
        let pa = self.encode(manager, a, budget)?;
        let pb = self.encode(manager, b, budget)?;
        Some((pa, pb))
    }

    /// A fresh witness ring variable for the disequality between `a` and
    /// `b` (one per pair — deduplicated so repeated disequalities share).
    fn fresh_witness(&mut self, a: TermId, b: TermId) -> Var {
        let key = if a.0 <= b.0 { (a, b) } else { (b, a) };
        *self.witnesses.entry(key).or_insert_with(|| {
            let v = self.next_var;
            self.next_var += 1;
            v
        })
    }

    /// Pass 2: the polynomial of a term. Explicit stack with combine
    /// frames and an operand stack of completed polynomials — the same
    /// discipline every other term walk in this codebase follows.
    fn encode(&mut self, manager: &TermManager, root: TermId, budget: u64) -> Option<MPoly> {
        enum Combine {
            Add(usize),
            Mul(usize),
            Neg,
            /// The bitsum's definition generator is emitted and the fresh
            /// sum variable is the value.
            Bitsum(TermId, usize),
        }
        let mut results: Vec<MPoly> = Vec::new();
        let mut stack: Vec<nixie_core::ast::TermId> = vec![root];
        let mut combines: Vec<Combine> = Vec::new();
        let mut steps = 0u64;

        while let Some(t) = stack.pop() {
            steps += 1;
            if steps > budget {
                return None;
            }
            let term = manager.get(t)?;
            match &term.kind {
                TermKind::FfConst { value, field } => {
                    if *field != self.field {
                        return None; // mixed fields: refused upstream, guard anyway
                    }
                    let mut p = MPoly::zero();
                    p.add_term(
                        self.f,
                        Monomial::unit(),
                        &self.f.from_bigint(&value.clone()),
                    );
                    results.push(p);
                }
                TermKind::Var(_) => {
                    // FF-sorted variables were registered in pass 1;
                    // anything else here is a shape violation.
                    let var = self.var_index.get(&t).copied()?;
                    let mut p = MPoly::zero();
                    p.add_term(self.f, Monomial::from_var(var), &self.f.one());
                    results.push(p);
                }
                TermKind::FfAdd(children) => {
                    combines.push(Combine::Add(children.len()));
                    for &c in children.iter().rev() {
                        stack.push(c);
                    }
                }
                TermKind::FfMul(children) => {
                    combines.push(Combine::Mul(children.len()));
                    for &c in children.iter().rev() {
                        stack.push(c);
                    }
                }
                TermKind::FfNeg(child) => {
                    combines.push(Combine::Neg);
                    stack.push(*child);
                }
                TermKind::FfBitsum(children) => {
                    combines.push(Combine::Bitsum(t, children.len()));
                    for &c in children.iter().rev() {
                        stack.push(c);
                    }
                }
                _ => return None, // unsupported shape — refused
            }
        }

        while let Some(combine) = combines.pop() {
            match combine {
                Combine::Add(n) => {
                    if results.len() < n {
                        return None;
                    }
                    let mut sum = MPoly::zero();
                    for _ in 0..n {
                        sum = sum.add(self.f, &results.pop()?);
                    }
                    results.push(sum);
                }
                Combine::Mul(n) => {
                    if results.len() < n {
                        return None;
                    }
                    let mut prod = MPoly::constant(self.f, &self.f.one());
                    for _ in 0..n {
                        let p = results.pop()?;
                        prod = prod.mul(self.f, &p);
                    }
                    results.push(prod);
                }
                Combine::Neg => {
                    let p = results.pop()?;
                    results.push(p.neg(self.f));
                }
                Combine::Bitsum(_t, n) => {
                    if results.len() < n {
                        return None;
                    }
                    // Σ 2ⁱ bᵢ in order: the children were pushed in
                    // reverse, so the last n results are b₀ … bₙ₋₁ in
                    // order.
                    let drained: Vec<MPoly> = results.split_off(results.len() - n);
                    let s = {
                        let v = self.next_var;
                        self.next_var += 1;
                        v
                    };
                    let mut definition = MPoly::zero();
                    definition.add_term(self.f, Monomial::from_var(s), &self.f.one());
                    let mut power = self.f.one();
                    for p in drained {
                        definition = definition.sub(self.f, &p.scale(self.f, &power));
                        power = self
                            .f
                            .mul(&power, &self.f.from_biguint(&BigUint::from(2u8)));
                    }
                    self.bitsum_generators.push(definition);
                    let mut out = MPoly::zero();
                    out.add_term(self.f, Monomial::from_var(s), &self.f.one());
                    results.push(out);
                }
            }
        }
        if results.len() != 1 {
            return None;
        }
        results.pop()
    }
}

// ================= Step 3: FindZero =================

/// The branching search for a rational point: one explicit heap stack of
/// nodes (basis + partial assignment), never native recursion.
fn find_zero(
    f: &FieldCtx,
    basis: &nixie_math::ff::grobner::GrobnerBasis,
    enc: &Encoder<'_>,
    budget_steps: u64,
) -> FfOutcome {
    struct Node {
        basis: nixie_math::ff::grobner::GrobnerBasis,
        inputs: Vec<MPoly>,
    }

    let mut stack: Vec<Node> = vec![Node {
        basis: basis.clone(),
        inputs: basis.inputs.clone(),
    }];
    let mut steps = 0u64;
    let variables: Vec<Var> = {
        let mut vs: Vec<Var> = (0..enc.next_var).collect();
        vs.sort_unstable();
        vs
    };

    while let Some(node) = stack.pop() {
        steps += 1;
        if steps > budget_steps {
            return FfOutcome::OutOfBudget {
                where_: "FindZero search",
            };
        }
        // 1 ∈ I → dead branch.
        if node.basis.contains_nonzero_constant() {
            continue;
        }

        // Every variable linear-univariate → the single point is the model.
        let linear: FxHashMap<Var, Limbs> = node
            .basis
            .linear_univariates(f)
            .into_iter()
            .collect::<FxHashMap<_, _>>();
        if linear.len() == variables.len() {
            let mut model = FfModel {
                values: FxHashMap::default(),
            };
            for (term, var) in &enc.var_index {
                if let Some(val) = linear.get(var) {
                    model.insert(*term, f.to_biguint(val));
                }
            }
            return FfOutcome::Model(model);
        }

        // Brancher 1: a super-linear univariate element of the GB.
        let mut brancher: Option<(Var, Vec<Limbs>)> = None;
        for g in &node.basis.basis {
            let Some(lm) = g.poly.lm(nixie_math::ff::grobner::DEGREVLEX) else {
                continue;
            };
            if lm.vars().len() != 1 || lm.vars()[0].power == 1 {
                continue;
            }
            let x = lm.vars()[0].var;
            let univariate = g
                .poly
                .terms_iter()
                .all(|(m, _)| m.vars().iter().all(|vp| vp.var == x));
            if !univariate {
                continue;
            }
            let deg = lm.vars()[0].power as usize;
            let mut coeffs: Vec<Limbs> = vec![f.zero(); deg + 1];
            for (m, c) in g.poly.terms_iter() {
                let d = if m.is_unit() { 0 } else { m.vars()[0].power };
                coeffs[d as usize] = c.clone();
            }
            let uni = UniPoly::from_coeffs(coeffs);
            let mut rbudget = RootBudget::new(budget_steps);
            match uni_roots(f, &uni, &mut rbudget) {
                Err(RootError::Budget) | Ok(None) => {
                    return FfOutcome::OutOfBudget {
                        where_: "root finding",
                    };
                }
                Ok(Some(roots)) => {
                    brancher = Some((x, roots));
                    break;
                }
            }
        }

        let (var, values) = if let Some(b) = brancher {
            b
        } else {
            // Brancher 2: zero-dimensional → minimal polynomial of an
            // unassigned variable. Brancher 3: positive-dimensional →
            // value enumeration (complete, p-sized).
            let Some(free_var) = variables
                .iter()
                .copied()
                .find(|v| !linear.contains_key(v))
                .or_else(|| variables.first().copied())
            else {
                return FfOutcome::InvalidModel("no variables to branch on".to_string());
            };
            if node.basis.is_zero_dimensional(&variables) {
                let mut mbudget = GrobnerBudget::new(budget_steps);
                match minimal_polynomial(f, &node.basis, free_var, &variables, &mut mbudget) {
                    Some(minpoly) => {
                        let mut rbudget = RootBudget::new(budget_steps);
                        match uni_roots(f, &minpoly, &mut rbudget) {
                            Err(RootError::Budget) | Ok(None) => {
                                return FfOutcome::OutOfBudget {
                                    where_: "root finding",
                                };
                            }
                            Ok(Some(roots)) if roots.is_empty() => continue, // dead branch
                            Ok(Some(roots)) => (free_var, roots),
                        }
                    }
                    None => {
                        return FfOutcome::OutOfBudget {
                            where_: "minimal polynomial",
                        };
                    }
                }
            } else {
                // Positive-dimensional: enumerate the residues of the
                // free variable. Complete — any solution assigns it some
                // value — but p-sized; the budget fires honestly at a
                // large prime.
                let p = f.modulus();
                if *p > BigUint::from(1_000_000u64) {
                    return FfOutcome::OutOfBudget {
                        where_: "positive-dimensional enumeration",
                    };
                }
                let count: u64 = p.to_string().parse().unwrap_or(u64::MAX);
                let vals: Vec<Limbs> = (0..count)
                    .map(|v| f.from_biguint(&BigUint::from(v)))
                    .collect();
                (free_var, vals)
            }
        };

        // Branch: add x − value, recompute the basis (recompute, never
        // incrementally roll back — the design's scoping discipline).
        for value in values {
            let mut poly = MPoly::zero();
            poly.add_term(f, Monomial::from_var(var), &f.one());
            let mut const_poly = MPoly::zero();
            const_poly.add_term(f, Monomial::unit(), &value.clone());
            let new_gen = poly.sub(f, &const_poly);
            let mut inputs = node.inputs.clone();
            inputs.push(new_gen);
            let mut gbudget = GrobnerBudget::new(budget_steps);
            match grobner_basis(f, &inputs, &mut gbudget) {
                Err(GrobnerError::Budget) => {
                    return FfOutcome::OutOfBudget {
                        where_: "Gröbner basis",
                    };
                }
                Ok(child) => stack.push(Node {
                    basis: child,
                    inputs,
                }),
            }
        }
    }
    // The stack emptied without a model: the branching was exhaustive —
    // UNSAT is genuine (Step 4's honesty gate: this is *not* a budget
    // outcome).
    FfOutcome::Exhausted
}

// ================= Enumeration path (tiny fields) =================

/// Collect the FF-sorted variables of the assertions; error on any
/// non-literal or foreign-theory shape.
fn collect_field_variables(
    manager: &TermManager,
    field: FieldId,
    assertions: &[TermId],
) -> Result<Vec<TermId>, String> {
    let mut vars: Vec<TermId> = Vec::new();
    let mut visited: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        let Some(term) = manager.get(t) else {
            return Err(format!("dangling term {t:?}"));
        };
        match &term.kind {
            TermKind::Var(_) => {
                if matches!(
                    manager.sorts.get(term.sort).map(|s| &s.kind),
                    Some(SortKind::FiniteField(id)) if *id == field
                ) && !vars.contains(&t)
                {
                    vars.push(t);
                }
            }
            TermKind::FfConst { field: id, .. } => {
                if *id != field {
                    return Err("mixed fields in one check".to_string());
                }
            }
            TermKind::FfAdd(_)
            | TermKind::FfMul(_)
            | TermKind::FfNeg(_)
            | TermKind::FfBitsum(_)
            | TermKind::Eq(_, _)
            | TermKind::Not(_)
            | TermKind::True
            | TermKind::False => {
                stack.extend(nixie_core::ast::get_children(&term.kind));
            }
            _ => return Err("non-FF structure inside the conjunction".to_string()),
        }
    }
    vars.sort_unstable();
    Ok(vars)
}

/// Complete enumeration for tiny fields: every assignment of `vars`
/// evaluated against the assertions' exact semantics. `p^n ≤ 2^22` is the
/// caller's guarantee (checked in [`check_conjunction`]).
fn enumerate(
    manager: &TermManager,
    field: FieldId,
    modulus: &BigUint,
    vars: &[TermId],
    assertions: &[TermId],
    budget: u64,
) -> FfOutcome {
    // Mixed-radix enumeration over p^n points.
    let n = vars.len();
    let total: BigUint = num_traits::Pow::pow(modulus.clone(), n);
    let total_u64: Option<u64> = (&total).try_into().ok();
    let Some(total_u64) = total_u64.filter(|&t| t <= (1 << 22)) else {
        return FfOutcome::OutOfBudget {
            where_: "enumeration space",
        };
    };

    let mut assignment: FxHashMap<TermId, BigUint> = FxHashMap::default();
    let mut counter = BigUint::zero();
    for _ in 0..total_u64 {
        // Decode the counter into digits base p.
        let mut rest = counter.clone();
        for var in vars {
            let digit = &rest % modulus;
            rest = &rest / modulus;
            assignment.insert(*var, digit);
        }
        // Budget: one unit per candidate point — enumeration is complete
        // only when it finishes, and finishing must be distinguishable
        // from stopping.
        if u64::from(counter.to_string().parse::<u32>().unwrap_or(u32::MAX)) > budget {
            return FfOutcome::OutOfBudget {
                where_: "enumeration space",
            };
        }
        let all_satisfied = assertions.iter().all(|&a| {
            matches!(
                eval_literal(manager, field, modulus, a, &assignment),
                Some(true)
            )
        });
        if all_satisfied {
            let mut model = FfModel {
                values: FxHashMap::default(),
            };
            for var in vars {
                model.insert(*var, assignment[var].clone());
            }
            return FfOutcome::Model(model);
        }
        counter += 1u8;
    }
    FfOutcome::Exhausted
}

/// Exact literal evaluation under an assignment (the term-language
/// semantics — the same fold the model validator cross-checks against the
/// polynomial encoding).
fn eval_literal(
    manager: &TermManager,
    field: FieldId,
    modulus: &BigUint,
    root: TermId,
    assignment: &FxHashMap<TermId, BigUint>,
) -> Option<bool> {
    match &manager.get(root)?.kind {
        TermKind::True => Some(true),
        TermKind::False => Some(false),
        TermKind::Eq(a, b) => {
            let va = eval_term(manager, field, modulus, *a, assignment)?;
            let vb = eval_term(manager, field, modulus, *b, assignment)?;
            Some(va == vb)
        }
        TermKind::Not(inner) => eval_literal(manager, field, modulus, *inner, assignment).map_not(),
        _ => None,
    }
}

/// Exact FF-term evaluation in `BigUint` arithmetic mod `p` (explicit
/// stack; used by the enumeration path and reusable for debugging).
fn eval_term(
    manager: &TermManager,
    field: FieldId,
    modulus: &BigUint,
    root: TermId,
    assignment: &FxHashMap<TermId, BigUint>,
) -> Option<BigUint> {
    enum Combine {
        Add(usize),
        Mul(usize),
        Neg,
        Bitsum(usize),
    }
    let mut results: Vec<BigUint> = Vec::new();
    let mut stack: Vec<TermId> = vec![root];
    let mut combines: Vec<Combine> = Vec::new();
    while let Some(t) = stack.pop() {
        let term = manager.get(t)?;
        match &term.kind {
            TermKind::FfConst { value, field: id } => {
                if *id != field {
                    return None;
                }
                results.push(num_bigint::BigInt::to_biguint(value)? % modulus);
            }
            TermKind::Var(_) => {
                results.push(assignment.get(&t).cloned()?);
            }
            TermKind::FfAdd(children) => {
                combines.push(Combine::Add(children.len()));
                for &c in children.iter().rev() {
                    stack.push(c);
                }
            }
            TermKind::FfMul(children) => {
                combines.push(Combine::Mul(children.len()));
                for &c in children.iter().rev() {
                    stack.push(c);
                }
            }
            TermKind::FfNeg(child) => {
                combines.push(Combine::Neg);
                stack.push(*child);
            }
            TermKind::FfBitsum(children) => {
                combines.push(Combine::Bitsum(children.len()));
                for &c in children.iter().rev() {
                    stack.push(c);
                }
            }
            _ => return None,
        }
    }
    while let Some(combine) = combines.pop() {
        match combine {
            Combine::Add(n) => {
                let mut sum = BigUint::zero();
                for _ in 0..n {
                    sum = (sum + results.pop()?) % modulus;
                }
                results.push(sum);
            }
            Combine::Mul(n) => {
                let mut prod = BigUint::one();
                for _ in 0..n {
                    prod = (prod * results.pop()?) % modulus;
                }
                results.push(prod);
            }
            Combine::Neg => {
                let v = results.pop()?;
                results.push((modulus - v) % modulus);
            }
            Combine::Bitsum(n) => {
                let drained = results.split_off(results.len() - n);
                let mut acc = BigUint::zero();
                let mut power = BigUint::one();
                for v in drained {
                    acc = (acc + &power * v) % modulus;
                    power = (&power << 1) % modulus;
                }
                results.push(acc);
            }
        }
    }
    if results.len() != 1 {
        return None;
    }
    results.pop()
}

/// `Option<bool>` negation without the identity-extension footgun.
trait MapNot {
    fn map_not(self) -> Self;
}

impl MapNot for Option<bool> {
    fn map_not(self) -> Self {
        self.map(|b| !b)
    }
}

// ================= Step 5: validation =================

/// Substitute the model into every asserted literal and evaluate in 𝔽_p —
/// through the *polynomial* encoding, so the validator is a second,
/// independent implementation of the semantics (an encoder bug that made
/// the search accept a non-model is exactly what this catches).
///
/// `Ok(())` when the model satisfies everything; the error string
/// describes the first violated literal (a loud diagnostic — the caller
/// turns this into `Unknown`, never `Sat`).
pub fn validate_model(
    manager: &TermManager,
    field: FieldId,
    assertions: &[TermId],
    model: &FfModel,
) -> Result<(), String> {
    // Direct term evaluation under the assignment: independent of the
    // polynomial encoder (Step 5's "exact and costs one pass").
    let Some(modulus) = manager.sorts.field_table().modulus(field).cloned() else {
        return Err("field has no prime modulus".to_string());
    };
    for &assertion in assertions {
        match eval_literal(manager, field, &modulus, assertion, &model.values) {
            Some(true) => {}
            Some(false) => {
                return Err(format!(
                    "model violates assertion {assertion:?}: exact evaluation failed"
                ));
            }
            None => {
                return Err(format!(
                    "assertion {assertion:?} could not be evaluated under the model \
                     (unassigned variable or unsupported shape)"
                ));
            }
        }
    }
    Ok(())
}
