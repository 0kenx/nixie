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
//!
//! **`QF_UFFF` (FF ⊕ EUF).** An uninterpreted application with an FF
//! result sort (`f : 𝔽pⁿ → 𝔽p`) is an **opaque ring variable** to every
//! walk here: the encoder mints it a variable like a `Var`, the
//! enumerator assigns it like one, and the exact evaluator looks it up
//! in the assignment. Application *arguments* are never descended into
//! (they may belong to other fields, whose slices own them). Everything
//! EUF knows about these variables — asserted equalities and
//! disequalities, and the congruences `x = y ⟹ f(x) = f(y)` — arrives as
//! ordinary literals from the combination layer
//! (`nixie-solver/src/solver/check_ff.rs`'s `dpll_ufff`), so this module
//! needs no e-graph of its own.

use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::sort::SortKind;
use nixie_core::sort::field::FieldId;
use nixie_math::ff::field::{FieldCtx, Limbs};
use nixie_math::ff::grobner::{
    DEGREVLEX, GrobnerBasis, GrobnerBudget, GrobnerError, grobner_basis, minimal_polynomial,
    normal_form,
};
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
    /// The checkable object that justifies the UNSAT (§8). `None` on the
    /// paths with no certificate (branch exhaustion, enumeration) — those
    /// must degrade to `Unknown` in certified mode, never pose as proved.
    pub certificate: Option<FfCertificate>,
}

/// An independently checkable UNSAT certificate for a finite-field
/// conjunction.
#[derive(Debug, Clone)]
pub enum FfCertificate {
    /// Weak Nullstellensatz: `Σ cᵢ · fᵢ = 1` over the listed asserted
    /// literals' encoded generators. Verification re-encodes the literals
    /// and re-multiplies — one pass of polynomial arithmetic, independent
    /// of the Gröbner machinery that produced the cofactors.
    IdealMembership {
        /// The field the certificate lives in.
        field: FieldId,
        /// The full generator list: (asserted-literal index for fact
        /// generators, `None` for witness/bitsum definitions), with the
        /// polynomial. Index-aligned with `cofactors`.
        generators: Vec<(Option<usize>, MPoly)>,
        /// The cofactors: `Σ cofactors[i] · generators[i].1 = 1`.
        cofactors: Vec<MPoly>,
    },
    /// Pigeonhole: a `distinct` over `k` terms of a field with order `p`
    /// and `k > p`. Verification re-reads the literal and the field's
    /// order from the sort table.
    Cardinality {
        /// The field.
        field: FieldId,
        /// The literal index of the `distinct`.
        literal: usize,
        /// The term count.
        k: usize,
    },
}

impl FfCertificate {
    /// Re-verify the certificate against the original assertions:
    /// re-encode the named literals and re-multiply (IdealMembership), or
    /// re-read the distinct count and the field order (Cardinality).
    /// `false` on any mismatch — the caller fails closed.
    #[must_use]
    pub fn verify(&self, manager: &TermManager, assertions: &[TermId]) -> bool {
        match self {
            FfCertificate::IdealMembership {
                field,
                generators,
                cofactors,
            } => {
                if generators.len() != cofactors.len() || generators.is_empty() {
                    return false;
                }
                let Some(modulus) = manager.sorts.field_table().modulus(*field).cloned() else {
                    return false;
                };
                let Ok(f) = FieldCtx::new(modulus) else {
                    return false;
                };
                // Replay the deterministic encoding over the same
                // assertions: same variable registration order, same
                // witness minting, bitsum definitions last — the
                // generator list must reproduce exactly.
                let Ok((_enc, replay)) =
                    encode_generators(manager, *field, &f, assertions, 1 << 24)
                else {
                    return false;
                };
                if replay.len() != generators.len() {
                    return false;
                }
                let mut acc = MPoly::zero();
                for (((recorded_literal, recorded_poly), replayed), cofactor) in
                    generators.iter().zip(&replay).zip(cofactors)
                {
                    if recorded_literal != &replayed.literal || recorded_poly != &replayed.poly {
                        return false;
                    }
                    acc = acc.add(&f, &cofactor.mul(&f, recorded_poly));
                }
                // Σ cᵢ fᵢ must equal a NONZERO constant (rescaleable to
                // 1; any nonzero constant is a valid refutation).
                acc.is_nonzero_constant()
            }
            FfCertificate::Cardinality { field, literal, k } => {
                let Some(&assertion) = assertions.get(*literal) else {
                    return false;
                };
                let Some(term) = manager.get(assertion) else {
                    return false;
                };
                let TermKind::Distinct(args) = &term.kind else {
                    return false;
                };
                if args.len() != *k {
                    return false;
                }
                let Some(modulus) = manager.sorts.field_table().modulus(*field) else {
                    return false;
                };
                BigUint::from(*k) > *modulus
            }
        }
    }
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
            // `false` needs no field certificate: the Boolean skeleton
            // refutes it, which certified mode's LRAT kernel proves.
            certificate: None,
        });
    }

    // ---- The cardinality guard (§7) ----
    // A `distinct` over k terms of 𝔽_p (or any set of terms forced
    // pairwise-distinct) requires k ≤ p: the field HAS p elements. For
    // ZK primes this is vacuous; for 𝔽₂/𝔽₃ omitting the check hands the
    // GB a pigeonhole refutation it must find through k·(k−1)/2 witness
    // generators of exponentially growing certificate degree — and the
    // design names the omission as a false-`sat` class in the
    // combination setting. Checked here, up front, for every field size.
    if let Some((index, k)) = distinct_set_exceeding_field(manager, field, assertions, &modulus) {
        return FfOutcome::Unsat(FfCore {
            fact_indices: vec![index],
            certificate: Some(FfCertificate::Cardinality {
                field,
                literal: index,
                k,
            }),
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
                // The linear core runs even on enumeration-eligible goals:
                // an inconsistent linear system is refuted in one pass
                // WITH a checkable certificate, where the exhaustive
                // search has none — certified mode would otherwise
                // decline every tiny-field UNSAT (the F_3..F_13 goals).
                // 𝔽₂ has no Montgomery form (even modulus) and skips
                // straight to the exhaustive path.
                if let Ok(f) = FieldCtx::new(modulus.clone()) {
                    match encode_generators(manager, field, &f, assertions, budget_steps) {
                        Ok((_enc, generators)) => match linear_core(&f, field, generators) {
                            FrontResult::Inconsistent(core, certificate) => {
                                return FfOutcome::Unsat(FfCore {
                                    fact_indices: core.into_iter().collect(),
                                    certificate,
                                });
                            }
                            FrontResult::Rewritten(_) => {}
                        },
                        Err(outcome) => return outcome,
                    }
                }
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

/// Step 1, shared by the decision procedure and certificate
/// verification: encode the assertions into generators. Deterministic
/// (fixed variable registration, fixed witness minting, bitsum
/// definitions appended last), so a replay from the same assertions
/// reproduces the same generator list — the property the UNSAT
/// certificate's verifier relies on.
fn encode_generators<'f>(
    manager: &TermManager,
    field: FieldId,
    f: &'f FieldCtx,
    assertions: &[TermId],
    budget_steps: u64,
) -> Result<(Encoder<'f>, Vec<FrontGen>), FfOutcome> {
    #[allow(clippy::let_and_return)]
    let mut enc = Encoder::new(f, field);
    let mut generators: Vec<FrontGen> = Vec::new();
    for (index, &assertion) in assertions.iter().enumerate() {
        let Some(term) = manager.get(assertion) else {
            return Err(FfOutcome::InvalidModel(format!(
                "dangling term {assertion:?}"
            )));
        };
        match &term.kind {
            TermKind::True => {}
            TermKind::False => {
                return Err(FfOutcome::Unsat(FfCore {
                    fact_indices: vec![index],
                    // `false` needs no field certificate: the Boolean
                    // skeleton refutes it, which the certified gate's
                    // LRAT kernel proves on its own.
                    certificate: None,
                }));
            }
            TermKind::Eq(a, b) => match enc.encode_pair(manager, *a, *b, budget_steps) {
                Some((pa, pb)) => generators.push(FrontGen {
                    literal: Some(index),
                    poly: pa.sub(f, &pb),
                    origin: std::iter::once(index).collect(),
                }),
                None => return Err(FfOutcome::OutOfBudget { where_: "encoding" }),
            },
            TermKind::Not(inner) => {
                let inner_term = manager.get(*inner);
                match inner_term.map(|t| &t.kind) {
                    Some(TermKind::Eq(a, b)) => {
                        match enc.encode_pair(manager, *a, *b, budget_steps) {
                            Some((pa, pb)) => {
                                let w = enc.fresh_witness(*a, *b);
                                let mut w_poly = MPoly::zero();
                                w_poly.add_term(f, Monomial::from_var(w), &f.one());
                                let one = MPoly::constant(f, &f.one());
                                generators.push(FrontGen {
                                    literal: Some(index),
                                    poly: pa.sub(f, &pb).mul(f, &w_poly).sub(f, &one),
                                    origin: std::iter::once(index).collect(),
                                });
                            }
                            None => {
                                return Err(FfOutcome::OutOfBudget { where_: "encoding" });
                            }
                        }
                    }
                    _ => {
                        return Err(FfOutcome::InvalidModel(
                            "unsupported literal shape under not".to_string(),
                        ));
                    }
                }
            }
            _ => {
                return Err(FfOutcome::InvalidModel(
                    "non-literal assertion reached the FF check".to_string(),
                ));
            }
        }
    }
    for (origin, poly) in std::mem::take(&mut enc.bitsum_generators) {
        generators.push(FrontGen {
            literal: None,
            poly,
            origin,
        });
    }
    Ok((enc, generators))
}

/// A two-way split Gröbner basis (Phase 7; cvc5 `split_gb.cpp`, the
/// [split-GB] paper's SplitGb): a LINEAR ideal and a NONLINEAR ideal,
/// exchanged under cvc5's `admit` discipline —
///
/// * the linear ideal accepts every linear consequence of either
///   basis (it stays linear under Buchberger: S-pairs of linear
///   polynomials are linear, so it can never re-inflate);
/// * the nonlinear ideal accepts only **linear binomials** (`x − c`,
///   `x − y`), so the dense linear content (definitions, RREF rows)
///   never enters the cascade — the exact re-expansion failure the two
///   flattening studies root-caused (a pivot row substituted into a
///   product rebuilds the expansion inside the S-pairs).
///
/// With the encoder's operand flattening, a circuit-shaped generator
/// `⟨a,z⟩·⟨b,z⟩ − c` reaches the nonlinear ideal as the binomial
/// `t·u − k` plus two linear definitions in the linear ideal — binomial
/// cleanliness AND decomposition, the property both studies converged
/// on.
///
/// Sound by construction: every polynomial exchanged is a member of the
/// ideal its basis generates, and every basis input is (inductively) a
/// member of the component's ideal, so `1` in either basis refutes the
/// component. Termination by Noetherianity (each round either strictly
/// grows one of the two ideals or the fixpoint stops); in practice the
/// shared budget bounds the work.
struct SplitBasis {
    /// The merged basis for FindZero (NOT itself inter-reduced — a
    /// union of two Gröbner bases; every element is in the component's
    /// ideal, which is all FindZero's branchers need).
    merged: GrobnerBasis,
}

/// Compute the split basis of one component's generators. `Err` on
/// budget exhaustion (the caller answers `Unknown`).
fn split_grobner_basis(
    f: &FieldCtx,
    component: &[&FrontGen],
    budget: &mut GrobnerBudget,
) -> Result<SplitBasis, GrobnerError> {
    let deg_of = |p: &MPoly| p.lm(DEGREVLEX).map_or(0, |m| m.total_degree());
    let mut l_inputs: Vec<MPoly> = Vec::new();
    let mut nl_inputs: Vec<MPoly> = Vec::new();
    for g in component {
        if deg_of(&g.poly) <= 1 {
            l_inputs.push(g.poly.clone());
        } else {
            nl_inputs.push(g.poly.clone());
        }
    }
    let mut l_basis: Option<GrobnerBasis> = None;
    let mut nl_basis: Option<GrobnerBasis> = None;
    // Polys pending insertion into each ideal (cvc5's newPolys): a
    // basis is recomputed only when its pending set is nonempty, from
    // its current elements plus the pending polys.
    let mut new_l: Vec<MPoly> = Vec::new();
    let mut new_nl: Vec<MPoly> = Vec::new();
    let mut round = 0u32;
    loop {
        round += 1;
        if round > 64 {
            // Noetherian in principle; bounded in practice. A long
            // exchange chain is a capacity limit, not an answer.
            return Err(GrobnerError::Budget);
        }
        if !new_l.is_empty() || (l_basis.is_none() && !l_inputs.is_empty()) {
            let mut gens: Vec<MPoly> = l_basis.as_ref().map_or_else(
                || l_inputs.clone(),
                |b| b.basis.iter().map(|t| t.poly.clone()).collect(),
            );
            gens.append(&mut new_l);
            l_basis = Some(grobner_basis(f, &gens, budget)?);
        }
        if !new_nl.is_empty() || (nl_basis.is_none() && !nl_inputs.is_empty()) {
            let mut gens: Vec<MPoly> = nl_basis.as_ref().map_or_else(
                || nl_inputs.clone(),
                |b| b.basis.iter().map(|t| t.poly.clone()).collect(),
            );
            gens.append(&mut new_nl);
            nl_basis = Some(grobner_basis(f, &gens, budget)?);
        }
        // The exchange: offer every basis element to every ideal that
        // admits it (cvc5's `admit`), skipping ideal membership. Only
        // linear polys are ever exchanged; the nonlinear ideal admits
        // only binomials.
        let mut member = |p: &MPoly, b: &Option<GrobnerBasis>| -> Option<bool> {
            b.as_ref()
                .map(|b| normal_form(f, p, b, budget).is_some_and(|nf| nf.is_zero()))
        };
        let mut offered_l: Vec<MPoly> = Vec::new();
        let mut offered_nl: Vec<MPoly> = Vec::new();
        for basis in [&l_basis, &nl_basis] {
            let Some(b) = basis else {
                continue;
            };
            for t in &b.basis {
                let p = &t.poly;
                if p.lm(DEGREVLEX).is_none_or(|m| m.total_degree() > 1) {
                    continue;
                }
                if member(p, &l_basis) != Some(true) {
                    offered_l.push(p.clone());
                }
                if p.n_terms() <= 2 && member(p, &nl_basis) != Some(true) {
                    offered_nl.push(p.clone());
                }
            }
        }
        if offered_l.is_empty() && offered_nl.is_empty() {
            break;
        }
        new_l = offered_l;
        new_nl = offered_nl;
    }
    let mut merged = GrobnerBasis {
        basis: Vec::new(),
        inputs: Vec::new(),
    };
    if let Some(b) = &l_basis {
        merged.basis.extend(b.basis.iter().cloned());
        merged.inputs.extend(b.inputs.iter().cloned());
    }
    if let Some(b) = &nl_basis {
        merged.basis.extend(b.basis.iter().cloned());
        merged.inputs.extend(b.inputs.iter().cloned());
    }
    if std::env::var_os("NIXIE_FF_STATS").is_some() {
        eprintln!(
            "[ff-stats] split: {} rounds, linear {}, nonlinear {}",
            round,
            l_basis.as_ref().map_or(0, |b| b.basis.len()),
            nl_basis.as_ref().map_or(0, |b| b.basis.len()),
        );
    }
    Ok(SplitBasis { merged })
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
    let (enc, generators) = match encode_generators(manager, field, f, assertions, budget_steps) {
        Ok(x) => x,
        Err(outcome) => return outcome,
    };
    if generators.is_empty() {
        let mut model = FfModel {
            values: FxHashMap::default(),
        };
        for var in enc.var_terms() {
            model.insert(var, BigUint::from(0u8));
        }
        return FfOutcome::Model(model);
    }

    // ---- Phase 5 front end, before any Gröbner work ----
    // The linear core: sparse Gaussian elimination over 𝔽_p on the
    // linear generators; pivots substitute into the nonlinear part; an
    // inconsistent row is an immediate UNSAT whose core is that row's
    // origin (the asserted literals it was combined from). Constant
    // propagation falls out: a pivot row with no other variables IS
    // `x − c`, and the substitution applies it everywhere at once. This
    // is the LRA tableau discipline with every hard part removed (no
    // bounds, no ordering, no anti-cycling rule) — the design's "do not
    // make Gröbner the front line".
    let generators = match linear_core(f, field, generators) {
        FrontResult::Inconsistent(core, certificate) => {
            return FfOutcome::Unsat(FfCore {
                fact_indices: core.into_iter().collect(),
                certificate,
            });
        }
        FrontResult::Rewritten(gens) => gens,
    };
    // ---- Step 2/3: connected components (§6.4), then per-component
    // Gröbner + FindZero ----
    // The variable-sharing graph's connected components are independent
    // subproblems: no polynomial mentions variables of two components,
    // so the ideal is a direct sum and a point of the whole is exactly a
    // point per component. The design calls this "the single most
    // reliable way to keep basis sizes sane" — a 20-constraint circuit
    // decomposing into 5 four-variable systems turns an intractable
    // Macaulay blowup into five trivial ones. Each component gets its
    // own budget (component counts are small; a shared cap would starve
    // late components).
    let components = connected_components(&generators);
    if std::env::var_os("NIXIE_FF_STATS").is_some() {
        eprintln!(
            "[ff-stats] field p>{}: {} generators after front end, {} components (sizes {:?}), budget 2^{}",
            f.modulus().bits(),
            generators.len(),
            components.len(),
            components.iter().map(|c| c.len()).collect::<Vec<_>>(),
            budget_steps.ilog2()
        );
    }
    // Per component: the MONOLITHIC basis first — the proven path,
    // exactly the pre-split behavior and budget semantics — and the
    // split basis as the FALLBACK for components whose monolithic
    // cascade is the blowup: separated linear/nonlinear ideals under
    // cvc5's admit discipline, then FindZero over the merged union.
    // UNSAT of any component refutes the whole; SAT needs a point of
    // every component. Each component gets its own budget (component
    // counts are small; a shared cap would starve late components).
    let mut combined = FfModel {
        values: FxHashMap::default(),
    };
    for component in &components {
        let input_polys: Vec<MPoly> = component.iter().map(|g| g.poly.clone()).collect();
        let mut gbudget = GrobnerBudget::new(budget_steps);
        let (basis, root_is_gb, is_split) = match grobner_basis(f, &input_polys, &mut gbudget) {
            Ok(basis) => (basis, true, false),
            Err(GrobnerError::Budget) => {
                // The fallback: the split (a fresh budget — the
                // monolithic attempt's burn is sunk cost, and the
                // separated ideals' work is disjoint from it).
                let mut split_budget = GrobnerBudget::new(budget_steps);
                match split_grobner_basis(f, component, &mut split_budget) {
                    Ok(split) => (split.merged, false, true),
                    Err(GrobnerError::Budget) => {
                        return FfOutcome::OutOfBudget {
                            where_: "Gröbner basis (component)",
                        };
                    }
                }
            }
        };
        if std::env::var_os("NIXIE_FF_STATS").is_some() {
            eprintln!(
                "[ff-stats] component: {} generators -> {} basis of {}{}",
                component.len(),
                if is_split {
                    "split-merged"
                } else {
                    "monolithic"
                },
                basis.basis.len(),
                gbudget_remaining(&gbudget)
                    .map_or_else(String::new, |r| format!(", GB steps left 2^{}", r.ilog2()))
            );
        }
        if basis.contains_nonzero_constant() {
            if !is_split {
                // The monolithic refutation: the tracer is aligned with
                // the component's generators — the traced core and the
                // replayable certificate, exactly as before.
                let owned: Vec<FrontGen> = component.iter().map(|g| (*g).clone()).collect();
                return traced_unsat(f, field, &owned, &basis);
            }
            // A split-path refutation: the derivation runs through both
            // ideals (or the exchanged polys detach the tracer from the
            // component's generators), so the core is the component's
            // origins and no certificate is claimed — certified mode
            // honestly downgrades.
            let core: Vec<usize> = component
                .iter()
                .flat_map(|g| g.origin.iter().copied())
                .collect();
            return FfOutcome::Unsat(FfCore {
                fact_indices: core,
                certificate: None,
            });
        }
        let vars = component_variables(component);
        let fz_outcome = find_zero(f, &basis, &enc, &vars, budget_steps, root_is_gb);
        match fz_outcome {
            FfOutcome::Model(model) => {
                for (var, value) in model.assignments() {
                    combined.insert(*var, value.clone());
                }
            }
            FfOutcome::Exhausted => {
                // This component has no point: the whole goal is
                // UNSAT, with this component's origins as the
                // core (no certificate — exhaustion).
                let core: Vec<usize> = component
                    .iter()
                    .flat_map(|g| g.origin.iter().copied())
                    .collect();
                return FfOutcome::Unsat(FfCore {
                    fact_indices: core,
                    certificate: None,
                });
            }
            other => return other,
        }
    }
    FfOutcome::Model(combined)
}

/// The remaining budget of a GrobnerBudget (for step-count reporting).
fn gbudget_remaining(b: &GrobnerBudget) -> Option<u64> {
    b.remaining()
}

/// Partition generators into the connected components of the
/// variable-sharing graph (union-find over variables; each generator
/// unions the variables its polynomial mentions). Deterministic:
/// components are emitted in the order of their smallest generator
/// index, generators within a component in index order.
fn connected_components(generators: &[FrontGen]) -> Vec<Vec<&FrontGen>> {
    // Union-find over Var.
    let mut parent: FxHashMap<Var, Var> = FxHashMap::default();
    let find = |mut v: Var, parent: &mut FxHashMap<Var, Var>| -> Var {
        loop {
            let next = *parent.entry(v).or_insert(v);
            if next == v {
                return v;
            }
            v = next;
        }
    };
    let union = |a: Var, b: Var, parent: &mut FxHashMap<Var, Var>| {
        let (ra, rb) = (find(a, parent), find(b, parent));
        if ra != rb {
            parent.insert(ra, rb);
        }
    };
    for g in generators {
        let vars: Vec<Var> = g
            .poly
            .terms_iter()
            .flat_map(|(m, _)| m.vars().iter().map(|vp| vp.var))
            .collect();
        if let Some(&first) = vars.first() {
            for &v in &vars[1..] {
                union(first, v, &mut parent);
            }
        }
    }
    // Group generators by their component root (any of the generator's
    // variables; a variable-less generator is its own singleton).
    let mut groups: Vec<(Var, Vec<usize>)> = Vec::new();
    let mut root_index: FxHashMap<Var, usize> = FxHashMap::default();
    for (i, g) in generators.iter().enumerate() {
        let root = g
            .poly
            .terms_iter()
            .find_map(|(m, _)| m.vars().first().map(|vp| find(vp.var, &mut parent)));
        let root = match root {
            Some(r) => r,
            None => {
                // Constant polynomial: its own singleton component (only
                // reachable for nonzero constants the front end kept).
                Var::from(u32::MAX - (i as u32))
            }
        };
        let next = root_index.len();
        let slot = *root_index.entry(root).or_insert(next);
        if slot == groups.len() {
            groups.push((root, Vec::new()));
        }
        groups[slot].1.push(i);
    }
    // Deterministic order: by smallest generator index in the component.
    let mut ordered: Vec<(Var, Vec<usize>)> = groups.into_iter().collect();
    for (_, idxs) in ordered.iter_mut() {
        idxs.sort_unstable();
    }
    ordered.sort_by_key(|(_, idxs)| idxs[0]);
    ordered
        .into_iter()
        .map(|(_, idxs)| idxs.iter().map(|&i| &generators[i]).collect())
        .collect()
}

/// The variables a component's generators mention, sorted.
fn component_variables(component: &[&FrontGen]) -> Vec<Var> {
    let mut vars: Vec<Var> = Vec::new();
    for g in component {
        for (m, _) in g.poly.terms_iter() {
            for vp in m.vars() {
                if !vars.contains(&vp.var) {
                    vars.push(vp.var);
                }
            }
        }
    }
    vars.sort_unstable();
    vars
}

/// One generator with its provenance: the asserted literal it came from
/// (if any) and, after the front end, the union of literals any
/// combination touched. The origin set is what UNSAT cores are cut from.
#[derive(Debug, Clone)]
struct FrontGen {
    /// The asserted literal this generator encodes (`None` for bitsum
    /// definitions — a definition is not a fact and cores exclude it).
    literal: Option<usize>,
    /// The polynomial.
    poly: MPoly,
    /// The literal indices this generator derives from.
    origin: std::collections::BTreeSet<usize>,
}

/// Extract the traced core from a `1 ∈ I` basis: the asserted literals
/// whose generators carry nonzero cofactor in the certificate (origin
/// sets composed through the front end).
fn traced_unsat(
    f: &FieldCtx,
    field: FieldId,
    generators: &[FrontGen],
    basis: &nixie_math::ff::grobner::GrobnerBasis,
) -> FfOutcome {
    let Some(witness) = basis.constant_witness() else {
        return FfOutcome::OutOfBudget {
            where_: "Gröbner basis",
        };
    };
    // §8's "easy half", checked EVERY time, not only in certified mode:
    // re-multiply Σ cᵢ·fᵢ and compare with the constant — one pass of
    // polynomial arithmetic, orders of magnitude cheaper than the basis
    // that produced it, and the difference between "the GB says so" and
    // "here is a checkable object". A tracer or arithmetic defect that
    // breaks the identity surfaces as Unknown, never as an unjustified
    // Unsat. (The basis's `inputs` are the front-end-rewritten
    // generators, index-aligned with `witness.cofactors`; `f` is the
    // field the whole check ran over.)
    if !witness.verify(f, &basis.inputs) {
        return FfOutcome::InvalidModel(
            "UNSAT certificate failed verification (cofactor identity \
             broken) — declining to an honest Unknown"
                .to_string(),
        );
    }
    let mut core: std::collections::BTreeSet<usize> = std::collections::BTreeSet::new();
    for (gen_idx, generator) in generators.iter().enumerate() {
        if witness.cofactors.get(gen_idx).is_some_and(|c| !c.is_zero()) {
            core.extend(generator.origin.iter().copied());
        }
    }
    if core.is_empty() {
        // The certificate rests only on definitions — not reachable with
        // a sound encoder, but an empty core must never be returned as
        // "UNSAT by nothing": fall back to naming every fact.
        core = generators
            .iter()
            .flat_map(|g| g.origin.iter().copied())
            .collect();
    }
    // The certificate: the FULL generator list (facts, witnesses, bitsum
    // definitions — index-aligned with the cofactors) plus the cofactors.
    // Verification replays `encode_generators` over the same assertions,
    // which deterministically reproduces the list, and re-multiplies —
    // so the certificate is exactly the cofactors, and everything else
    // is re-derived by the checker.
    let mut cert_generators: Vec<(Option<usize>, MPoly)> = Vec::new();
    let mut cert_cofactors: Vec<MPoly> = Vec::new();
    for (gen_idx, generator) in generators.iter().enumerate() {
        cert_generators.push((generator.literal, generator.poly.clone()));
        cert_cofactors.push(
            witness
                .cofactors
                .get(gen_idx)
                .cloned()
                .unwrap_or_else(MPoly::zero),
        );
    }
    let certificate = Some(FfCertificate::IdealMembership {
        field,
        generators: cert_generators,
        cofactors: cert_cofactors,
    });
    FfOutcome::Unsat(FfCore {
        fact_indices: core.into_iter().collect(),
        certificate,
    })
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
    /// Bitsum definition generators accumulated during encoding, each
    /// with the literal whose encoding minted it — provenance for cores
    /// (a definition is not a fact, but the fact that REQUIRED it
    /// belongs in any core the definition participates in).
    bitsum_generators: Vec<(std::collections::BTreeSet<usize>, MPoly)>,
    /// The literal whose terms are currently being encoded.
    current_literal: Option<usize>,
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
            current_literal: None,
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
            // A `QF_UFFF` application with an FF result sort of THIS field
            // is an opaque variable (see the module doc): mint it, and do
            // NOT descend into the arguments — they may belong to other
            // fields whose slices own them, and nothing this field's
            // polynomials can say about them is sound.
            if let TermKind::Apply { .. } = &term.kind
                && self.is_field_sort(manager, term.sort)
                && !self.var_index.contains_key(&t)
            {
                self.var_index.insert(t, self.next_var);
                self.next_var += 1;
            }
            if let TermKind::Apply { .. } = &term.kind {
                continue;
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

    /// Pass 2: the polynomial of a term. ONE frame stack: `Expand` frames
    /// push `Combine` frames *under* their children, so a combine pops
    /// exactly when its own children have all produced values — a
    /// separate combine list would let sibling operands bleed across
    /// windows (the first version's Add consumed the neighbour's operands
    /// and fabricated `x₀x₁x₂` monomials out of linear sums; the planted
    /// fuzzer caught it as a false UNSAT).
    fn encode(&mut self, manager: &TermManager, root: TermId, budget: u64) -> Option<MPoly> {
        enum Combine {
            Add(usize),
            Mul(usize),
            Neg,
            /// The bitsum's definition generator is emitted and the fresh
            /// sum variable is the value.
            Bitsum(usize),
        }
        enum Frame {
            Expand(TermId),
            Combine(Combine),
        }
        let mut results: Vec<MPoly> = Vec::new();
        let mut stack: Vec<Frame> = vec![Frame::Expand(root)];
        let mut steps = 0u64;

        while let Some(frame) = stack.pop() {
            steps += 1;
            if steps > budget {
                return None;
            }
            match frame {
                Frame::Expand(t) => {
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
                        TermKind::Apply { .. } => {
                            // A `QF_UFFF` opaque application (registered in
                            // pass 1 when its result sort is this field).
                            // Atomic: the arguments are never encoded here.
                            let var = self.var_index.get(&t).copied()?;
                            let mut p = MPoly::zero();
                            p.add_term(self.f, Monomial::from_var(var), &self.f.one());
                            results.push(p);
                        }
                        TermKind::FfAdd(children) => {
                            stack.push(Frame::Combine(Combine::Add(children.len())));
                            for &c in children.iter().rev() {
                                stack.push(Frame::Expand(c));
                            }
                        }
                        TermKind::FfMul(children) => {
                            stack.push(Frame::Combine(Combine::Mul(children.len())));
                            for &c in children.iter().rev() {
                                stack.push(Frame::Expand(c));
                            }
                        }
                        TermKind::FfNeg(child) => {
                            stack.push(Frame::Combine(Combine::Neg));
                            stack.push(Frame::Expand(*child));
                        }
                        TermKind::FfBitsum(children) => {
                            stack.push(Frame::Combine(Combine::Bitsum(children.len())));
                            for &c in children.iter().rev() {
                                stack.push(Frame::Expand(c));
                            }
                        }
                        _ => return None, // unsupported shape — refused
                    }
                }
                Frame::Combine(kind) => {
                    match kind {
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
                        Combine::Bitsum(n) => {
                            if results.len() < n {
                                return None;
                            }
                            // The children were pushed in reverse, so the
                            // last n results are b₀ … bₙ₋₁ in order.
                            let drained: Vec<MPoly> = results.split_off(results.len() - n);
                            let s = {
                                let v = self.next_var;
                                self.next_var += 1;
                                v
                            };
                            // Definition: s − Σ 2ⁱ bᵢ, into the separate
                            // generator set (a definition, not a fact).
                            let mut definition = MPoly::zero();
                            definition.add_term(self.f, Monomial::from_var(s), &self.f.one());
                            let mut power = self.f.one();
                            for p in drained {
                                definition = definition.sub(self.f, &p.scale(self.f, &power));
                                power = self
                                    .f
                                    .mul(&power, &self.f.from_biguint(&BigUint::from(2u8)));
                            }
                            self.bitsum_generators.push((
                                self.current_literal
                                    .into_iter()
                                    .collect::<std::collections::BTreeSet<usize>>(),
                                definition,
                            ));
                            let mut out = MPoly::zero();
                            out.add_term(self.f, Monomial::from_var(s), &self.f.one());
                            results.push(out);
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

// ================= Step 3: FindZero =================

/// The branching search for a rational point: one explicit heap stack of
/// nodes (basis + partial assignment), never native recursion.
fn find_zero(
    f: &FieldCtx,
    basis: &nixie_math::ff::grobner::GrobnerBasis,
    enc: &Encoder<'_>,
    variables: &[Var],
    budget_steps: u64,
    root_is_gb: bool,
) -> FfOutcome {
    struct Node {
        basis: nixie_math::ff::grobner::GrobnerBasis,
        /// Whether `basis` is an inter-reduced Gröbner basis of
        /// `inputs`' ideal. The split path's root is a UNION of two
        /// Gröbner bases — sound for every rule that only consumes
        /// ideal members (univariate branching, linear univariates,
        /// whole-ring detection), but NOT for the minimal-polynomial
        /// rule, whose quotient-basis arithmetic is valid only for a
        /// true basis.
        is_gb: bool,
    }

    let mut stack: Vec<Node> = vec![Node {
        basis: basis.clone(),
        is_gb: root_is_gb,
    }];
    // Whether any round-robin enumerated fewer than p values: an
    // exhausted stack over truncated branches is an OutOfBudget, never
    // an Exhausted.
    let mut truncated_any = false;
    let mut steps = 0u64;
    // ONE budget across the whole search: a fresh per-node budget made
    // the total work unbounded (a deep tree of cheap nodes never hit the
    // cap and ground instead of answering). Shared, a blowup becomes an
    // honest OutOfBudget.
    let mut gbudget = GrobnerBudget::new(budget_steps);
    let mut rbudget = RootBudget::new(budget_steps);
    let variables: Vec<Var> = variables.to_vec();

    while let Some(node) = stack.pop() {
        steps += 1;
        if steps > budget_steps {
            return FfOutcome::OutOfBudget {
                where_: "FindZero search",
            };
        }
        if std::env::var_os("NIXIE_FF_STATS").is_some() && steps % 10 == 1 {
            eprintln!(
                "[fz] node {steps}: stack {} basis {} gbudget 2^{}",
                stack.len(),
                node.basis.basis.len(),
                gbudget_remaining(&gbudget).map_or(0, |r| r.ilog2())
            );
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
        // SELECTION: among all candidates, take the one of SMALLEST
        // degree — the branching factor is the root count, so the
        // min-degree choice is the smallest tree. First-found order once
        // produced a degree-8 brancher where a degree-2 sat beside it,
        // and a 16-constraint sparse goal ground for minutes on the
        // 8-way tree (a 64-constraint goal with no such element solved
        // in seconds — the chaos is the selection, not the size).
        let mut candidates: Vec<(usize, Var, UniPoly)> = Vec::new();
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
            candidates.push((deg, x, UniPoly::from_coeffs(coeffs)));
        }
        // Deterministic order: degree, then variable index.
        candidates.sort_by_key(|(deg, x, _)| (*deg, *x));

        // The min-degree candidate decides: root finding either yields
        // its roots or exhausts the budget (there is no "no roots"
        // outcome for a squarefree product the basis admits), so the
        // first candidate is also the last one consulted.
        let brancher = match candidates.first() {
            Some(&(_, x, ref uni)) => match uni_roots(f, uni, &mut rbudget) {
                Err(RootError::Budget) | Ok(None) => {
                    return FfOutcome::OutOfBudget {
                        where_: "root finding",
                    };
                }
                Ok(Some(roots)) => Some((x, roots)),
            },
            None => None,
        };

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
            if node.is_gb && node.basis.is_zero_dimensional(&variables) {
                match minimal_polynomial(f, &node.basis, free_var, &variables, &mut gbudget) {
                    Some(minpoly) => {
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
                // Positive-dimensional: enumerate the free variable's
                // residues LAZILY, in value order 0, 1, 2, …, up to a
                // small horizon. Complete for p ≤ horizon; beyond it,
                // a truncated enumeration is recorded and the exhausted
                // stack reports OutOfBudget, never Exhausted — the
                // honest form of "this will not finish at a big prime".
                // Structured systems tolerate the horizon well: a wrong
                // guess on a product chain dies in one node (the branch
                // literal contradicts or pins the propagation), so the
                // effective branch factor is tiny even though the
                // theoretical one is p.
                const RR_HORIZON: u64 = 256;
                let p = f.modulus();
                let cap: u64 = p.try_into().unwrap_or(u64::MAX);
                let horizon = RR_HORIZON.min(cap);
                let truncated = horizon < cap;
                let vals: Vec<Limbs> = (0..horizon)
                    .map(|v| f.from_biguint(&BigUint::from(v)))
                    .collect();
                if truncated {
                    truncated_any = true;
                }
                (free_var, vals)
            }
        };

        // Branch: add x − value, recompute the basis (recompute, never
        // incrementally roll back — the design's scoping discipline).
        // The child's generators are the node's BASIS ELEMENTS plus the
        // branch literal — the same ideal as the raw inputs (a basis
        // generates its ideal; the split root's union generates the
        // component ideal), but already reduced, so each branch
        // bootstraps from the reduced basis instead of re-running the
        // original cascade.
        let elements: Vec<MPoly> = node.basis.basis.iter().map(|t| t.poly.clone()).collect();
        for value in values {
            let mut poly = MPoly::zero();
            poly.add_term(f, Monomial::from_var(var), &f.one());
            let mut const_poly = MPoly::zero();
            const_poly.add_term(f, Monomial::unit(), &value.clone());
            let new_gen = poly.sub(f, &const_poly);
            let mut inputs = elements.clone();
            inputs.push(new_gen);
            match grobner_basis(f, &inputs, &mut gbudget) {
                Err(GrobnerError::Budget) => {
                    return FfOutcome::OutOfBudget {
                        where_: "Gröbner basis",
                    };
                }
                Ok(child) => stack.push(Node {
                    basis: child,
                    is_gb: true,
                }),
            }
        }
    }
    // The stack emptied without a model: the branching was exhaustive —
    // UNSAT is genuine (Step 4's honesty gate: this is *not* a budget
    // outcome) — UNLESS a round-robin branch enumerated fewer than p
    // values: then unexplored assignments remain, the empty stack proves
    // nothing, and the verdict is Unknown. (The first version of the
    // lazy round-robin dropped exactly this gate — a planted BN254 goal
    // whose satisfying values all exceeded the horizon came back
    // `unsat`; the planted corpus caught it, the tiny-prime oracle
    // could not, because p ≤ 256 never truncates there.)
    if truncated_any {
        return FfOutcome::OutOfBudget {
            where_: "positive-dimensional enumeration",
        };
    }
    FfOutcome::Exhausted
}

// ================= Enumeration path (tiny fields) =================

/// The first `distinct` literal whose term count exceeds the field's
/// order: (literal index, term count). Pigeonhole makes it unsatisfiable
/// on its own, so it is its own core.
fn distinct_set_exceeding_field(
    manager: &TermManager,
    field: FieldId,
    assertions: &[TermId],
    modulus: &BigUint,
) -> Option<(usize, usize)> {
    for (index, &assertion) in assertions.iter().enumerate() {
        let term = manager.get(assertion)?;
        let TermKind::Distinct(args) = &term.kind else {
            continue;
        };
        // All arguments must live in THIS field (a mixed-field distinct
        // is a type error the parser rejects; guard anyway).
        let all_here = args.iter().all(|&a| {
            manager
                .get(a)
                .and_then(|t| manager.sorts.get(t.sort).map(|s| s.kind.clone()))
                .is_some_and(|k| matches!(k, SortKind::FiniteField(id) if id == field))
        });
        if all_here && BigUint::from(args.len()) > *modulus {
            return Some((index, args.len()));
        }
    }
    None
}

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
            // A `QF_UFFF` application whose result sort is this field is an
            // opaque variable the enumerator must assign (see the module
            // doc). Arguments are not walked: same-field subterms reach
            // `vars` through the literals that mention them directly, and
            // foreign-field arguments belong to other slices — walking
            // them here would both over-collect and mis-route.
            TermKind::Apply { .. } => {
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
    // Mixed-radix enumeration over p^n points. The caller's cap
    // (p^n ≤ 2^22, checked in [`check_conjunction`]) guarantees the
    // point count fits u64, and any modulus with n ≥ 1 under that cap
    // is far below 2^64 — so the counter and its digits run in u64
    // (the first version did BigUint div/mod per digit per point, which
    // made a 2^15-point enumeration cost ~a second; the combination
    // loop runs thousands of those).
    let n = vars.len();
    let total: BigUint = num_traits::Pow::pow(modulus.clone(), n);
    let total_u64: Option<u64> = (&total).try_into().ok();
    let Some(total_u64) = total_u64.filter(|&t| t <= (1 << 22)) else {
        return FfOutcome::OutOfBudget {
            where_: "enumeration space",
        };
    };
    // Out of budget up front: enumerating `budget` points only to
    // abandon the search at the same verdict is pure waste.
    if total_u64 > budget {
        return FfOutcome::OutOfBudget {
            where_: "enumeration space",
        };
    }
    let modulus_u64: u64 = modulus.try_into().unwrap_or(u64::MAX);

    let mut assignment: FxHashMap<TermId, BigUint> = FxHashMap::default();
    for counter in 0..total_u64 {
        // Decode the counter into digits base p.
        let mut rest = counter;
        for var in vars {
            let digit = rest % modulus_u64;
            rest /= modulus_u64;
            assignment.insert(*var, BigUint::from(digit));
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

/// Exact FF-term evaluation in `BigUint` arithmetic mod `p`. ONE frame
/// stack (Expand/Combine interleaved) — a separate combine list lets
/// sibling operands bleed across windows, which mis-evaluated nested
/// `(ff.mul (ff.add …) (ff.add …))` shapes and made the validator reject
/// correct witnesses (caught by the planted-solution fuzzer).
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
    enum Frame {
        Expand(TermId),
        Combine(Combine),
    }
    let mut results: Vec<BigUint> = Vec::new();
    let mut stack: Vec<Frame> = vec![Frame::Expand(root)];
    while let Some(frame) = stack.pop() {
        match frame {
            Frame::Expand(t) => {
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
                    // `QF_UFFF` opaque application: its value is whatever the
                    // assignment gives the term (the combination layer
                    // guarantees those values satisfy congruence; this fold
                    // deliberately knows nothing about it). Atomic — the
                    // arguments are not evaluated here.
                    TermKind::Apply { .. } => {
                        results.push(assignment.get(&t).cloned()?);
                    }
                    TermKind::FfAdd(children) => {
                        stack.push(Frame::Combine(Combine::Add(children.len())));
                        for &c in children.iter().rev() {
                            stack.push(Frame::Expand(c));
                        }
                    }
                    TermKind::FfMul(children) => {
                        stack.push(Frame::Combine(Combine::Mul(children.len())));
                        for &c in children.iter().rev() {
                            stack.push(Frame::Expand(c));
                        }
                    }
                    TermKind::FfNeg(child) => {
                        stack.push(Frame::Combine(Combine::Neg));
                        stack.push(Frame::Expand(*child));
                    }
                    TermKind::FfBitsum(children) => {
                        stack.push(Frame::Combine(Combine::Bitsum(children.len())));
                        for &c in children.iter().rev() {
                            stack.push(Frame::Expand(c));
                        }
                    }
                    _ => return None,
                }
            }
            Frame::Combine(kind) => match kind {
                Combine::Add(n) => {
                    if results.len() < n {
                        return None;
                    }
                    let mut sum = BigUint::zero();
                    for _ in 0..n {
                        sum = (sum + results.pop()?) % modulus;
                    }
                    results.push(sum);
                }
                Combine::Mul(n) => {
                    if results.len() < n {
                        return None;
                    }
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
                    if results.len() < n {
                        return None;
                    }
                    let drained = results.split_off(results.len() - n);
                    let mut acc = BigUint::zero();
                    let mut power = BigUint::one();
                    for v in drained {
                        acc = (acc + &power * v) % modulus;
                        power = (&power << 1) % modulus;
                    }
                    results.push(acc);
                }
            },
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

/// Exact evaluation of an FF term of `field` under a term→residue map —
/// the public face of the [`validate_model`] fold, for callers outside
/// this crate (the `QF_UFFF` combination layer's function-hood scan:
/// given candidate values for the opaque applications and variables, a
/// congruence check needs the *argument* values, and arguments are
/// arbitrary FF terms). Returns `None` on an unassigned leaf, a foreign
/// constant, or a non-FF shape — never a guess.
#[must_use]
pub fn evaluate_term_exact(
    manager: &TermManager,
    field: FieldId,
    root: TermId,
    assignment: &FxHashMap<TermId, BigUint>,
) -> Option<BigUint> {
    let modulus = manager.sorts.field_table().modulus(field)?.clone();
    eval_term(manager, field, &modulus, root, assignment)
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

// ================= Phase 5: the field-aware front end =================

/// The linear core's verdict.
enum FrontResult {
    /// The generator list, rewritten: pivots eliminated, linear rows in
    /// reduced form, origins merged. Every asserted constraint survives
    /// (a `0 = 0` row is the only thing dropped).
    Rewritten(Vec<FrontGen>),
    /// An inconsistent linear row; the payloads are the literal indices
    /// of its origin and (when tracked) the ideal-membership certificate
    /// — the row's own combination IS one: `Σ combo_i · gᵢ = c ≠ 0`.
    Inconsistent(std::collections::BTreeSet<usize>, Option<FfCertificate>),
}

/// Constant propagation + sparse Gaussian elimination over the linear
/// generators, substitution into the nonlinear remainder.
///
/// Sound by construction: every step is an ideal-preserving operation
/// (swap, scale, combine, substitute) over 𝔽_p rows that carry their
/// literal provenance, so an inconsistent row is a certified `1 ∈
/// ⟨support⟩` traceable to asserted facts.
fn linear_core(f: &FieldCtx, field: FieldId, gens: Vec<FrontGen>) -> FrontResult {
    use nixie_math::polynomial::Var;
    use std::collections::BTreeMap;
    // Snapshot for certificate construction: (literal, poly) per
    // generator, in the encoder's order (the combo vectors index this).
    let snapshot: Vec<(Option<usize>, MPoly)> =
        gens.iter().map(|g| (g.literal, g.poly.clone())).collect();

    // Partition into linear rows and nonlinear generators.
    struct Row {
        coeffs: BTreeMap<Var, Limbs>,
        constant: Limbs,
        origin: std::collections::BTreeSet<usize>,
        literal: Option<usize>,
        /// The row's combination over the ORIGINAL linear generators
        /// (dense over the linear prefix, in partition order): the row
        /// polynomial = Σ combo[i] · linear_gens[i]. Maintained through
        /// every row operation, this is the linear-core half of the UNSAT
        /// certificate.
        combo: Vec<Limbs>,
    }
    let mut rows: Vec<Row> = Vec::new();
    let mut nonlinear: Vec<FrontGen> = Vec::new();
    // The linear generators, in partition order (the certificate's
    // combination indexes these).
    let mut linear_gens: Vec<FrontGen> = Vec::new();
    let n_combo = gens.len();
    for g in gens {
        let linear = g.poly.terms_iter().all(|(m, _)| m.total_degree() <= 1);
        if !linear {
            nonlinear.push(g);
            continue;
        }
        let FrontGen {
            literal,
            poly,
            origin,
        } = g;
        let mut coeffs: BTreeMap<Var, Limbs> = BTreeMap::new();
        let mut constant = f.zero();
        for (m, c) in poly.terms_iter() {
            if m.is_unit() {
                constant = c.clone();
            } else {
                coeffs.insert(m.vars()[0].var, c.clone());
            }
        }
        let mut combo = vec![f.zero(); n_combo];
        combo[linear_gens.len()] = f.one();
        linear_gens.push(FrontGen {
            literal,
            poly,
            origin: origin.clone(),
        });
        rows.push(Row {
            coeffs,
            constant,
            origin,
            literal,
            combo,
        });
    }

    // Reduced row-echelon: repeatedly pick the row whose smallest
    // uneliminated variable is smallest (deterministic), normalize it,
    // eliminate that variable from every other row. Terminates in ≤
    // n_vars rounds (each round removes a variable from all rows).
    let mut pivots: Vec<(Var, usize)> = Vec::new(); // (var, row index)
    loop {
        let mut chosen: Option<(usize, Var)> = None;
        for (ri, row) in rows.iter().enumerate() {
            let Some(&smallest) = row.coeffs.keys().next() else {
                continue;
            };
            if pivots.iter().any(|(v, _)| *v == smallest) {
                continue;
            }
            match chosen {
                Some((_, v)) if v <= smallest => {}
                _ => chosen = Some((ri, smallest)),
            }
        }
        let Some((ri, pivot_var)) = chosen else {
            break;
        };
        // Normalize the pivot row (leading coefficient 1).
        let lc = rows[ri].coeffs[&pivot_var].clone();
        let Some(inv) = f.inv(&lc) else {
            break; // unreachable: keys hold nonzero coefficients
        };
        {
            let row = &mut rows[ri];
            for c in row.coeffs.values_mut() {
                *c = f.mul(c, &inv);
            }
            row.constant = f.mul(&row.constant, &inv);
            for c in row.combo.iter_mut() {
                *c = f.mul(c, &inv);
            }
        }
        // Eliminate from every other row, merging provenance.
        for rj in 0..rows.len() {
            if rj == ri {
                continue;
            }
            let Some(factor) = rows[rj].coeffs.get(&pivot_var).cloned() else {
                continue;
            };
            let (pc, pk, po, pcombo) = {
                let r = &rows[ri];
                (
                    r.coeffs.clone(),
                    r.constant.clone(),
                    r.origin.clone(),
                    r.combo.clone(),
                )
            };
            let row = &mut rows[rj];
            for (v, c) in &pc {
                let sub = f.mul(c, &factor);
                let entry = row.coeffs.entry(*v).or_insert_with(|| f.zero());
                *entry = f.sub(entry, &sub);
                if f.is_zero(entry) {
                    row.coeffs.remove(v);
                }
            }
            row.constant = f.sub(&row.constant, &f.mul(&pk, &factor));
            for (i, c) in pcombo.iter().enumerate() {
                let sub = f.mul(c, &factor);
                row.combo[i] = f.sub(&row.combo[i], &sub);
            }
            row.origin.extend(po.iter().copied());
        }
        pivots.push((pivot_var, ri));
    }

    // Inconsistent row: no variables, nonzero constant → immediate
    // UNSAT, certified by the row's own combination (rescaled to monic —
    // the identity Σ comboᵢ·gᵢ = 1 holds exactly for the normalized row,
    // since normalization divided the whole row, combination included,
    // by the leading coefficient... which for a variable-less row IS the
    // constant; verify() re-multiplies and only demands a nonzero
    // constant, so no rescale bookkeeping is needed here).
    for row in &rows {
        if row.coeffs.is_empty() && !f.is_zero(&row.constant) {
            // Convert the combination's field elements into constant
            // polynomials (the certificate's cofactor format).
            let cofactors: Vec<MPoly> = row.combo.iter().map(|c| MPoly::constant(f, c)).collect();
            let certificate = Some(FfCertificate::IdealMembership {
                field,
                generators: snapshot,
                cofactors,
            });
            return FrontResult::Inconsistent(row.origin.clone(), certificate);
        }
    }

    // Substitute each pivot into the nonlinear generators. The pivot row
    // reads `x + Σ c_v·v + c₀ = 0`, i.e. `x = −c₀ − Σ c_v·v`.
    let mut result: Vec<FrontGen> = Vec::new();
    for (pivot_var, ri) in &pivots {
        let row = &rows[*ri];
        let mut repl = MPoly::constant(f, &f.neg(&row.constant));
        for (v, c) in &row.coeffs {
            if v == pivot_var {
                continue;
            }
            let mut term = MPoly::zero();
            term.add_term(f, Monomial::from_var(*v), c);
            repl = repl.sub(f, &term);
        }
        let mut next: Vec<FrontGen> = Vec::with_capacity(nonlinear.len());
        for g in nonlinear {
            let poly = substitute_var(f, &g.poly, *pivot_var, &repl);
            next.push(FrontGen {
                literal: g.literal,
                poly,
                origin: {
                    let mut o = g.origin.clone();
                    o.extend(row.origin.iter().copied());
                    o
                },
            });
        }
        nonlinear = next;
    }
    result.extend(nonlinear);
    // The pivot rows themselves survive as generators (they carry the
    // linear constraints; FindZero's linear-univariate detection reads
    // them). Dependent rows reduced to 0 = 0 are dropped — no
    // information lost.
    for (pivot_var, ri) in &pivots {
        let row = &rows[*ri];
        let mut poly = MPoly::zero();
        poly.add_term(f, Monomial::from_var(*pivot_var), &f.one());
        for (v, c) in &row.coeffs {
            if v == pivot_var {
                continue;
            }
            poly.add_term(f, Monomial::from_var(*v), c);
        }
        poly.add_term(f, Monomial::unit(), &row.constant);
        result.push(FrontGen {
            literal: row.literal,
            poly,
            origin: row.origin.clone(),
        });
    }
    FrontResult::Rewritten(result)
}

/// Substitute `var := repl` in a polynomial (ideal-preserving when the
/// substitution comes from an ideal member defining var).
fn substitute_var(
    f: &FieldCtx,
    p: &MPoly,
    var: nixie_math::polynomial::Var,
    repl: &MPoly,
) -> MPoly {
    let mut out = MPoly::zero();
    for (m, c) in p.terms_iter() {
        let deg = m.degree(var);
        if deg == 0 {
            out.add_term(f, m.clone(), c);
        } else {
            let mut rest = Monomial::unit();
            for vp in m.vars() {
                if vp.var != var {
                    rest = rest.mul(&Monomial::from_var_power(vp.var, vp.power));
                }
            }
            let mut factor = repl.clone();
            for _ in 1..deg {
                factor = factor.mul(f, repl);
            }
            let term = mul_by_monomial_pub(f, &factor.scale(f, c), &rest);
            out = out.add(f, &term);
        }
    }
    out
}

/// Monomial multiply helper (mirrors the private one in grobner.rs).
fn mul_by_monomial_pub(f: &FieldCtx, p: &MPoly, m: &Monomial) -> MPoly {
    let mut out = MPoly::zero();
    for (mm, c) in p.terms_iter() {
        out.add_term(f, mm.mul(m), c);
    }
    out
}
