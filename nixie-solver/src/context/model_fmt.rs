//! Model and function-interpretation output formatting for [`Context`].
//!
//! These methods turn the solver's model, term values, and sorts into
//! SMT-LIB2 display strings for `(get-model)` / `(get-value ...)` and the Z3
//! function-interpretation extensions.  They live in a child module so the
//! (already large) `context` module stays under the 2000-line policy limit;
//! being a child of `context`, they retain full access to `Context`'s private
//! fields.

#[allow(unused_imports)]
use crate::prelude::*;
use crate::solver::SolverResult;
use nixie_core::ast::{TermId, TermKind};
use nixie_core::sort::{SortId, SortKind};
use nixie_theories::nl_witness::{AlgebraicValue, NlWitnessValue};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use super::{Context, RawFuncInterp};
mod array_model;
mod candidate_model;
mod certified_numeric;
mod class_values;
mod completed_candidate;
mod datatype_completion;
mod finite_uninterpreted;
mod get_value;
mod mint;
mod printed_check;
mod printed_eval;
mod projected_functions;
mod published;
mod underspecified;
pub(super) use published::PublishedModel;

/// Render a nonlinear-real exact value as SMT-LIB2 text.
///
/// Rational values print exactly as the ordinary `RealConst` arm of
/// [`Context::format_value`] prints them, so the two channels agree
/// character-for-character on a value both could carry. Algebraic values print
/// as `root-obj`; see [`render_root_obj`].
fn render_nl_witness_value(value: &NlWitnessValue) -> String {
    match value {
        NlWitnessValue::Rational(rational) => {
            if rational.denom().is_one() {
                format!("{}.0", rational.numer())
            } else {
                format!("(/ {} {})", rational.numer(), rational.denom())
            }
        }
        NlWitnessValue::Algebraic(algebraic) => render_root_obj(algebraic),
    }
}

/// Render an exact algebraic number as SMT-LIB2 `root-obj` notation.
///
/// # The spelling is Z3's, verified against it
///
/// Every rule below was read off `z3 4.15.4` rather than inferred, by running
/// the corresponding goal and capturing `(get-value (x))`:
///
/// | goal | Z3 answer |
/// |---|---|
/// | `x² = 2` | `(root-obj (+ (^ x 2) (- 2)) 1)` |
/// | `x² = 2 ∧ x > 0` | `(root-obj (+ (^ x 2) (- 2)) 2)` |
/// | `2x² = 3` | `(root-obj (+ (* 2 (^ x 2)) (- 3)) 1)` |
/// | `x² + x = 1 ∧ x > 0` | `(root-obj (+ (^ x 2) x (- 1)) 2)` |
/// | `x² − 2x = 1 ∧ x > 0` | `(root-obj (+ (^ x 2) (* (- 2) x) (- 1)) 2)` |
/// | `x⁵ − 3x = 1` | `(root-obj (+ (^ x 5) (* (- 3) x) (- 1)) 1)` |
///
/// So: monomials in **descending** degree, zero coefficients omitted; degree
/// `k ≥ 2` spells `(^ x k)`, degree 1 spells bare `x`, degree 0 spells the
/// bare integer; a coefficient of exactly `1` is elided rather than written as
/// `(* 1 ..)`; a negative integer anywhere spells `(- n)`, since SMT-LIB has no
/// negative numerals.
///
/// The bound variable is **always** printed `x`, whatever the SMT constant is
/// called — confirmed by asking Z3 for a model of `yy² = 2`, which answers
/// `(root-obj (+ (^ x 2) (- 2)) 1)` for `yy`. `root-obj`'s first argument is a
/// closed polynomial term with its own binder, not an expression over the
/// model's constants.
fn render_root_obj(value: &AlgebraicValue) -> String {
    let mut monomials: Vec<String> = Vec::new();
    for (degree, coefficient) in value.coefficients.iter().enumerate().rev() {
        if coefficient.is_zero() {
            continue;
        }
        let power = match degree {
            0 => None,
            1 => Some("x".to_string()),
            k => Some(format!("(^ x {k})")),
        };
        monomials.push(match (power, coefficient.is_one()) {
            // Degree 0: the bare integer.
            (None, _) => render_integer(coefficient),
            // A unit coefficient is elided: `(^ x 2)`, never `(* 1 (^ x 2))`.
            (Some(power), true) => power,
            (Some(power), false) => format!("(* {} {power})", render_integer(coefficient)),
        });
    }
    // A `root-obj` polynomial always has at least two monomials in practice —
    // a single-monomial polynomial `c·xᵏ` has only the rational root 0, which
    // never reaches this type. Handle it anyway rather than emitting a
    // one-argument `(+ ..)`, which some readers reject.
    let polynomial = match monomials.len() {
        1 => monomials.join(""),
        _ => format!("(+ {})", monomials.join(" ")),
    };
    format!("(root-obj {polynomial} {})", value.root_index)
}

/// An integer as an SMT-LIB2 term: negatives need the `-` *operator*, since
/// the grammar has no negative numeral.
fn render_integer(value: &BigInt) -> String {
    if value.is_negative() {
        format!("(- {})", -value)
    } else {
        value.to_string()
    }
}

/// Constructor-expansion budget for [`Context::default_value`]'s datatype
/// arm.  Mirrors the solver-side ground-default budget; see
/// [`crate::solver::model_builder::ground_default_term`].
///
/// This is the *only* bound in the default-value walk, and it is deliberate:
///
/// - Array nesting needs no bound.  `Array` sorts intern bottom-up, so the
///   sort graph itself is acyclic and an array-only descent always
///   terminates; the walk is an explicit heap stack
///   ([`DefaultValueFrame`]), so depth cannot take the native stack down
///   either.  A cap here (there used to be one at 512) could only replace a
///   perfectly computable value with a wrong `?` placeholder.
/// - Datatype constructor expansion **must** be bounded, because the walk
///   steps through the datatype *definition* table and that edge can close
///   a genuine cycle: `(declare-datatype T ((c (f (Array Int T)))))` has no
///   finite ground value at all – every expansion of `c` needs a value of
///   `(Array Int T)`, which needs a value of `T` again.  (An earlier fix
///   threaded a shared budget through both halves of the cycle after the
///   original code reset its counter to 0 at every datatype re-entry and
///   recursed forever on `(get-model)`.)  When the budget is exhausted the
///   walk yields the honest placeholder `?` – visibly not a value – rather
///   than fabricating a wrong finite value for an ill-founded sort.
const DT_DEFAULT_EXPANSION_LIMIT: u32 = 16;

/// One suspended node of [`Context::default_value`]'s iterative walk.
///
/// The walk evaluates one `(sort, expansions)` task at a time; a compound
/// sort pushes a frame here, evaluates its first child, and each finished
/// child value is folded back into the innermost frame.
enum DefaultValueFrame {
    /// `((as const {sort_name}) {range_default})`, waiting for the range
    /// default.
    ArrayConst {
        /// The rendered name of the array sort itself.
        sort_name: String,
    },
    /// `({name} {field defaults...})`, collecting field defaults in order.
    Constructor {
        /// The constructor's name.
        name: String,
        /// Field default values collected so far.
        done: Vec<String>,
        /// All field sorts of the constructor.
        fields: Vec<SortId>,
        /// Index into `fields` of the next field to evaluate.
        next_field: usize,
        /// The constructor-expansion count charged to every field.
        expansions: u32,
    },
}

/// One suspended compound node of [`Context::format_sort_name`]'s iterative
/// walk: an `(Array dom rng)` or a `(Name arg...)` parametric application.
enum SortNameFrame {
    /// The domain is being rendered; the range is next.
    RangeAfter {
        /// The array sort this frame will finish.
        sort: SortId,
        /// The not-yet-rendered range sort.
        range: SortId,
    },
    /// The range is being rendered; the domain's text is finished.
    Finish {
        /// The array sort this frame will finish.
        sort: SortId,
        /// The rendered domain text.
        domain: String,
    },
    /// The element sort is being rendered; wrapping it finishes `(Set ..)`.
    SetAfter {
        /// The set sort this frame will finish.
        sort: SortId,
    },
    /// The element sort of a bag is being rendered; wrap it as `(Bag …)`.
    SeqAfter { sort: SortId },
    BagAfter {
        /// The bag sort this frame will finish.
        sort: SortId,
    },
    /// A parametric application `(name arg...)` collecting its arguments in
    /// order.
    Parametric {
        /// The parametric sort this frame will finish.
        sort: SortId,
        /// The already-resolved head name.
        name: String,
        /// Argument texts rendered so far.
        done: Vec<String>,
        /// All argument sorts of the application.
        args: Vec<SortId>,
        /// Index into `args` of the next argument to render.
        next: usize,
    },
}

fn render_eval_value(
    value: &crate::solver::EvalVal,
    term: TermId,
    manager: &nixie_core::ast::TermManager,
) -> Option<String> {
    let sort_kind = manager
        .get(term)
        .and_then(|t| manager.sorts.get(t.sort))
        .map(|s| &s.kind);
    match value {
        crate::solver::EvalVal::Bool(flag) => {
            matches!(sort_kind, Some(SortKind::Bool)).then(|| flag.to_string())
        }
        crate::solver::EvalVal::Bv { value, width } => match sort_kind {
            Some(SortKind::BitVec(sort_width)) if sort_width == width => {
                Some(nixie_core::smtlib::format_bitvec_literal(value, *width))
            }
            _ => None,
        },
        crate::solver::EvalVal::NumBig(rational) => match sort_kind {
            Some(SortKind::Int) if rational.is_integer() => Some(rational.to_integer().to_string()),
            Some(SortKind::Real) => Some(if rational.is_integer() {
                format!("{}.0", rational.numer())
            } else {
                format!("(/ {} {})", rational.numer(), rational.denom())
            }),
            _ => None,
        },
        crate::solver::EvalVal::Num(rational) => match sort_kind {
            Some(SortKind::Int) if *rational.denom() == 1 => Some(rational.numer().to_string()),
            Some(SortKind::Real) => Some(if *rational.denom() == 1 {
                format!("{}.0", rational.numer())
            } else {
                format!("(/ {} {})", rational.numer(), rational.denom())
            }),
            _ => None,
        },
    }
}

impl Context {
    pub(super) fn func_interp_reading(
        &self,
        func_name: &str,
        solver_model: &crate::solver::Model,
        class_values: &class_values::ClassValues,
        assert_function: bool,
    ) -> Option<(RawFuncInterp, bool)> {
        let mut is_function = true;
        // Find the declared function so we know its arity and default sort.
        let decl = self.declared_funs.iter().find(|d| d.name == func_name)?;
        let arity = decl.arg_sorts.len();
        if let Some(table) = self.published.function_overrides.get(func_name) {
            return Some((table.clone(), true));
        }
        let default_else = self.default_value(decl.ret_sort);

        // Resolve `func_name` to the EUF function-symbol id.  For an `Apply`
        // term the EUF id is the underlying value of the function-name `Spur`,
        // so we recover it from any matching application term (read-only — no
        // mutable interner access required).
        let mut func_id: Option<u32> = None;
        for idx in 0..(self.terms.len() as u32) {
            let tid = TermId(idx);
            let Some(term) = self.terms.get(tid) else {
                continue;
            };
            if let TermKind::Apply {
                func: func_spur, ..
            } = &term.kind
                && self.terms.resolve_str(*func_spur) == func_name
            {
                func_id = Some(func_spur.into_inner().get());
                break;
            }
        }

        // No application of this function exists in the E-graph: the function is
        // declared but never applied, so its interpretation is purely the default.
        let Some(func_id) = func_id else {
            return Some(((Vec::new(), default_else, arity), true));
        };

        // Pull congruence-closed application entries from the EUF solver.  Each
        // entry already has its argument and result classes canonicalized, so
        // congruence (e.g. f(a) == f(b) when a == b) is applied for us.
        let mut euf_entries = self.solver.euf_function_entries(func_id);
        // Specialized solvers (notably finite fields) can own an application
        // without interning it into EUF. Its checked model entry is equally
        // part of the function's interpretation.
        let mut applications: Vec<_> = solver_model.assignments().keys().copied().collect();
        applications.sort_unstable();
        for term in applications {
            let Some(TermKind::Apply { func, args }) = self.terms.get(term).map(|t| &t.kind) else {
                continue;
            };
            if self.terms.resolve_str(*func) != func_name
                || euf_entries
                    .iter()
                    .any(|entry| entry.result_class_terms.contains(&term))
            {
                continue;
            }
            euf_entries.push(nixie_theories::euf::FuncAppEntry {
                arg_reps: args
                    .iter()
                    .map(|&arg| {
                        self.solver
                            .euf_class_representative(arg)
                            .unwrap_or(arg.raw())
                    })
                    .collect(),
                arg_class_terms: args
                    .iter()
                    .map(|&arg| self.solver.euf_class_terms(arg))
                    .collect(),
                result_rep: self
                    .solver
                    .euf_class_representative(term)
                    .unwrap_or(term.raw()),
                result_class_terms: vec![term],
            });
        }

        // Deduplicate on the canonical argument-class representative tuple so
        // congruent applications produce exactly one entry.  Because congruence
        // forces congruent applications into the same result class, the values
        // agree in a consistent model.
        // Keyed by the *evaluated* argument tuple, not by the class
        // representatives: two argument classes with no concrete value of
        // their own render as the same fallback, and keying on the
        // representatives let both through — `(p a)` and `(not (p b))` over an
        // uninterpreted sort printed `(ite (= x!0 @uc_U_0) true (ite (= x!0
        // @uc_U_0) false true))`, one guard twice with contradicting answers
        // (`#P2b-34`).  With every argument resolved through the canonical map
        // the collision is gone, and keying on what is printed is what makes
        // that structural rather than incidental.
        // Keyed by the rendered tuple, carrying the tuple's *class* keys so a
        // violation names them.  Two entries with the same rendered arguments
        // and different values cannot both be right, whether they come from
        // one class (a contradiction in the canonical map) or from two (a
        // model in which two arguments the solver kept apart are published
        // indistinguishably — the array-model defect `#P2b-37` closed by
        // giving every pair of foreign arrays in different classes a witness
        // read that separates them).  The assertion is unscoped for that
        // reason: it is the property the printed interpretation needs, and
        // narrowing it to same-class collisions is what let the second kind
        // pass unnoticed.
        let mut seen_arg_keys: crate::prelude::HashMap<Vec<String>, (Vec<u64>, String)> =
            crate::prelude::HashMap::new();
        let mut entries: Vec<(Vec<String>, String)> = Vec::new();
        let mut deferred: Vec<(&nixie_theories::euf::FuncAppEntry, String)> = Vec::new();
        for entry in &euf_entries {
            // Resolve the result value first: skip applications whose class has
            // no concrete model value (an unconstrained application contributes
            // nothing observable beyond the else-branch).
            let Some(val_str) =
                self.class_value_string(&entry.result_class_terms, solver_model, class_values)
            else {
                continue;
            };

            // Resolve each argument to its canonical model value.  An
            // argument class the model gives no value at all makes the whole
            // entry unusable: substituting the argument *sort's* default
            // invented a fact, and the invented tuple then collided with a
            // real one — `(bvslt (f w) #b00)` with `w` modelled `#b00` printed
            // `f(#b00) = #b00`, because an unrelated application whose
            // argument the model left open was rendered at `#b00` first and
            // won the deduplication (`#P2b-34`).  The else-value covers the
            // point honestly instead.
            let exact: Option<Vec<String>> = entry
                .arg_class_terms
                .iter()
                .map(|members| self.class_value_string(members, solver_model, class_values))
                .collect();
            let arg_strs = match exact {
                Some(args) => args,
                None => {
                    // Keep it for a second pass: the sort default is a guess,
                    // and a guess must never take the tuple a real entry
                    // needs.
                    deferred.push((entry, val_str));
                    continue;
                }
            };

            let class_keys: Vec<u64> = entry
                .arg_class_terms
                .iter()
                .map(|members| {
                    members
                        .first()
                        .map_or(u64::MAX, |&member| self.class_key(member))
                })
                .collect();
            if let Some((seen_keys, seen_value)) = seen_arg_keys.get(&arg_strs) {
                is_function &= *seen_value == val_str;
                debug_assert!(
                    !assert_function || *seen_value == val_str,
                    "two interpretation entries for {func_name}{arg_strs:?} disagree: the \
                     canonical class -> value map gave {val_str} and {seen_value} (argument \
                     classes {class_keys:?} and {seen_keys:?})"
                );
                continue;
            }
            seen_arg_keys.insert(arg_strs.clone(), (class_keys, val_str.clone()));
            entries.push((arg_strs, val_str));
        }

        // Second pass: entries whose argument the model left open.  The
        // corresponding sort default stands in, but only for a tuple no exact
        // entry claimed.
        for (entry, val_str) in deferred {
            let arg_strs: Vec<String> = entry
                .arg_class_terms
                .iter()
                .enumerate()
                .map(|(i, members)| {
                    self.class_value_string(members, solver_model, class_values)
                        .unwrap_or_else(|| {
                            decl.arg_sorts
                                .get(i)
                                .map_or_else(|| "?".to_string(), |&s| self.default_value(s))
                        })
                })
                .collect();
            if seen_arg_keys.contains_key(&arg_strs) {
                continue;
            }
            seen_arg_keys.insert(arg_strs.clone(), (Vec::new(), val_str.clone()));
            entries.push((arg_strs, val_str));
        }

        // Pick `else_value`: the most common entry value (ties → first seen),
        // matching Z3's habit of reusing an existing value as the default.
        let else_value = Self::most_common_value(&entries).unwrap_or(default_else);
        let else_value = self.else_override(func_name).unwrap_or(else_value);

        Some(((entries, else_value, arity), is_function))
    }

    pub(super) fn func_interp_from(
        &self,
        func_name: &str,
        solver_model: &crate::solver::Model,
        class_values: &class_values::ClassValues,
    ) -> Option<RawFuncInterp> {
        self.func_interp_reading(func_name, solver_model, class_values, true)
            .map(|(interp, _)| interp)
    }

    pub(super) fn model_rows(&self) -> Option<Vec<(String, String, String)>> {
        if self.last_result != Some(SolverResult::Sat) {
            return None;
        }

        let mut model = Vec::new();
        // An empty assertion stack is satisfied by *every* assignment, so the
        // solver answers `sat` without ever building a model.  Completing from
        // the sort defaults is exact there, not a guess — with nothing asserted
        // no constraint exists that a completion could violate — whereas
        // reporting "no model available" for a `sat` verdict is simply wrong.
        // Any other missing model is a genuine extraction failure and stays
        // `None`, so a real assignment is never fabricated.
        //
        // A nonlinear-real model whose values are algebraic is the second
        // exception. There is no `Model` for it — `√2` has no term in the
        // rational term language — and yet the assignment is fully known: it
        // lives in `Solver::nl_algebraic_values`, which is populated only
        // all-or-nothing and only for a real cell decomposition's `Sat` (see
        // that field). So the gate opens on that map being non-empty, and on
        // nothing weaker: widening it to "assertions non-empty" would fabricate
        // a sort-default model for every other modelless `sat` in the tree.
        let empty_model;
        let solver_model = match self.published_model() {
            Some(solver_model) => solver_model,
            None if self.assertions.is_empty() || !self.solver.nl_algebraic_values().is_empty() => {
                empty_model = crate::solver::Model::new();
                &empty_model
            }
            None => return None,
        };

        // The one canonical class → value map of this query (`#P2b-34`): the
        // constants below, every `define-fun` interpretation, every array
        // chain and `(get-value …)` all read their answers out of it, so two
        // renderers cannot describe the same class differently.  It carries
        // the synthesised `@uc_S_n` witnesses for unconstrained
        // uninterpreted-sort constants — grouped by congruence class, so
        // constants proven equal share a witness and distinct ones stay
        // distinct — as well as every value the circuit or the tableau
        // published.
        let class_values = self.build_class_values(solver_model);

        for decl in &self.declared_consts {
            // The exact-value side-channel is consulted first. It is only ever
            // populated when the ordinary `Model` is absent, so this cannot
            // shadow a real model entry today; consulting it first is what
            // keeps that true if one ever coexisted, because it is the more
            // precise of the two (a `Model` value for the same constant could
            // only be a rounded stand-in). Without this arm the sqrt2 goal
            // falls through to `default_value(Real)` and reports `0.0` — a
            // number satisfying none of its assertions.
            let value = if let Some(value) = self.published.literal_values.get(&decl.term) {
                value.clone()
            } else if let Some(exact) = self.solver.nl_algebraic_value(decl.term) {
                render_nl_witness_value(exact)
            } else if self.is_uninterpreted_sort(decl.sort)
                && let Some(value) = class_values.get(self.class_key(decl.term))
            {
                value.to_string()
            } else if matches!(
                self.terms.sorts.get(decl.sort).map(|s| &s.kind),
                Some(SortKind::Array { .. })
            ) {
                self.array_model_value(decl.term, decl.sort, solver_model, &class_values)
                    .unwrap_or_else(|| self.default_value(decl.sort))
            } else if let Some(value) = self.alias_model_values.get(&decl.term) {
                self.format_value_at(*value, decl.term)
            } else if let Some(val) = solver_model.get(decl.term) {
                self.format_value_at(val, decl.term)
            } else if let Some(chain) =
                self.array_model_value(decl.term, decl.sort, solver_model, &class_values)
            {
                // An array is never *assigned* a value term — there is no
                // literal for "the function `{0 ↦ 5}` extended by 0" — so
                // before `#P2b-34` it fell through to the sort default and
                // printed `((as const …) #x00)` beside its own `select`
                // entries saying otherwise.  The published reads are that
                // function; a `store` chain over the default is how SMT-LIB
                // spells it.
                chain
            } else if let Some(witness) = self
                .is_uninterpreted_sort(decl.sort)
                .then(|| class_values.get(self.class_key(decl.term)))
                .flatten()
            {
                // No direct model entry for an uninterpreted-sort constant:
                // the canonical map's synthesized Z3-style `@uc_S_n` abstract
                // witness, which is grouped by congruence class so equal
                // constants share one and distinct constants get distinct
                // ones.  Always a valid value, unlike the previous invalid
                // `?` — and, being the same map every other renderer reads,
                // the same witness `f`'s interpretation prints.
                witness.to_string()
            } else if let Some(value) =
                self.datatype_class_value(decl.term, decl.sort, solver_model, &class_values)
            {
                // A datatype constant the reconstruction could not build
                // (`#P2b-39`): assembled from the values this model gives the
                // *selector applications* the script itself spells, rather
                // than from the sort defaults.  Falling through to
                // `default_value` printed a constructor whose fields were the
                // sort defaults while `(get-value ((tag b)))` answered the
                // asserted value out of the same model in the same run — 153
                // of 300 generated datatype scripts published a model that
                // contradicted their own assertions that way.
                value
            } else {
                self.defined_bool_value(decl.term, solver_model)
                    .unwrap_or_else(|| self.default_value(decl.sort))
            };
            let sort_name = self.format_sort_name(decl.sort);
            model.push((decl.name.clone(), sort_name, value));
        }

        Some(model)
    }

    fn published_model_withheld(&self) -> bool {
        self.uncertified_model_error().is_some()
    }

    /// Quote the entire witness symbol, rather than embedding a quoted sort
    /// token inside a simple symbol.
    fn format_uninterpreted_witness(&self, sort: SortId, index: usize) -> String {
        let rendered = self.format_sort_name(sort);
        let name = rendered
            .strip_prefix('|')
            .and_then(|s| s.strip_suffix('|'))
            .unwrap_or(&rendered);
        // User @ symbols are legal in Nixie. Number only fresh spellings so
        // declaring @uc_U_0 cannot turn an abstract value into a self-reference.
        // Consider declarations, never parse-back artifacts in the term arena:
        // repeated get-model/get-value calls must retain the same numbering.
        let prefix = format!("@uc_{name}_");
        let mut occupied: Vec<u128> = self
            .declared_consts
            .iter()
            .map(|d| d.name.as_str())
            .chain(self.declared_funs.iter().map(|d| d.name.as_str()))
            .filter_map(|symbol| {
                let suffix = symbol.strip_prefix(&prefix)?;
                let number = suffix.parse::<u128>().ok()?;
                (number.to_string() == suffix).then_some(number)
            })
            .collect();
        occupied.sort_unstable();
        occupied.dedup();
        let mut candidate = index as u128;
        for reserved in occupied {
            if reserved > candidate {
                break;
            }
            candidate += 1;
        }
        nixie_core::smtlib::format_symbol(&format!("{prefix}{candidate}"))
    }

    /// Get the model (if SAT)
    /// Returns a list of (name, sort, value) tuples
    pub fn get_model(&self) -> Option<Vec<(String, String, String)>> {
        if self.published_model_withheld() {
            return None;
        }
        self.model_rows()
    }

    /// Build a raw function interpretation for a declared uninterpreted function.
    ///
    /// Derives entries from the EUF congruence closure rather than from raw
    /// `Apply` terms alone.  For every application `f(a1, …, an)` interned in the
    /// E-graph, the arguments and the result are canonicalized through their
    /// equivalence-class representatives, so:
    ///
    /// - Two applications whose arguments are pairwise congruent (e.g. `f(a)` and
    ///   `f(b)` when `a = b` is implied by the assertions) collapse to a **single**
    ///   entry keyed by the shared argument class.
    /// - The reported argument and result strings are **model values** taken from
    ///   the class (resolving through the representative), not raw term ids.
    /// - When an application has no direct model value, the value of any congruent
    ///   member of its class is used.
    ///
    /// `else_value` is chosen as the most frequently occurring entry value (ties
    /// broken by first occurrence), mirroring how Z3 selects a default; if there
    /// are no entries it falls back to the return sort's default value.
    ///
    /// Returns `None` when:
    /// - the last check was not `Sat`, or
    /// - no model is available, or
    /// - `func_name` is not a declared function.
    ///
    /// The return type is `(entries, else_value_string, arity)` to avoid
    /// pulling `nixie_core::model` types into this file.
    pub fn get_func_interp_raw(&self, func_name: &str) -> Option<RawFuncInterp> {
        if self.last_result != Some(SolverResult::Sat) {
            return None;
        }
        let solver_model = self.published_model()?;
        let class_values = self.build_class_values(solver_model);
        self.func_interp_from(func_name, solver_model, &class_values)
    }

    /// Resolve an equivalence class (its member `TermId`s) to a formatted model
    /// value string, by finding the first member that carries either a direct
    /// model assignment or is itself a literal constant.
    ///
    /// Returns `None` when no member of the class has an observable value.
    fn class_value_string(
        &self,
        members: &[TermId],
        solver_model: &crate::solver::Model,
        class_values: &class_values::ClassValues,
    ) -> Option<String> {
        // The canonical map first: it carries the `@uc_S_n` witness a class
        // over an uninterpreted sort has no term for, which is exactly the
        // class this walk used to report as valueless (`#P2b-34`).
        if let Some(&member) = members.first()
            && let Some(value) = class_values.get(self.class_key(member))
        {
            return Some(value.to_string());
        }
        // An array-sorted class is rendered the way `(get-model)` renders an
        // array constant of that class — the `store` chain over its base — so
        // `f : Array -> BV` gets one interpretation entry per array rather
        // than one per *sort*: `(distinct (f arr) (f brr))` printed `f` as a
        // constant, because both argument classes fell back to the array
        // sort's default and the second entry was deduplicated away.
        for &member in members {
            let Some(sort) = self.terms.get(member).map(|data| data.sort) else {
                continue;
            };
            if !self
                .terms
                .sorts
                .get(sort)
                .is_some_and(|s| matches!(s.kind, SortKind::Array { .. }))
            {
                continue;
            }
            if let Some(chain) = self.array_model_value(member, sort, solver_model, class_values) {
                return Some(chain);
            }
            return Some(self.default_value(sort));
        }
        // Folding a member in the model is still an *exact* answer — it is the
        // model's own arithmetic — and it is what resolves an argument like
        // `(bvsub (f #b10) v)` that has a value without having a model entry.
        for &member in members {
            if let Some(value) = self
                .solver
                .eval_under_interpretation(member, solver_model, &self.terms)
                .value_owned()
                && let Some(text) = render_eval_value(&value, member, &self.terms)
            {
                return Some(text);
            }
        }
        for &member in members {
            // Direct model assignment (covers variables and applications whose
            // value was extracted from an equality constraint).
            if let Some(val_term) = solver_model.get(member) {
                return Some(self.format_value(val_term));
            }
            // The member may itself be a literal constant (e.g. the term `5` in
            // `f(a) = 5`), which has no separate model entry but is its own value.
            if let Some(term) = self.terms.get(member)
                && matches!(
                    term.kind,
                    TermKind::True
                        | TermKind::False
                        | TermKind::IntConst(_)
                        | TermKind::RealConst(_)
                        | TermKind::BitVecConst { .. }
                )
            {
                return Some(self.format_value(member));
            }
        }
        None
    }

    /// Choose the most frequently occurring value among the interpretation
    /// entries, breaking ties in favour of the earliest occurrence.  Returns
    /// `None` for an empty entry list.
    fn most_common_value(entries: &[(Vec<String>, String)]) -> Option<String> {
        let mut counts: crate::prelude::HashMap<&str, (usize, usize)> =
            crate::prelude::HashMap::new();
        for (order, (_, value)) in entries.iter().enumerate() {
            let slot = counts.entry(value.as_str()).or_insert((0, order));
            slot.0 += 1;
        }
        counts
            .into_iter()
            .max_by(|(_, (count_a, order_a)), (_, (count_b, order_b))| {
                // Higher count wins; on a tie the smaller insertion order wins,
                // so we reverse the order comparison.
                count_a.cmp(count_b).then_with(|| order_b.cmp(order_a))
            })
            .map(|(value, _)| value.to_string())
    }

    /// Format a sort ID to its SMT-LIB2 name.
    ///
    /// Handles every `SortKind` that [`Context::parse_sort_name`] can
    /// produce (its inverse), including compound `(Array ..)`/`(_
    /// BitVec ..)`/`(_ FloatingPoint ..)` forms and previously
    /// declared uninterpreted/datatype sorts by name, so
    /// `get-model`/`get-value` output reflects a declared constant's
    /// real sort instead of falling back to a generic placeholder.
    /// Sort parameters render as their name and parametric applications as
    /// `(Name arg...)`, matching [`nixie_core::smtlib::SmtLibPrinter`]; both
    /// used to print as the literal string `Unknown`, which collapsed every
    /// such sort – however many and however different – onto one name.
    ///
    /// The walk over nested `Array`/parametric sorts is an explicit heap stack
    /// ([`SortNameFrame`]) – array-sort nesting is input-controlled (the
    /// builder API composes sorts in O(1) stack, and chained `define-sort`
    /// grows a sort by one level per command), so native recursion here was
    /// an unbounded stack risk with no error channel to cap it honestly.
    /// Sub-sorts reachable along more than one path are rendered once and
    /// memoized; the memo is restricted to genuinely shared sorts so that a
    /// deep unshared chain does not pay quadratic memory for cached copies
    /// of every suffix.  (The *output* still spells shared sorts out in
    /// full each time – SMT-LIB sort syntax has no sharing – so output
    /// size, not the walk, remains the inherent cost on heavily shared
    /// sorts.)
    fn format_sort_name(&self, sort: SortId) -> String {
        // Pre-pass over the sort DAG (visited-set bounded): find the sorts
        // reachable along more than one path, the only ones worth caching.
        let mut seen: crate::prelude::HashSet<SortId> = crate::prelude::HashSet::new();
        let mut shared: crate::prelude::HashSet<SortId> = crate::prelude::HashSet::new();
        let mut scan = vec![sort];
        while let Some(s) = scan.pop() {
            if !seen.insert(s) {
                shared.insert(s);
                continue;
            }
            if let Some(node) = self.terms.sorts.get(s) {
                // Only the compound kinds have sub-sorts to visit; the leaf
                // kinds are listed rather than swept up by a wildcard so a
                // future sort kind with children cannot silently skip the
                // pre-pass (and lose its memoization).
                match &node.kind {
                    SortKind::Seq(elem) => scan.push(*elem),
                    SortKind::Set(elem) => scan.push(*elem),
                    SortKind::Bag(elem) => scan.push(*elem),
                    SortKind::Array { domain, range } => {
                        scan.push(*domain);
                        scan.push(*range);
                    }
                    SortKind::Parametric { args, .. } => scan.extend(args.iter().copied()),
                    SortKind::Bool
                    | SortKind::Int
                    | SortKind::Real
                    | SortKind::String
                    | SortKind::BitVec(_)
                    | SortKind::FloatingPoint { .. }
                    | SortKind::RoundingMode
                    | SortKind::FiniteField(_)
                    | SortKind::Uninterpreted(_)
                    | SortKind::Parameter(_)
                    | SortKind::Datatype(_) => {}
                }
            }
        }

        let mut memo: crate::prelude::HashMap<SortId, String> = crate::prelude::HashMap::new();
        let mut pending: Vec<SortNameFrame> = Vec::new();
        let mut current = sort;
        'render: loop {
            // Render `current`, descending through `Array` domains until a
            // leaf (or memoized) sort is reached.
            let mut text: String = loop {
                if let Some(hit) = memo.get(&current) {
                    break hit.clone();
                }
                let Some(s) = self.terms.sorts.get(current) else {
                    break "Unknown".to_string();
                };
                let leaf = match &s.kind {
                    SortKind::Set(elem) => {
                        pending.push(SortNameFrame::SetAfter { sort: current });
                        current = *elem;
                        continue;
                    }
                    SortKind::Seq(elem) => {
                        pending.push(SortNameFrame::SeqAfter { sort: current });
                        current = *elem;
                        continue;
                    }
                    SortKind::Bag(elem) => {
                        pending.push(SortNameFrame::BagAfter { sort: current });
                        current = *elem;
                        continue;
                    }
                    SortKind::Array { domain, range } => {
                        pending.push(SortNameFrame::RangeAfter {
                            sort: current,
                            range: *range,
                        });
                        current = *domain;
                        continue;
                    }
                    SortKind::Bool => "Bool".to_string(),
                    SortKind::Int => "Int".to_string(),
                    SortKind::Real => "Real".to_string(),
                    SortKind::String => "String".to_string(),
                    SortKind::BitVec(w) => format!("(_ BitVec {w})"),
                    SortKind::FloatingPoint { eb, sb } => format!("(_ FloatingPoint {eb} {sb})"),
                    SortKind::RoundingMode => "RoundingMode".to_string(),
                    SortKind::FiniteField(id) => self
                        .terms
                        .sorts
                        .field_table()
                        .get(*id)
                        .map(|f| f.sort_syntax())
                        .unwrap_or_else(|| format!("<unknown field {}>", id.raw())),
                    // An uninterpreted sort's name is interned by the *term*
                    // manager (`Parser::parse_sort` for `declare-sort` names
                    // and `TermManager::reglan_sort` both call
                    // `TermManager::intern_str`), so it resolves through
                    // `self.terms`.
                    SortKind::Uninterpreted(spur) => {
                        nixie_core::smtlib::format_symbol(self.terms.resolve_str(*spur))
                    }
                    // A datatype/parameter/parametric name, by contrast, is
                    // interned by the *sort* manager's own `Rodeo`
                    // (`mk_datatype_sort` / `declare_datatype`,
                    // `mk_sort_parameter`, `declare_parametric_sort` /
                    // `instantiate_parametric_sort` / `define_parametric_sort`
                    // all go through `SortManager::interner`).  The two
                    // interners are separate, so a key from one resolved
                    // through the other yields an unrelated string or indexes
                    // out of range; each name below therefore goes through
                    // `self.terms.sorts.resolve_spur`.  Mirrors
                    // `SmtLibPrinter::write_sort`, where the same hazard is
                    // documented.
                    SortKind::Datatype(spur) => {
                        self.terms.sorts.datatype_name(current).map_or_else(
                            || {
                                nixie_core::smtlib::format_symbol(
                                    self.terms.sorts.resolve_spur(*spur),
                                )
                            },
                            nixie_core::smtlib::format_symbol,
                        )
                    }
                    SortKind::Parameter(spur) => {
                        nixie_core::smtlib::format_symbol(self.terms.sorts.resolve_spur(*spur))
                    }
                    // Rendered exactly as the printer spells it: `(Name
                    // arg...)`, arguments rendered through this same walk.
                    // Printing every parametric sort as the single literal
                    // "Unknown" used to collapse distinct sorts -- `(List
                    // Int)` and a bare parameter `T` alike -- onto one
                    // meaningless name in `(get-model)` output.
                    SortKind::Parametric { name, args } => {
                        let head =
                            nixie_core::smtlib::format_symbol(self.terms.sorts.resolve_spur(*name));
                        let args: Vec<SortId> = args.iter().copied().collect();
                        match args.first().copied() {
                            // A nullary application has no arguments to walk:
                            // `(Name)`, as `write_sort` prints it.
                            None => format!("({head})"),
                            Some(first) => {
                                pending.push(SortNameFrame::Parametric {
                                    sort: current,
                                    name: head,
                                    done: Vec::with_capacity(args.len()),
                                    args,
                                    next: 1,
                                });
                                current = first;
                                continue;
                            }
                        }
                    }
                };
                if shared.contains(&current) {
                    memo.insert(current, leaf.clone());
                }
                break leaf;
            };
            // Fold the rendered text upward: a finished domain schedules its
            // partner range; a finished range completes its `(Array ..)`.
            loop {
                match pending.pop() {
                    None => return text,
                    Some(SortNameFrame::RangeAfter { sort, range }) => {
                        pending.push(SortNameFrame::Finish { sort, domain: text });
                        current = range;
                        continue 'render;
                    }
                    Some(SortNameFrame::Finish { sort, domain }) => {
                        text = format!("(Array {domain} {text})");
                        if shared.contains(&sort) {
                            memo.insert(sort, text.clone());
                        }
                    }
                    Some(SortNameFrame::SetAfter { sort }) => {
                        text = format!("(Set {text})");
                        if shared.contains(&sort) {
                            memo.insert(sort, text.clone());
                        }
                    }
                    Some(SortNameFrame::SeqAfter { sort }) => {
                        text = format!("(Seq {text})");
                        if shared.contains(&sort) {
                            memo.insert(sort, text.clone());
                        }
                    }
                    Some(SortNameFrame::BagAfter { sort }) => {
                        text = format!("(Bag {text})");
                        if shared.contains(&sort) {
                            memo.insert(sort, text.clone());
                        }
                    }
                    Some(SortNameFrame::Parametric {
                        sort,
                        name,
                        mut done,
                        args,
                        next,
                    }) => {
                        done.push(text);
                        match args.get(next).copied() {
                            Some(arg) => {
                                pending.push(SortNameFrame::Parametric {
                                    sort,
                                    name,
                                    done,
                                    args,
                                    next: next + 1,
                                });
                                current = arg;
                                continue 'render;
                            }
                            None => {
                                text = format!("({name} {})", done.join(" "));
                                if shared.contains(&sort) {
                                    memo.insert(sort, text.clone());
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /// Whether `sort` is an uninterpreted (user-declared) sort.
    fn is_uninterpreted_sort(&self, sort: SortId) -> bool {
        !self.is_rounding_mode_sort(sort)
            && self
                .terms
                .sorts
                .get(sort)
                .is_some_and(|s| matches!(s.kind, SortKind::Uninterpreted(_)))
    }

    /// Render numeric values at the sort of the declaration they interpret.
    fn format_value_at(&self, value: TermId, target: TermId) -> String {
        if !self.terms.get(target).is_some_and(|node| {
            node.sort == self.terms.sorts.int_sort || node.sort == self.terms.sorts.real_sort
        }) {
            return self.format_value(value);
        }
        crate::solver::array_completion_certify::evaluate_closed_value_pure(
            &self.solver,
            value,
            &self.terms,
        )
        .and_then(|value| render_eval_value(&value, target, &self.terms))
        .unwrap_or_else(|| self.format_value(value))
    }

    /// Format a model value
    fn format_value(&self, term: TermId) -> String {
        match self.terms.get(term).map(|t| &t.kind) {
            Some(TermKind::Apply { .. })
                if crate::solver::array_axioms::const_array_default(term, &self.terms).is_some() => {
                    nixie_core::smtlib::Printer::new(&self.terms).print_term(term)
                }
            Some(TermKind::True) => "true".to_string(),
            Some(TermKind::False) => "false".to_string(),
            Some(TermKind::IntConst(n)) => n.to_string(),
            Some(TermKind::RealConst(r)) => {
                if *r.denom() == 1 {
                    format!("{}.0", r.numer())
                } else {
                    format!("(/ {} {})", r.numer(), r.denom())
                }
            }
            Some(TermKind::BitVecConst { value, width }) => {
                format!(
                    "#b{:0>width$}",
                    format!("{:b}", value),
                    width = *width as usize
                )
            }
            // Floating-point constants, array store/const-array chains, string
            // literals and datatype constructor applications are structured
            // values that the shared SMT-LIB printer renders faithfully
            // (`(fp ..)`, `(_ +zero eb sb)`, `(store ..)`, `"..."`,
            // `(cons 7 nil)`), so delegate rather than emitting an invalid `?`
            // placeholder.
            //
            // Delegating matters beyond brevity for the datatype case:
            // `(get-value ..)` renders through the very same printer (see
            // [`Context::format_get_value`]), so routing `(get-model)` through
            // it is what keeps the two commands character-for-character in
            // agreement about a reconstructed datatype value.
            Some(
                TermKind::FpLit { .. }
                    | TermKind::FpPlusInfinity { .. }
                    | TermKind::FpMinusInfinity { .. }
                    | TermKind::FpPlusZero { .. }
                    | TermKind::FpMinusZero { .. }
                    | TermKind::FpNaN { .. }
                    | TermKind::Store(..)
                    | TermKind::StringLit(_)
                    | TermKind::DtConstructor { .. }
                    // A synthesized exact arithmetic value: the
                    // wide-publication channel's `(/ numer denom)` term
                    // (which the constructor folds to `(* numer 1)`-shaped
                    // products when the denominator is 1, and plain
                    // numerals for integer sorts).  The shared printer
                    // renders `Div` by sort (`/` for `Real`, Euclidean
                    // `div` for `Int`) and the compound arithmetic forms
                    // as themselves, keeping the printed model
                    // re-readable as the same value — the `?` placeholder
                    // this arm used to fall through to is not a value at
                    // all (the exact-publication build's `get-model` gap:
                    // `get-value` printed the rational while `get-model`
                    // printed `?` for the same entry).
                    | TermKind::Div(..)
                    | TermKind::Add(..)
                    | TermKind::Sub(..)
                    | TermKind::Mul(..)
                    | TermKind::Neg(..)
                    // A synthesized set value: a canonical
                    // `set.union`-of-`set.singleton` term (or `set.empty`),
                    // which the printer renders as itself — so a printed
                    // model re-reads as the same value.
                    | TermKind::SetEmpty(_)
                    | TermKind::SetSingleton(_)
                    | TermKind::SetUnion(_, _)
                    // A synthesized bag value: a canonical
                    // `bag.union_disjoint`-of-`(bag e n)` term (or
                    // `bag.empty`), likewise rendered as itself.
                    | TermKind::BagEmpty(_)
                    | TermKind::BagMake(_, _)
                    | TermKind::BagUnionDisjoint(_, _)
                    // A field element: the printer renders the exact
                    // `#f<v>m<p>` literal.
                    | TermKind::FfConst { .. },
            ) => {
                let printer = nixie_core::smtlib::Printer::new(&self.terms);
                printer.print_term(term)
            }
            // A rounding-mode value: a nullary `Var` at the reserved
            // `RoundingMode` sort, interned under the canonical long name —
            // print the name (that IS the value's SMT-LIB spelling).
            // (Ported from upstream v0.3.3.)
            Some(TermKind::Var(spur))
                if self
                    .terms
                    .get(term)
                    .is_some_and(|t| t.sort == self.terms.sorts.rounding_mode_sort) =>
            {
                nixie_core::smtlib::format_symbol(self.terms.resolve_str(*spur))
            }
            Some(TermKind::Var(name)) if self.terms.get(term).is_some_and(|t| self.is_uninterpreted_sort(t.sort)) => {
                nixie_core::smtlib::format_symbol(self.terms.resolve_str(*name))
            }
            _ => "?".to_string(),
        }
    }

    /// Get a default value for a sort.
    ///
    /// Used to complete `get-model` output for a declared constant that the
    /// model left unconstrained.  Every case yields a *valid* SMT-LIB value of
    /// the sort (never the invalid `?` placeholder), except uninhabited or
    /// ill-founded datatypes, which have no ground value at all.
    ///
    /// The walk is an explicit heap stack ([`DefaultValueFrame`]), so array
    /// nesting of any depth is rendered in full – the pre-conversion code
    /// both recursed natively and truncated every value below 512 sort
    /// levels to a wrong `?`.  The datatype arm expands constructors:
    ///
    /// - `nil`-style nullary constructors render as their bare name;
    /// - compound constructors render as an application of the field
    ///   defaults (`(mk-pair 0 0)`), the constructor chosen by the shared
    ///   [`default_constructor_index`](crate::solver::model_builder::default_constructor_index)
    ///   policy – the first one with no datatype-sorted field, so a
    ///   well-founded construction bottoms out immediately, matching the
    ///   solver's own reconstruction of an underdetermined datatype term;
    /// - expansion is bounded by [`DT_DEFAULT_EXPANSION_LIMIT`], the one
    ///   *deliberate* bound in this walk: an ill-founded declaration such
    ///   as `(declare-datatype T ((c (f T))))`, or one that closes the
    ///   cycle through an array field as in
    ///   `(declare-datatype D ((c (f (Array Int D)))))`, has no finite
    ///   ground value at all, and yields the honest `?` placeholder rather
    ///   than a non-terminating expansion (see the limit's doc comment).
    fn default_value(&self, sort: SortId) -> String {
        let mut pending: Vec<DefaultValueFrame> = Vec::new();
        // The task being evaluated: a sort, and the number of datatype
        // constructor expansions already charged on the path to it.
        let mut task: (SortId, u32) = (sort, 0);
        'task: loop {
            // Evaluate `task` down to a leaf value, pushing a frame for
            // each compound sort passed through on the way.
            let mut value: String = loop {
                let (sort, expansions) = task;
                let Some(s) = self.terms.sorts.get(sort) else {
                    break "?".to_string();
                };
                match &s.kind {
                    SortKind::Bool => break "false".to_string(),
                    SortKind::Int => break "0".to_string(),
                    SortKind::Real => break "0.0".to_string(),
                    // The empty set is ground and exists at every element
                    // sort, so no witness has to be minted for it.
                    SortKind::Set(_) => {
                        break format!("(as set.empty {})", self.format_sort_name(sort));
                    }
                    // The empty bag is ground and exists at every element
                    // sort, likewise.
                    SortKind::Seq(_) => {
                        break format!("(as seq.empty {})", self.format_sort_name(task.0));
                    }
                    SortKind::Bag(_) => {
                        break format!("(as bag.empty {})", self.format_sort_name(sort));
                    }
                    // The empty string is the canonical ground `String`
                    // value; the old `?` fallback was not valid SMT-LIB
                    // output at all.
                    SortKind::String => break "\"\"".to_string(),
                    SortKind::BitVec(w) => {
                        break format!("#b{:0>width$}", "0", width = *w as usize);
                    }
                    // Positive zero is a canonical, valid ground FP value.
                    SortKind::FloatingPoint { eb, sb } => break format!("(_ +zero {eb} {sb})"),
                    // The canonical default rounding mode (matches
                    // `ValueFactory`'s default for the sort).
                    SortKind::RoundingMode => break "roundNearestTiesToEven".to_string(),
                    // The field's zero element, spelled as its SMT-LIB
                    // literal so the default re-reads as itself.
                    SortKind::FiniteField(id) => {
                        let zero = self
                            .terms
                            .sorts
                            .field_table()
                            .get(*id)
                            .map(|f| f.literal_syntax(&num_bigint::BigInt::from(0)))
                            .unwrap_or_else(|| format!("#f0m(field {})", id.raw()));
                        break zero;
                    }
                    // A constant array whose every entry is the range's
                    // default value.  Descending into the range charges no
                    // constructor expansion – the sort graph alone is
                    // acyclic, so this edge cannot close a cycle.
                    SortKind::Array { range, .. } => {
                        let range = *range;
                        let sort_name = self.format_sort_name(sort);
                        pending.push(DefaultValueFrame::ArrayConst { sort_name });
                        task = (range, expansions);
                    }
                    // A datatype default is a ground constructor
                    // application built from the field sorts' own
                    // defaults.  Every field charges one constructor
                    // expansion, whatever its sort: the pre-fix code
                    // charged nothing for non-datatype fields and
                    // re-entered the walk at depth zero, which is exactly
                    // the reset that let an array-mediated cycle run
                    // forever.
                    SortKind::Datatype(_) => {
                        if expansions >= DT_DEFAULT_EXPANSION_LIMIT {
                            break "?".to_string();
                        }
                        let Some(dt_name) = self.terms.sorts.datatype_name(sort) else {
                            break "?".to_string();
                        };
                        let dt_name = dt_name.to_string();
                        let Some(def) = self.terms.sorts.get_datatype(&dt_name) else {
                            break "?".to_string();
                        };
                        let Some(index) = crate::solver::model_builder::default_constructor_index(
                            def,
                            &self.terms.sorts,
                        ) else {
                            break "?".to_string();
                        };
                        let Some(constructor) = def.constructors.get(index) else {
                            break "?".to_string();
                        };
                        let name = nixie_core::smtlib::format_symbol(
                            self.terms.sorts.resolve_spur(constructor.name),
                        );
                        let fields: Vec<SortId> = constructor
                            .selectors
                            .iter()
                            .map(|&(_, field_sort)| field_sort)
                            .collect();
                        // A nullary constructor is already its own ground
                        // value.  (`fields.first()` returning `None` is the
                        // same statement as `selectors.is_empty()`; matching
                        // on it keeps the non-empty arm unwrap-free.)
                        let charged = expansions.saturating_add(1);
                        match fields.first().copied() {
                            None => break name,
                            Some(first) => {
                                let arity = fields.len();
                                pending.push(DefaultValueFrame::Constructor {
                                    name,
                                    done: Vec::with_capacity(arity),
                                    fields,
                                    next_field: 1,
                                    expansions: charged,
                                });
                                task = (first, charged);
                            }
                        }
                    }
                    // Uninterpreted-sort defaults are abstract witnesses.
                    // `get_model` assigns a distinct per-constant index; as
                    // a standalone fallback emit the zero-th witness for
                    // the sort.
                    SortKind::Uninterpreted(_) => {
                        break self.format_uninterpreted_witness(sort, 0);
                    }
                    // Sort parameters and unapplied parametric sorts have
                    // no ground values.
                    SortKind::Parameter(_) | SortKind::Parametric { .. } => {
                        break "?".to_string();
                    }
                }
            };
            // Fold the finished value into the innermost pending frame; a
            // constructor frame with fields left schedules the next one.
            loop {
                match pending.pop() {
                    None => return value,
                    Some(DefaultValueFrame::ArrayConst { sort_name }) => {
                        value = format!("((as const {sort_name}) {value})");
                    }
                    Some(DefaultValueFrame::Constructor {
                        name,
                        mut done,
                        fields,
                        next_field,
                        expansions,
                    }) => {
                        done.push(value);
                        match fields.get(next_field).copied() {
                            Some(field_sort) => {
                                pending.push(DefaultValueFrame::Constructor {
                                    name,
                                    done,
                                    fields,
                                    next_field: next_field + 1,
                                    expansions,
                                });
                                task = (field_sort, expansions);
                                continue 'task;
                            }
                            None => value = format!("({} {})", name, done.join(" ")),
                        }
                    }
                }
            }
        }
    }

    /// A ground *term* carrying the same default value that
    /// [`Context::default_value`] renders as a string, or `None` for sorts with
    /// no constructible ground witness (uninterpreted and array sorts, sort
    /// parameters, and ill-founded datatypes).
    ///
    /// Used to complete the model before a `(get-value ...)` evaluation, so a
    /// query over an unconstrained constant – including inside a compound term
    /// such as `(+ x 1)` – reduces to a real value instead of echoing itself.
    ///
    /// Delegates to the solver's
    /// [`ground_default_term`](crate::solver::model_builder::ground_default_term),
    /// which is also what fills in an unconstrained *field* of a reconstructed
    /// datatype value – one definition of "the default of this sort" rather
    /// than one per caller.
    fn default_value_term(&mut self, sort: SortId) -> Option<TermId> {
        crate::solver::model_builder::ground_default_term(&mut self.terms, sort)
    }

    /// The value string [`Context::get_model`] reports for `term`, when `term`
    /// is a declared constant that the model left unassigned.
    ///
    /// `(get-value ...)` and `(get-model)` must never disagree about the same
    /// constant, and `get_model`'s uninterpreted-sort witnesses (`@uc_S_n`) are
    /// numbered across the whole declaration list – so the answer is read back
    /// out of `get_model` itself rather than recomputed.
    fn unassigned_const_value(&self, term: TermId, model: &crate::solver::Model) -> Option<String> {
        let index = self.declared_consts.iter().position(|d| d.term == term)?;
        // A constant the model *did* assign keeps the ordinary evaluation path.
        if model.get(term).is_some() {
            return None;
        }
        let (_, _, value) = self.get_model()?.into_iter().nth(index)?;
        Some(value)
    }

    /// Answer a `(get-value (t1 .. tn))` request.
    ///
    /// SMT-LIB 2.6 §4.1.1: the command is available only in `sat` mode, so a
    /// missing/superseded check result is reported as an error rather than
    /// answered from stale state.  Each term is evaluated in the current model,
    /// which is first *completed* with the sort defaults `get_model` reports for
    /// unconstrained declared constants – otherwise `Model::eval` returns an
    /// unassigned constant unchanged and `(get-value (x))` answered `((x x))`,
    /// echoing the term instead of producing a value.
    fn format_get_value_legacy(&mut self, terms: &[TermId], keys: &[String]) -> String {
        if terms.len() != keys.len() {
            return "(error \"get-value query spellings do not match its terms\")".into();
        }
        const NO_MODEL: &str = "(error \"No model available\")";
        if self.last_result != Some(SolverResult::Sat) {
            return NO_MODEL.to_string();
        }
        // Owned so the evaluation below can borrow `self.terms` mutably; see
        // `get_model` for why an empty assertion stack — or a populated
        // algebraic side-channel — yields an empty model rather than an error.
        let mut model = match self.published_model() {
            Some(model) => model.clone(),
            None if self.assertions.is_empty() || !self.solver.nl_algebraic_values().is_empty() => {
                crate::solver::Model::new()
            }
            None => return NO_MODEL.to_string(),
        };

        // Completion substitution: every declared constant with no model entry
        // maps to its sort default.
        //
        // A constant the algebraic side-channel *does* pin is excluded. Its
        // sort default is `0.0`, and substituting that would answer a compound
        // query like `(get-value ((* x x)))` with `0.0` for a goal whose
        // witness is `√2` — a fabricated value, and one contradicting the `2.0`
        // that the very same model implies. Left out of the map the term
        // survives evaluation unreduced and echoes back, which is the same
        // honest non-answer this path already gives for anything else it
        // cannot fold. (A bare `(get-value (x))` never reaches the completion
        // at all: `unassigned_const_value` answers it from `get_model` below,
        // which is where the `root-obj` rendering lives.)
        let unassigned: Vec<(TermId, SortId)> = self
            .declared_consts
            .iter()
            .filter(|d| model.get(d.term).is_none())
            .filter(|d| self.solver.nl_algebraic_value(d.term).is_none())
            .map(|d| (d.term, d.sort))
            .collect();
        let mut completion: crate::prelude::FxHashMap<TermId, TermId> =
            crate::prelude::FxHashMap::default();
        for (term, sort) in unassigned {
            if let Some(value) = self.default_value_term(sort) {
                completion.insert(term, value);
            }
        }

        // Relation compounds the query mentions that the assertion stack
        // never did (`(get-value ((rel.join r s)))` with no asserted
        // membership in the join): the model-build survey walks the
        // assertions, so such compounds have no entry. Compose them on
        // demand from the operands' verified values — the compound is a
        // function of its operands, so the composed value is not a guess;
        // anything the pass cannot verify still echoes (the honest
        // non-answer). Explicit-stack walk: queries nest arbitrarily.
        let mentions_rel = terms.iter().any(|&t| {
            let mut stack = vec![t];
            let mut seen = crate::prelude::FxHashSet::default();
            while let Some(cur) = stack.pop() {
                if !seen.insert(cur) {
                    continue;
                }
                let Some(kind) = self.terms.get(cur).map(|d| d.kind.clone()) else {
                    continue;
                };
                if matches!(
                    kind,
                    nixie_core::ast::TermKind::SetRelJoin(_, _)
                        | nixie_core::ast::TermKind::SetRelProduct(_, _)
                        | nixie_core::ast::TermKind::SetRelTranspose(_)
                        | nixie_core::ast::TermKind::SetRelIden(_)
                ) {
                    return true;
                }
                stack.extend(nixie_core::ast::traversal::get_children(&kind));
            }
            false
        });
        if mentions_rel {
            let survey = crate::solver::set_theory::survey_for_model(terms, &self.terms);
            self.solver
                .complete_rel_values(&survey, &mut model, &mut self.terms);
        }
        self.solver
            .complete_set_query(terms, &mut model, &mut self.terms);
        // Bag queries over an installed bag value: `bag.card`, `bag.count`
        // and `bag.member` are *functions of the value* (which the model
        // pass verified), so folding them is evaluation, not a guess. A
        // query-only `(bag.card b)` — one whose assertion stack never
        // constrained any cardinality — is exactly the case with no
        // readback entry to print otherwise.
        //
        // A query-only `bag.choose` — one the assertion stack never
        // mentioned, so the reduction stated no choose axiom and the bag
        // pass valued nothing — completes first, from the same installed
        // value: the first cell's element (a member, which is what the
        // choose of a nonempty bag is), or a fresh `0`-style default over
        // an empty bag (unspecified, so any value models it). This is the
        // same "complete the model before the query" discipline as the
        // rel pass above — and it must run *before* the folds below,
        // because `(bag.count (bag.choose b) b)` reads the entry.
        let mut choose_installs: Vec<(TermId, TermId)> = Vec::new();
        {
            let mut stack = terms.to_vec();
            let mut seen = crate::prelude::FxHashSet::default();
            while let Some(t) = stack.pop() {
                if !seen.insert(t) {
                    continue;
                }
                let Some(kind) = self.terms.get(t).map(|d| d.kind.clone()) else {
                    continue;
                };
                match kind {
                    nixie_core::ast::TermKind::BagChoose(b) => {
                        if model.get(t).is_none()
                            && let Some(v) = self.query_choose_value(b, &model)
                        {
                            choose_installs.push((t, v));
                        }
                    }
                    // A query-only map/filter completes from the domain's
                    // installed value: images/kept-cells folded per cell,
                    // exactly the semantics the reduction asserts for the
                    // counted elements.
                    nixie_core::ast::TermKind::BagMap { .. }
                    | nixie_core::ast::TermKind::BagFilter { .. } => {
                        if model.get(t).is_none()
                            && let Some(v) = self.query_map_filter_value(t, &model)
                        {
                            choose_installs.push((t, v));
                        }
                    }
                    _ => {
                        stack.extend(nixie_core::ast::traversal::get_children(&kind));
                    }
                }
            }
        }
        for (t, v) in choose_installs {
            model.set(t, v);
        }
        let bag_folds: Vec<(TermId, i64)> = terms
            .iter()
            .flat_map(|&t| self.complete_bag_query(t, &model))
            .collect();
        for (t, n) in bag_folds {
            let v = match self.terms.get(t).map(|d| &d.kind) {
                Some(
                    TermKind::BagMember(_, _) | TermKind::BagSubbag(_, _) | TermKind::Eq(_, _),
                ) => {
                    if n > 0 {
                        self.terms.true_id
                    } else {
                        self.terms.false_id
                    }
                }
                _ => self.terms.mk_int(BigInt::from(n)),
            };
            model.set(t, v);
        }

        let mut values = Vec::with_capacity(terms.len());
        for (&term, term_str) in terms.iter().zip(keys) {
            let value_str = if let Some(value) = self.unassigned_const_value(term, &model) {
                // A bare unconstrained constant: report exactly what
                // `(get-model)` reports for it, witnesses included.
                value
            } else if let Some(value) = model.get(term) {
                // The term is directly pinned in the model (e.g. an NL-search
                // select read whose value was installed via the dispatch
                // model). `Model::eval` would instead re-evaluate it
                // structurally (and, for an array read, rebuild the array
                // interpretation), so prefer the direct assignment.
                nixie_core::smtlib::Printer::new(&self.terms).print_term(value)
            } else {
                let completed = if completion.is_empty() {
                    term
                } else {
                    self.terms.substitute(term, &completion)
                };
                // Purification rewrites e.g. `(f 3)` -> `(f v)` (plus `v = 3`)
                // at encode time, so the model holds `f(v)`, not `f(3)`. Resolve
                // through the arg->proxy map first; fall back to the original if
                // the proxy does not yield a concrete value (a non-proxied term)
                // (pr30: purification_preserves_get_value_on_original_application).
                // `Model::eval` substitutes and folds the Boolean structure but
                // leaves arithmetic/bit-vector applications of the substituted
                // constants unreduced (`(+ x 1)` -> `(+ 0 1)`), so run the
                // rewriter over the result to reach an actual value.
                let proxies = self.solver.numarg_proxies.clone();
                let value = if !proxies.is_empty() {
                    let proxied = self.terms.substitute(completed, &proxies);
                    if proxied != completed {
                        let ev = model.eval(proxied, &mut self.terms);
                        let pv = self.terms.simplify(ev);
                        if pv != proxied {
                            pv
                        } else {
                            let ev2 = model.eval(completed, &mut self.terms);
                            self.terms.simplify(ev2)
                        }
                    } else {
                        let ev = model.eval(completed, &mut self.terms);
                        self.terms.simplify(ev)
                    }
                } else {
                    let ev = model.eval(completed, &mut self.terms);
                    self.terms.simplify(ev)
                };
                nixie_core::smtlib::Printer::new(&self.terms).print_term(value)
            };
            values.push(format!("({} {})", term_str, value_str));
        }
        format!("({})", values.join("\n "))
    }

    /// Format the model as SMT-LIB2
    /// Value of a Boolean constant the assertions DEFINE at conjunct level
    /// (`(= b φ)`), evaluated under the model being printed — `Some` only
    /// when `b` has such a definition and it evaluates to a definite truth
    /// value under `solver_model` (numeric entries and already-printed
    /// Booleans).  Used by the default-completion arm in `get_model` so a
    /// defined Boolean is never defaulted to `false` in a model whose own
    /// values make its definition `true` (the QF_NIA/VeryMax invalid-model
    /// class: definition Booleans completed `false`, exact re-evaluation of
    /// the printed model refuted the assertions).
    fn defined_bool_value(
        &self,
        b: nixie_core::TermId,
        solver_model: &crate::solver::Model,
    ) -> Option<String> {
        use nixie_core::TermKind;
        let bool_sort = self.terms.sorts.bool_sort;

        // Conjunct-level `(= b φ)` definitions, collected exactly like the
        // nonlinear search's grounding (descend `and` only).
        let mut defs: crate::prelude::HashMap<nixie_core::TermId, nixie_core::TermId> =
            crate::prelude::HashMap::new();
        let mut stack: Vec<nixie_core::TermId> = self.assertions.clone();
        let mut seen = crate::prelude::HashSet::new();
        while let Some(id) = stack.pop() {
            if !seen.insert(id) {
                continue;
            }
            let Some(n) = self.terms.get(id) else {
                continue;
            };
            match &n.kind {
                TermKind::And(xs) => stack.extend(xs.iter().copied()),
                TermKind::Eq(a, c) => {
                    let bool_var = |t: nixie_core::TermId| {
                        self.terms.get(t).is_some_and(|m| {
                            m.sort == bool_sort && matches!(m.kind, TermKind::Var(_))
                        })
                    };
                    let bool_sorted = |t: nixie_core::TermId| {
                        self.terms.get(t).is_some_and(|m| m.sort == bool_sort)
                    };
                    if bool_var(*a) && bool_sorted(*c) {
                        defs.entry(*a).or_insert(*c);
                    } else if bool_var(*c) && bool_sorted(*a) {
                        defs.entry(*c).or_insert(*a);
                    }
                }
                _ => {}
            }
        }
        let phi = *defs.get(&b)?;

        // Interpretation = the model being printed: numeric entries and
        // Boolean entries (true/false terms) alike.
        let mut interp = nixie_theories::nl_eval::Interpretation::empty();
        for (&t, &v) in solver_model.assignments() {
            let Some(node) = self.terms.get(v) else {
                continue;
            };
            match &node.kind {
                TermKind::IntConst(n) => {
                    interp.pin_num(t, num_rational::BigRational::from(n.clone()));
                }
                TermKind::RealConst(r) => {
                    interp.pin_num(
                        t,
                        num_rational::BigRational::new(
                            num_bigint::BigInt::from(*r.numer()),
                            num_bigint::BigInt::from(*r.denom()),
                        ),
                    );
                }
                TermKind::True => {
                    interp.pin_truth(t, true);
                }
                TermKind::False => {
                    interp.pin_truth(t, false);
                }
                _ => {}
            }
        }
        // Definition chains: resolve in dependency order (a `φ` that names
        // another definition Boolean evaluates once that one is pinned).
        for _ in 0..defs.len().saturating_add(1) {
            let mut changed = false;
            for (&db, &dphi) in &defs {
                if interp.truth_of(db).is_some() {
                    continue;
                }
                if let Some(nixie_theories::nl_eval::Value::Truth(v)) =
                    nixie_theories::nl_eval::evaluate(dphi, &self.terms, &interp)
                {
                    interp.pin_truth(db, v);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        match nixie_theories::nl_eval::evaluate(phi, &self.terms, &interp) {
            Some(nixie_theories::nl_eval::Value::Truth(true)) => Some("true".to_string()),
            Some(nixie_theories::nl_eval::Value::Truth(false)) => Some("false".to_string()),
            _ => None,
        }
    }

    /// Render the model of the last successful `check-sat` in SMT-LIB
    /// `(model ...)` form.
    pub fn format_model(&self) -> String {
        let recfun_lines = self.recfun_model_lines();
        // Declared uninterpreted functions are part of the model too
        // (`#P2b-34`): omitting them left `(get-model)` printing the constants
        // of a `(f x)` goal and nothing about `f`, so the model could be
        // neither replayed nor checked.
        if let Some(error) = self.uncertified_model_error() {
            return error;
        }
        let mut func_lines = self.func_interp_lines();
        let mut division_sorts: Vec<_> =
            self.published.zero_division_sorts.iter().copied().collect();
        division_sorts.sort_unstable_by_key(|s| s.0);
        for sort in division_sorts {
            let (name, sort, value) = if sort == self.terms.sorts.int_sort {
                ("div0", "Int", "0")
            } else {
                ("/0", "Real", "0.0")
            };
            func_lines.push(format!(
                "  (define-fun {name} ((x!0 {sort}) (x!1 {sort})) {sort} {value})"
            ));
        }
        match self.get_model() {
            None => "(error \"No model available\")".to_string(),
            Some(model) if model.is_empty() && recfun_lines.is_empty() && func_lines.is_empty() => {
                "(model)".to_string()
            }
            Some(model) => {
                let mut lines = vec!["(model".to_string()];
                for (name, sort, value) in model {
                    // The name goes through the one symbol encoder
                    // (`#P2b-39`): a declaration the script wrote as `|a b|`
                    // was printed back bare, which is not re-parsable SMT-LIB
                    // — `(define-fun a b () (_ BitVec 1) #b0)` reads as two
                    // symbols — and disagreed with the `(get-value)` key path,
                    // which answers with the term's source spelling.
                    lines.push(format!(
                        "  (define-fun {} () {} {})",
                        nixie_core::smtlib::format_symbol(&name),
                        sort,
                        value
                    ));
                }
                lines.extend(func_lines);
                lines.extend(recfun_lines);
                lines.push(")".to_string());
                lines.join("\n")
            }
        }
    }
}

impl Context {
    /// Fold one bag query term against the model's installed bag values,
    /// installing entries for `bag.card`/`bag.count`/`bag.member` terms
    /// whose operands have values. Recompute even existing readbacks from the
    /// installed bag; anything unresolvable is left alone
    /// (the honest echo).
    fn complete_bag_query(&self, term: TermId, model: &crate::solver::Model) -> Vec<(TermId, i64)> {
        // Explicit stack over the query: nesting is user-shaped. The
        // returned pairs are (term, value-as-integer); `bag.member` is
        // encoded as 1/0 and materialized by the caller.
        let mut out: Vec<(TermId, i64)> = Vec::new();
        let mut stack = vec![term];
        let mut seen = crate::prelude::FxHashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            let Some(kind) = self.terms.get(t).map(|d| d.kind.clone()) else {
                continue;
            };
            use nixie_core::ast::TermKind;
            match kind {
                TermKind::BagCard(b) => {
                    if let Some(cells) = self.installed_bag_cells(b, model) {
                        if let Some(total) = cells
                            .iter()
                            .try_fold(0_i64, |sum, &(_, n)| sum.checked_add(n))
                        {
                            out.push((t, total));
                        }
                    }
                }
                TermKind::BagCount(e, b) => {
                    if let Some(cells) = self.installed_bag_cells(b, model) {
                        // The element may itself have a model entry — a
                        // `bag.choose` valued by the bag pass, or any
                        // element-sorted term the model pins — and the
                        // fold must read *its* value's cell, not the
                        // term's spelling (`(bag.count (bag.choose b) b)` is
                        // the query the choose exists for).
                        let e = model.get(e).unwrap_or(e);
                        let n = self.cell_of(e, &cells);
                        out.push((t, n));
                    }
                }
                TermKind::BagMember(e, b) => {
                    if let Some(cells) = self.installed_bag_cells(b, model) {
                        let e = model.get(e).unwrap_or(e);
                        let n = self.cell_of(e, &cells);
                        out.push((t, if n > 0 { 1 } else { 0 }));
                    }
                }
                // A bag-sorted equality (the `bag.all`/`bag.some` lowering
                // lands here, as does any user equality): both sides' cells
                // resolve from installed/ground values, and the atom folds
                // to its truth — evaluation of verified objects.
                TermKind::Eq(a, b) => {
                    if self.bag_element_sort_of(a).is_some()
                        && self.bag_element_sort_of(b).is_some()
                        && let (Some(ca), Some(cb)) = (
                            self.value_bag_cells(a, model),
                            self.value_bag_cells(b, model),
                        )
                    {
                        let same = ca.len() == cb.len()
                            && ca.iter().all(|&(e, n)| self.cell_of(e, &cb) == n);
                        out.push((t, if same { 1 } else { 0 }));
                    }
                }
                // `bag.subbag a b` from installed values: pointwise ≤ over
                // the union of the cells (a cell absent from `b` counts 0) —
                // evaluation of verified objects, the same contract as the
                // count/member folds beside it. A side with no model entry
                // still folds when it is a closed ground chain (a compound
                // like `(bag 1 2)` is never installed — its value is
                // itself).
                TermKind::BagSubbag(a, b) => {
                    if let (Some(ca), Some(cb)) = (
                        self.value_bag_cells(a, model),
                        self.value_bag_cells(b, model),
                    ) {
                        let holds = ca.iter().all(|&(e, n)| self.cell_of(e, &cb) >= n);
                        out.push((t, if holds { 1 } else { 0 }));
                    }
                }
                _ => {
                    stack.extend(nixie_core::ast::traversal::get_children(&kind));
                }
            }
        }
        out
    }

    /// The `(element, multiplicity)` cells of a bag's installed value, or
    /// `None` when the bag has no (parseable) value entry.
    fn installed_bag_cells(
        &self,
        bag: TermId,
        model: &crate::solver::Model,
    ) -> Option<Vec<(TermId, i64)>> {
        self.bag_cells_of_term(model.get(bag)?, &|t: &TermId| {
            model.get(*t).filter(|&v| v != *t)
        })
    }

    /// A bag's cells for query folding: its installed value when it has
    /// one, else the term itself when it is a closed ground chain (a
    /// compound like `(bag 1 2)` is its own value — nothing installs it).
    fn value_bag_cells(
        &self,
        bag: TermId,
        model: &crate::solver::Model,
    ) -> Option<Vec<(TermId, i64)>> {
        match model.get(bag) {
            Some(v) => self.bag_cells_of_term(v, &|t: &TermId| model.get(*t).filter(|&v| v != *t)),
            None => self.bag_cells_of_term(bag, &|_| None),
        }
    }

    /// Walk a `bag.union_disjoint` chain of `bag.make` cells to its
    /// `bag.empty` base, collecting `(element, multiplicity)` pairs.
    /// `resolve` substitutes nested non-ground elements through the model
    /// (installed values); a walk that meets anything unparseable returns
    /// `None` — the caller echoes honestly.
    fn bag_cells_of_term(
        &self,
        mut cur: TermId,
        resolve: &dyn Fn(&TermId) -> Option<TermId>,
    ) -> Option<Vec<(TermId, i64)>> {
        let mut cells: Vec<(TermId, i64)> = Vec::new();
        loop {
            match self.terms.get(cur).map(|d| d.kind.clone()) {
                Some(nixie_core::ast::TermKind::BagEmpty(_)) => break,
                Some(nixie_core::ast::TermKind::BagUnionDisjoint(a, b)) => {
                    let Some(nixie_core::ast::TermKind::BagMake(e, n)) =
                        self.terms.get(b).map(|d| d.kind.clone())
                    else {
                        return None;
                    };
                    let n = self.int_of(n)?;
                    let e = resolve(&e).unwrap_or(e);
                    cells.push((e, n));
                    cur = a;
                }
                Some(nixie_core::ast::TermKind::BagMake(e, n)) => {
                    let n = self.int_of(n)?;
                    let e = resolve(&e).unwrap_or(e);
                    cells.push((e, n));
                    break;
                }
                _ => return None,
            }
        }
        let mut merged: Vec<(TermId, i64)> = Vec::new();
        for (element, count) in cells {
            if count <= 0 {
                continue;
            }
            if let Some((_, old)) = merged.iter_mut().find(|(e, _)| *e == element) {
                *old = old.checked_add(count)?;
            } else {
                merged.push((element, count));
            }
        }
        Some(merged)
    }

    /// An `IntConst` term's value.
    fn int_of(&self, t: TermId) -> Option<i64> {
        match self.terms.get(t).map(|d| &d.kind) {
            Some(nixie_core::ast::TermKind::IntConst(n)) => num_traits::ToPrimitive::to_i64(n),
            _ => None,
        }
    }

    /// The element sort when `t` is bag-sorted (a sort-check helper for
    /// the equality fold).
    fn bag_element_sort_of(&self, t: TermId) -> Option<nixie_core::sort::SortId> {
        self.terms.get(t).map(|d| d.sort).and_then(|s| {
            self.terms.sorts.get(s).and_then(|sort| match &sort.kind {
                nixie_core::SortKind::Bag(e) => Some(*e),
                _ => None,
            })
        })
    }

    /// The multiplicity of `e` among the cells: by term identity first,
    /// then by equal `IntConst` value (two spellings of one number are
    /// one cell).
    fn cell_of(&self, e: TermId, cells: &[(TermId, i64)]) -> i64 {
        if let Some(&(_, n)) = cells.iter().find(|&&(c, _)| c == e) {
            return n;
        }
        if let Some(n) = self.int_of(e)
            && let Some(&(_, m)) = cells.iter().find(|&&(c, _)| self.int_of(c) == Some(n))
        {
            return m;
        }
        0
    }

    /// A query-only `bag.choose(b)`'s value, from the installed bag value:
    /// the first cell's element — the same deterministic pick the model
    /// pass makes for asserted chooses, so a choose that appears in both
    /// an assertion and a query prints one value. An empty installed bag
    /// leaves the choose unspecified; `0` models it for `Int` element
    /// sorts (any value does), and other sorts echo honestly. No installed
    /// value at all (a declined bag) echoes too.
    /// A query-only `bag.map`/`bag.filter`'s value, from the domain bag's
    /// installed cells: the images (a `define-fun` body inlined and folded
    /// per cell, an application resolved through the model's entry) merged
    /// by value with their multiplicities summed — or the kept cells for a
    /// filter, where the predicate's truth comes from the same resolution.
    /// Anything unresolvable echoes honestly.
    fn query_map_filter_value(
        &mut self,
        term: TermId,
        model: &crate::solver::Model,
    ) -> Option<TermId> {
        let kind = self.terms.get(term)?.kind.clone();
        let (func, bag, ret, is_map) = match kind {
            TermKind::BagMap { func, ret, bag } => (func, bag, Some(ret), true),
            TermKind::BagFilter { pred, bag } => (pred, bag, None, false),
            _ => return None,
        };
        let cells = self.value_bag_cells(bag, model)?;
        let defs = self.solver.bag_fun_defs.clone();
        let mut out_cells: Vec<(TermId, i64)> = Vec::new();
        for &(e, n) in &cells {
            let target = if is_map {
                self.apply_query_fun(func, e, ret?, &defs, model)?
            } else {
                let p = self.apply_query_fun(func, e, self.terms.sorts.bool_sort, &defs, model)?;
                match self.terms.get(p).map(|d| &d.kind) {
                    Some(TermKind::True) => e,
                    Some(TermKind::False) => continue,
                    // An unresolved truth is not a guess to make.
                    _ => return None,
                }
            };
            match out_cells.iter_mut().find(|(v, _)| *v == target) {
                Some((_, m)) => *m = m.checked_add(n)?,
                None => out_cells.push((target, n)),
            }
        }
        let es = if is_map {
            ret?
        } else {
            self.bag_element_sort_of(bag)?
        };
        let bag_sort = self.terms.sorts.bag(es);
        let mut acc = self.terms.mk_bag_empty_at(bag_sort);
        for &(v, n) in &out_cells {
            let n_term = self.terms.mk_int(BigInt::from(n));
            let make = self.terms.mk_bag_make(v, n_term);
            acc = self.terms.mk_bag_union_disjoint(acc, make);
        }
        Some(acc)
    }

    /// The function application `f(x)` for a query-side fold: a defined
    /// function inlines and folds to a value; a declared one resolves
    /// through the model's application entry.
    fn apply_query_fun(
        &mut self,
        func: nixie_core::interner::Spur,
        x: TermId,
        ret: nixie_core::sort::SortId,
        defs: &FxHashMap<nixie_core::interner::Spur, crate::solver::bag_theory::BagFunDef>,
        model: &crate::solver::Model,
    ) -> Option<TermId> {
        if let Some(def) = defs.get(&func)
            && def.params.len() == 1
        {
            let mut subst: FxHashMap<TermId, TermId> = FxHashMap::default();
            subst.insert(def.params[0], x);
            let sub = self.terms.substitute(def.body, &subst);
            return Some(self.terms.simplify(sub));
        }
        let name = self.terms.resolve_str(func).to_string();
        let app = self.terms.mk_apply(&name, [x], ret);
        match model.get(app) {
            Some(v) => Some(v),
            None => {
                // A ground application the model never valued: fold what
                // folds, else echo.
                let folded = self.terms.simplify(app);
                if folded == app { None } else { Some(folded) }
            }
        }
    }

    fn query_choose_value(&mut self, bag: TermId, model: &crate::solver::Model) -> Option<TermId> {
        let cells = self.installed_bag_cells(bag, model)?;
        match cells.first() {
            Some(&(e, _)) => Some(e),
            None => {
                let es = self.terms.get(bag).map(|d| d.sort).and_then(|s| {
                    self.terms.sorts.get(s).and_then(|sort| match &sort.kind {
                        nixie_core::SortKind::Bag(e) => Some(*e),
                        _ => None,
                    })
                })?;
                if es == self.terms.sorts.int_sort {
                    Some(self.terms.mk_int(0))
                } else {
                    None
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ======== default_value semantic pins ========
    //
    // Every expected string below was captured from the pre-conversion
    // recursive implementation, so these tests prove the explicit-stack
    // conversion is behavior-preserving.

    /// Atomic sorts keep their canonical ground defaults.
    #[test]
    fn test_default_value_atomic_pins() {
        let mut ctx = Context::new();
        let bool_sort = ctx.terms.sorts.bool_sort;
        let int_sort = ctx.terms.sorts.int_sort;
        let real_sort = ctx.terms.sorts.real_sort;
        let string_sort = ctx.terms.sorts.string_sort();
        let bv8 = ctx.terms.sorts.bitvec(8);
        let f32_sort = ctx.terms.sorts.float_sort(8, 24);
        assert_eq!(ctx.default_value(bool_sort), "false");
        assert_eq!(ctx.default_value(int_sort), "0");
        assert_eq!(ctx.default_value(real_sort), "0.0");
        assert_eq!(ctx.default_value(string_sort), "\"\"");
        assert_eq!(ctx.default_value(bv8), "#b00000000");
        assert_eq!(ctx.default_value(f32_sort), "(_ +zero 8 24)");

        let spur = ctx.terms.intern_str("Widget");
        let widget = ctx
            .terms
            .sorts
            .intern(nixie_core::sort::SortKind::Uninterpreted(spur));
        assert_eq!(ctx.default_value(widget), "@uc_Widget_0");
    }

    /// Array defaults are const-arrays over the range default, spelled
    /// exactly as before the conversion.
    #[test]
    fn test_default_value_array_pins() {
        let mut ctx = Context::new();
        let int_sort = ctx.terms.sorts.int_sort;
        let a1 = ctx.terms.sorts.array(int_sort, int_sort);
        let a2 = ctx.terms.sorts.array(int_sort, a1);
        assert_eq!(ctx.default_value(a1), "((as const (Array Int Int)) 0)");
        assert_eq!(
            ctx.default_value(a2),
            "((as const (Array Int (Array Int Int))) ((as const (Array Int Int)) 0))"
        );
    }

    /// Well-founded datatype defaults: a compound constructor renders as an
    /// application of the field defaults; a nullary constructor renders as
    /// its bare name.
    #[test]
    fn test_default_value_datatype_pins() {
        let mut ctx = Context::new();
        ctx.execute_script("(declare-datatype Pair ((mk-pair (first Int) (second Int))))")
            .expect("datatype declaration script");
        let pair = ctx.terms.sorts.mk_datatype_sort("Pair");
        assert_eq!(ctx.default_value(pair), "(mk-pair 0 0)");

        let mut ctx2 = Context::new();
        ctx2.execute_script("(declare-datatype Color ((red) (green)))")
            .expect("datatype declaration script");
        let color = ctx2.terms.sorts.mk_datatype_sort("Color");
        assert_eq!(ctx2.default_value(color), "red");
    }

    /// The `(get-model)` infinite-recursion repro: a datatype whose only
    /// constructor closes a cycle through an array field,
    /// `(declare-datatype T ((c (f (Array Int T)))))`.
    ///
    /// The declaration IS accepted (verified against the working tree), and
    /// the sort has no finite ground value, so the default expands the
    /// constructor exactly [`DT_DEFAULT_EXPANSION_LIMIT`] times and bottoms
    /// out in the honest `?` placeholder.  The original code reset its
    /// depth counter to 0 at every re-entry and recursed forever; the
    /// budgeted fix produced exactly this value, and the explicit-stack
    /// conversion must keep producing it.
    #[test]
    fn test_default_value_ill_founded_array_cycle_pins() {
        let mut ctx = Context::new();
        ctx.execute_script("(declare-datatype T ((c (f (Array Int T)))))")
            .expect("self-referential array-field datatype is accepted");
        assert!(ctx.terms.sorts.is_datatype_declared("T"));
        let t_sort = ctx.terms.sorts.mk_datatype_sort("T");

        let mut expected = "?".to_string();
        for _ in 0..DT_DEFAULT_EXPANSION_LIMIT {
            expected = format!("(c ((as const (Array Int T)) {expected}))");
        }
        assert_eq!(ctx.default_value(t_sort), expected);
    }

    /// A *directly* self-referential ill-founded datatype
    /// (`(declare-datatype W ((c (f W))))`) also terminates with the honest
    /// placeholder at the same budget.
    #[test]
    fn test_default_value_ill_founded_direct_cycle_terminates() {
        let mut ctx = Context::new();
        ctx.execute_script("(declare-datatype W ((c (f W))))")
            .expect("self-referential datatype is accepted");
        let w_sort = ctx.terms.sorts.mk_datatype_sort("W");

        let mut expected = "?".to_string();
        for _ in 0..DT_DEFAULT_EXPANSION_LIMIT {
            expected = format!("(c {expected})");
        }
        assert_eq!(ctx.default_value(w_sort), expected);
    }

    /// The full script-level repro from the audit terminates and reports a
    /// honest Unknown instead of a placeholder model.
    #[test]
    fn test_get_model_ill_founded_datatype_script_terminates() {
        let mut ctx = Context::new();
        let out = ctx
            .execute_script(
                "(declare-datatype T ((c (f (Array Int T)))))\n\
                 (declare-const a T)\n\
                 (check-sat)\n\
                 (get-model)",
            )
            .expect("repro script executes");
        assert_eq!(out.first().map(String::as_str), Some("unknown"));
        let model = out.get(1).map(String::as_str).unwrap_or_default();
        assert!(
            model.starts_with("(error"),
            "an incomplete value must not be published: {model}"
        );
    }

    /// Beyond the removed 512-level cap the walk now renders the true
    /// value: the pre-conversion code answered a wrong `?` for every array
    /// sort nested deeper than 512.
    ///
    /// Depth is 2000 rather than the usual 50k-100k deep-nesting depth
    /// because the *output* of `default_value` is inherently quadratic in
    /// array depth – every level embeds its own full sort name – so 100k
    /// levels would be a multi-gigabyte string; output construction, not
    /// the walk, is the bottleneck.  The walk machinery itself is proven at
    /// 12 500 levels on a 128 KiB stack by the `format_sort_name` tests
    /// below, which share the same explicit-stack shape with linear output
    /// and pin the same ~10 bytes-per-frame threshold a 1 MiB / 100k pair
    /// would.  This test's own stack stays at 1 MiB: its depth is 2000, well
    /// under the scaling threshold, and nothing here is quadratic in stack.
    #[test]
    fn test_default_value_deep_array_chain_beyond_old_cap() {
        const DEPTH: usize = 2000;
        // STACK-1MIB: deliberately 1 MiB, not swept to 128 KiB — depth is
        // 2000 (sub-10,000), well under the scaling threshold and nothing
        // here is quadratic in stack.
        let handle = std::thread::Builder::new()
            .stack_size(1 << 20)
            .spawn(|| {
                let mut ctx = Context::new();
                let int_sort = ctx.terms.sorts.int_sort;
                let mut sort = int_sort;
                for _ in 0..DEPTH {
                    sort = ctx.terms.sorts.array(int_sort, sort);
                }
                let value = ctx.default_value(sort);
                assert!(
                    !value.contains('?'),
                    "a finite array sort must never render the `?` placeholder"
                );
                assert_eq!(value.matches("((as const ").count(), DEPTH);
                assert!(value.starts_with("((as const (Array Int "));
                // The innermost value is the Int default `0` wrapped by one
                // closing paren per level.
                let expected_suffix = format!(" 0{}", ")".repeat(DEPTH));
                assert!(
                    value.ends_with(&expected_suffix),
                    "value must bottom out in the Int default"
                );
            })
            .expect("spawn deep default-value thread");
        handle.join().expect("deep default-value must not overflow");
    }

    // ======== format_sort_name ========

    /// Leaf and compound sort names, pinned against the pre-conversion
    /// recursive renderer.
    #[test]
    fn test_format_sort_name_pins() {
        let mut ctx = Context::new();
        let int_sort = ctx.terms.sorts.int_sort;
        let bool_sort = ctx.terms.sorts.bool_sort;
        let bv8 = ctx.terms.sorts.bitvec(8);
        let f32_sort = ctx.terms.sorts.float_sort(8, 24);
        let arr = ctx.terms.sorts.array(int_sort, bv8);
        let nested = ctx.terms.sorts.array(arr, bool_sort);
        assert_eq!(ctx.format_sort_name(int_sort), "Int");
        assert_eq!(ctx.format_sort_name(bv8), "(_ BitVec 8)");
        assert_eq!(ctx.format_sort_name(f32_sort), "(_ FloatingPoint 8 24)");
        assert_eq!(ctx.format_sort_name(arr), "(Array Int (_ BitVec 8))");
        assert_eq!(
            ctx.format_sort_name(nested),
            "(Array (Array Int (_ BitVec 8)) Bool)"
        );

        ctx.execute_script("(declare-datatype Pair ((mk-pair (first Int) (second Int))))")
            .expect("datatype declaration script");
        let pair = ctx.terms.sorts.mk_datatype_sort("Pair");
        assert_eq!(ctx.format_sort_name(pair), "Pair");
    }

    /// Deep-nesting regression: a 12 500-level range-nested array sort (built
    /// through the builder API in O(1) stack) renders on a 128 KiB thread
    /// stack.  The pre-conversion renderer recursed natively per level, so
    /// returning at all is the proof; the exact length pins correctness
    /// (`len("(Array Int ") + len(")") = 12` added bytes per level).
    #[test]
    fn test_format_sort_name_deep_range_chain_small_stack() {
        // Stack and depth scale together (1 MiB/100k -> 128 KiB/12.5k): the
        // ~10 B-per-frame threshold is the pin, so never raise one alone.
        const DEPTH: usize = 12_500;
        let handle = std::thread::Builder::new()
            .stack_size(1 << 17)
            .spawn(|| {
                let mut ctx = Context::new();
                let int_sort = ctx.terms.sorts.int_sort;
                let mut sort = int_sort;
                for _ in 0..DEPTH {
                    sort = ctx.terms.sorts.array(int_sort, sort);
                }
                let name = ctx.format_sort_name(sort);
                assert_eq!(name.len(), 12 * DEPTH + 3);
                assert!(name.starts_with("(Array Int (Array Int "));
                // The innermost sort is `Int`, closed by one paren per level.
                let suffix = format!("Int{}", ")".repeat(DEPTH));
                assert!(name.ends_with(&suffix));
            })
            .expect("spawn deep-format thread");
        handle.join().expect("deep-format thread must not overflow");
    }

    /// Same regression with the nesting on the domain side, which exercises
    /// the domain-first descent frames.
    #[test]
    fn test_format_sort_name_deep_domain_chain_small_stack() {
        // Stack and depth scale together (1 MiB/100k -> 128 KiB/12.5k): the
        // ~10 B-per-frame threshold is the pin, so never raise one alone.
        const DEPTH: usize = 12_500;
        let handle = std::thread::Builder::new()
            .stack_size(1 << 17)
            .spawn(|| {
                let mut ctx = Context::new();
                let int_sort = ctx.terms.sorts.int_sort;
                let mut sort = int_sort;
                for _ in 0..DEPTH {
                    sort = ctx.terms.sorts.array(sort, int_sort);
                }
                let name = ctx.format_sort_name(sort);
                assert_eq!(name.len(), 12 * DEPTH + 3);
                assert!(name.starts_with("(Array (Array "));
                assert!(name.ends_with(" Int) Int)"));
            })
            .expect("spawn deep-format thread");
        handle.join().expect("deep-format thread must not overflow");
    }

    /// Shared-DAG regression for the memo: a doubling array sort
    /// (`s[i+1] = (Array s[i] s[i])`) is rendered once per *distinct* sort,
    /// not once per path.
    ///
    /// Depth is 20 rather than the usual 50-60 doubling levels because the
    /// *output* is inherently exponential in doubling depth – SMT-LIB sort
    /// syntax has no sharing, so the rendered text of level `n` has length
    /// `12 * 2^n - 9` and 60 levels would be an exabyte-scale string no
    /// algorithm could materialize.  At depth 20 the test pins the exact
    /// (12.6 MB) length and must complete quickly.
    #[test]
    fn test_format_sort_name_shared_doubling_dag() {
        const LEVELS: u32 = 20;
        let mut ctx = Context::new();
        let int_sort = ctx.terms.sorts.int_sort;
        let mut sort = int_sort;
        for _ in 0..LEVELS {
            sort = ctx.terms.sorts.array(sort, sort);
        }
        let name = ctx.format_sort_name(sort);
        // len(n) = 2 * len(n-1) + len("(Array ") + len(" ") + len(")")
        //        = 2 * len(n-1) + 9, len(0) = 3  =>  len(n) = 12 * 2^n - 9.
        let expected_len = 12usize * (1usize << LEVELS) - 9;
        assert_eq!(name.len(), expected_len);
        assert!(name.starts_with("(Array (Array "));
    }

    // ======== get_model through the public surface ========

    /// An unconstrained array constant round-trips its sort and default
    /// value through `(get-model)` exactly as before the conversion.
    #[test]
    fn test_get_model_array_const_roundtrip() {
        let mut ctx = Context::new();
        let out = ctx
            .execute_script("(declare-const a (Array Int Int))\n(check-sat)\n(get-model)")
            .expect("valid script executes");
        let model = out.last().map(String::as_str).unwrap_or_default();
        assert!(
            model.contains("(define-fun a () (Array Int Int) "),
            "model must render the array sort name: {model}"
        );
    }

    // ======== parameter / parametric sort names ========

    /// A sort *parameter* renders as its declared name. It used to render as
    /// the literal string "Unknown", so every parameter of every definition
    /// printed identically.
    #[test]
    fn test_format_sort_name_parameter_uses_its_real_name() {
        let mut ctx = Context::new();
        let t_param = ctx.terms.sorts.mk_sort_parameter("T");
        let u_param = ctx.terms.sorts.mk_sort_parameter("U");

        assert_eq!(ctx.format_sort_name(t_param), "T");
        assert_eq!(ctx.format_sort_name(u_param), "U");
        assert_ne!(
            ctx.format_sort_name(t_param),
            ctx.format_sort_name(u_param),
            "two distinct parameters must not collapse onto one printed name"
        );
    }

    /// A parametric application renders as `(Name arg...)`, exactly as
    /// `SmtLibPrinter::write_sort` spells it, with the head name resolved
    /// through the *sort* manager's interner.
    #[test]
    fn test_format_sort_name_parametric_instance_uses_its_real_name() {
        let mut ctx = Context::new();
        let int_sort = ctx.terms.sorts.int_sort;
        let bool_sort = ctx.terms.sorts.bool_sort;
        ctx.terms.sorts.declare_parametric_sort("List", 1);
        ctx.terms.sorts.declare_parametric_sort("Pair", 2);

        let list_int = ctx
            .terms
            .sorts
            .instantiate_parametric_sort("List", &[int_sort])
            .expect("List has arity 1");
        let pair = ctx
            .terms
            .sorts
            .instantiate_parametric_sort("Pair", &[list_int, bool_sort])
            .expect("Pair has arity 2");

        assert_eq!(ctx.format_sort_name(list_int), "(List Int)");
        assert_eq!(ctx.format_sort_name(pair), "(Pair (List Int) Bool)");
    }

    /// The parametric arguments are walked on the same explicit heap stack as
    /// array domains, so a deeply nested application does not touch the
    /// native stack: `(List (List ... Int ...))`.
    #[test]
    fn test_format_sort_name_deeply_nested_parametric() {
        // Stack and depth scale together (1 MiB/20k -> 128 KiB/2.5k): the
        // ~52 B-per-frame threshold is the pin, so never raise one alone.
        const DEPTH: usize = 2_500;

        let handle = std::thread::Builder::new()
            .stack_size(1 << 17)
            .spawn(|| {
                let mut ctx = Context::new();
                let int_sort = ctx.terms.sorts.int_sort;
                ctx.terms.sorts.declare_parametric_sort("List", 1);
                let mut sort = int_sort;
                for _ in 0..DEPTH {
                    sort = ctx
                        .terms
                        .sorts
                        .instantiate_parametric_sort("List", &[sort])
                        .expect("List has arity 1");
                }
                let name = ctx.format_sort_name(sort);
                // "(List " * DEPTH + "Int" + ")" * DEPTH
                assert_eq!(name.len(), 7 * DEPTH + 3);
                assert!(name.starts_with("(List (List "));
                // The innermost `Int` is followed by one closing paren per
                // level: `(List (List ... (List Int)...))`.
                assert!(name.ends_with(&format!(" Int{}", ")".repeat(DEPTH))));
            })
            .expect("spawn deep-parametric thread");
        handle
            .join()
            .expect("deep-parametric thread must not overflow");
    }

    /// End to end through `get_model`: constants declared at a parametric
    /// instance and at a sort parameter report their real sort names.  Both
    /// used to report the single name "Unknown", so a model could not even
    /// tell the two constants' sorts apart.
    ///
    /// Declared through the `Context` API rather than a script because the
    /// SMT-LIB front end does not yet accept an applied user sort
    /// constructor in sort position (`parse_sort` handles only `Array`
    /// there); the model formatter is what is under test here either way.
    #[test]
    fn test_get_model_parameter_and_parametric_sorts_show_real_names() {
        let mut ctx = Context::new();
        let int_sort = ctx.terms.sorts.int_sort;
        ctx.terms.sorts.declare_parametric_sort("List", 1);
        let list_int = ctx
            .terms
            .sorts
            .instantiate_parametric_sort("List", &[int_sort])
            .expect("List has arity 1");
        let t_param = ctx.terms.sorts.mk_sort_parameter("T");

        ctx.declare_const("xs", list_int);
        ctx.declare_const("t", t_param);
        assert_eq!(ctx.check_sat(), SolverResult::Sat);

        let model = ctx.get_model().expect("sat check produces a model");
        let sorts: crate::prelude::HashMap<&str, &str> = model
            .iter()
            .map(|(name, sort, _)| (name.as_str(), sort.as_str()))
            .collect();
        assert_eq!(sorts.get("xs").copied(), Some("(List Int)"));
        assert_eq!(sorts.get("t").copied(), Some("T"));
    }
}

// Experiment-only per-process selector; absent from production.
fn publication_probe(name: &str) -> bool {
    static MODE: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    MODE.get_or_init(|| std::env::var("NIXIE_PUBLICATION_PROBE").unwrap_or_default())
        .split(',')
        .any(|selected| selected == name)
}
