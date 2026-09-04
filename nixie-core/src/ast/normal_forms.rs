//! Normal form conversions for boolean formulas
//!
//! This module provides utilities for converting boolean formulas to various
//! normal forms such as CNF (Conjunctive Normal Form), DNF (Disjunctive Normal Form),
//! and NNF (Negation Normal Form). Also includes Skolemization for quantifier elimination.
//!
//! Split into submodules so each stays well under the workspace's line-count
//! ceiling (mirrors the precedent set by `ast/manager/query.rs` ->
//! `query/{size_depth,simplify,substitute,tests}.rs`):
//!
//! * `cnf` (private) -- [`to_cnf`], `is_cnf`, `extract_cnf_clauses`.
//! * `cnf_tseitin` (private) -- [`to_cnf_tseitin`], the equisatisfiable,
//!   linear-size definitional counterpart to [`to_cnf`] (see below).
//! * `dnf` (private) -- [`to_dnf`], `is_dnf`.
//! * `nnf` (private) -- [`simplify_boolean`], [`to_nnf`], `is_nnf`.
//! * `skolem` (private) -- [`skolemize`], [`skolemize_with_counter`],
//!   [`eliminate_universal_quantifiers`].
//!
//! # Iterative conversion
//!
//! Every pass here used to recurse natively once per level of input-term
//! nesting, with no depth guard at all: a pathologically deep (but validly
//! constructed, e.g. built directly via `mk_*`/`intern` rather than parsed)
//! term could overflow the call stack and abort the process. All four public
//! entry points (`to_cnf`, `to_dnf`, `to_nnf`, `skolemize`), plus
//! `simplify_boolean`, `is_nnf` and `eliminate_universal_quantifiers`, are
//! converted to use an explicit heap stack instead, mirroring the pattern
//! established by `ast::manager::query`'s `substitute`/`simplify`/
//! `term_size`/`term_depth` conversions: a `Vec`-backed work list replaces
//! the native call stack and can grow arbitrarily (bounded by memory, not the
//! fixed native stack).
//!
//! `is_cnf`/`is_clause`/`is_literal`, `is_dnf`/`is_term_conjunction`
//! (sharing `is_literal`), and `extract_cnf_clauses`/`extract_clause_literals`
//! are *not* converted: each of those call chains switches to a strictly
//! shallower function at every level (`is_cnf` only ever calls `is_clause`,
//! which only ever calls `is_literal`, which recurses no further at all), so
//! their native call depth is bounded by a small constant (3, 3, and 2
//! frames respectively) regardless of the input term's own depth. That is
//! not "input-depth-driven recursion" in the sense this conversion targets.
//!
//! # Exponential blowup (naive CNF/DNF distribution)
//!
//! `to_cnf`/`to_dnf` distribute `Or` over `And` (respectively `And` over
//! `Or`) directly, with no Tseitin-style fresh-variable naming to keep the
//! result polynomial. This is a textbook exponential-blowup shape: a formula
//! built as a chain of nested `Iff`/`Xor` (or, here, deeply nested
//! `And`-of-`Or` alternation) can produce a CNF/DNF result whose *size* is
//! exponential in the input's size, independent of any recursion-depth
//! concern. That is an inherent property of naive distribution-based
//! CNF/DNF conversion, not a regression introduced by this conversion pass.
//! It is inherent to the *contract*, not to the implementation: [`to_cnf`]
//! returns a formula logically **equivalent** to its input over the input's
//! own variables, and an equivalent CNF genuinely is exponentially larger
//! for these inputs -- no implementation of that contract can avoid it.
//!
//! What can avoid it is a weaker contract, and that is what
//! [`to_cnf_tseitin`] provides: an **equisatisfiable** CNF of linear size,
//! naming each compound subformula with a fresh variable instead of
//! distributing over it. Neither supersedes the other -- see
//! [`to_cnf_tseitin`]'s "Which one to use". [`to_cnf`]'s own contract is
//! unchanged by its arrival.
//!
//! `nixie-proof`'s `cnf.rs` takes the definitional approach at the
//! clause-database level instead, memoizing each subformula's introduced
//! variable in its own `tseitin_vars` map (actively read on every
//! conversion, not just written) to keep the result polynomial; it works on
//! its own `Formula`/`Var` types rather than on `TermManager` terms, so
//! `cnf_tseitin` here implements the transformation locally against
//! `TermManager` rather than depending across crates.
//! What this pass *does* fix, as a direct byproduct of converting to an
//! explicit work stack: the previous `distribute_or_over_and`/
//! `distribute_and_over_or` took a `cache` parameter that was never read
//! (named `_cache`, always passed through unused) -- i.e. zero memoization
//! of the pairwise distribution itself, so the same `(lhs, rhs)` pair
//! reached via two different callers recomputed the distribution from
//! scratch. That cache is now real (see the private `cnf::distribute_or_over_and`
//! function's doc comment), which avoids *redundant* recomputation of identical
//! sub-distributions; it does not, and cannot, bound the worst-case *output
//! size* of naive distribution, which remains exponential in the
//! adversarial case.
//!
//! # Capture avoidance
//!
//! Skolemization and universal-quantifier elimination both call
//! `TermManager::substitute` to ground out bound variables. That routine is
//! itself capture-avoiding and (as of this same conversion session) uses an
//! explicit heap stack rather than native recursion -- see
//! `ast::manager::query::substitute`'s module doc comment. Neither function
//! here needed any change to *how* it uses `substitute`; they already
//! delegate the substitution itself rather than reimplementing it, so they
//! inherit both properties for free.

use super::{TermId, TermKind, TermManager};
#[allow(unused_imports)]
use crate::prelude::*;
use smallvec::SmallVec;

mod cnf;
mod cnf_tseitin;
mod dnf;
mod nnf;
mod skolem;

#[cfg(test)]
mod tests;

pub use cnf::{extract_cnf_clauses, is_cnf, to_cnf};
pub use cnf_tseitin::to_cnf_tseitin;
pub use dnf::{is_dnf, to_dnf};
pub use nnf::{is_nnf, simplify_boolean, to_nnf};
pub use skolem::{eliminate_universal_quantifiers, skolemize, skolemize_with_counter};

/// Check if a term is a literal (variable or negated variable).
///
/// Shared by [`cnf`]'s `is_clause` and [`dnf`]'s `is_term_conjunction` (both
/// private to their own submodule), which is why this lives in the parent
/// module rather than either -- private items defined here are visible to
/// both child modules without needing any `pub(...)` qualifier, since Rust
/// privacy always lets a descendant module see its ancestors' private
/// items.
fn is_literal(term_id: TermId, manager: &TermManager) -> bool {
    match manager.get(term_id).map(|t| &t.kind) {
        Some(TermKind::Var(_)) | Some(TermKind::True) | Some(TermKind::False) => true,

        Some(TermKind::Not(arg)) => {
            matches!(manager.get(*arg).map(|t| &t.kind), Some(TermKind::Var(_)))
        }

        _ => false,
    }
}

/// One pending step of the iterative pairwise-distribution walk shared by
/// the private `cnf::distribute_or_over_and` and `dnf::distribute_and_over_or`
/// functions -- see either's doc comment. Generic over which combinators `Expand`'s
/// terminal case and `Combine` apply (CNF distributes `Or` over `And` and
/// combines via `mk_and`/`mk_or`; DNF is the exact mirror image), so this
/// shape itself carries no CNF/DNF-specific meaning and is shared here
/// rather than duplicated (this crate has been bitten before by two
/// separately-maintained copies of the same shape drifting apart -- see
/// `ast::traversal::map_terms`'s doc comment for its retired
/// `transform_children`).
enum DistributeStep {
    Expand(TermId, TermId),
    Combine(TermId, TermId, SmallVec<[(TermId, TermId); 4]>),
}
