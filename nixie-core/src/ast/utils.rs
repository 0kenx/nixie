//! Utility functions for term manipulation and analysis
//!
//! Every public walker here used to recurse once per term-nesting level with
//! no depth guard, so a term nested deep enough -- constructible directly
//! through `TermManager`'s builder API, not just via the SMT-LIB parser and
//! its `MAX_PARSE_DEPTH` -- crashed the process with a native stack overflow
//! instead of returning a value. None of these functions has an error
//! channel (they return a plain `u64`/`bool`/`usize`/`TermId`), so a depth
//! *cap* could only silently return a wrong answer -- exactly the "silent
//! fallthrough" anti-pattern this project spent the 0.3.1 release
//! eliminating elsewhere. Every walker below is instead driven by an
//! explicit heap-allocated stack, mirroring the precedent set by
//! `smtlib/parser/terms.rs` in this same release.
//!
//! This module is split into files along the shape of each walk (so that no
//! single file approaches the workspace's 2000-line ceiling):
//!
//! * `hash` -- `structural_hash`, which feeds every subterm into one
//!   shared, order-sensitive hasher.
//! * `equality` -- `structurally_equal` / `alpha_equivalent`, which walk
//!   two terms in lockstep via a stack of pending pairs.
//! * `stats` -- `is_ground`, `term_complexity`, `compute_statistics` and
//!   the predicate/search helpers that were already iterative.
//! * `flatten` -- `flatten_associative`, which rebuilds bottom-up through
//!   `&mut TermManager`.
//! * `tests` -- the pre-existing behavioral suite plus the
//!   depth/stack-overflow regression tests added for this conversion.
//!
//! Every name below is re-exported at this module's own path, so
//! `ast::utils::structural_hash` (and friends) keep working exactly as
//! before the split.

mod equality;
mod flatten;
mod hash;
mod stats;
#[cfg(test)]
mod tests;

pub use equality::{alpha_equivalent, structurally_equal};
pub use flatten::flatten_associative;
pub use hash::structural_hash;
pub use stats::{
    TermStatistics, collect_unique_subterms, compute_statistics, count_operations, find_terms,
    is_ground, max_term_id, term_complexity,
};
