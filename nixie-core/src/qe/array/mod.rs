//! Array Quantifier Elimination.

#[allow(unused_imports)]
use crate::prelude::*;

pub mod index_abstraction;
pub mod plugin;
pub mod quantifier_elim;

pub use plugin::{ArrayConstraint, ArrayId, ArrayQeConfig, ArrayQePlugin, ArrayQeStats, IndexId};

// `quantifier_elim`'s types are intentionally NOT re-exported here.
//
// That module (see its module doc comment) operates on a placeholder
// `TermId = usize` with no connection to a real `TermManager`: it cannot
// actually analyze formula structure, substitute terms, or mint fresh
// constants, so almost every non-trivial code path honestly returns `Err`
// rather than a real result. Re-exporting `ArrayQuantifierEliminator`,
// `ArrayProperty`, `ArrayTerm`, `IndexConstraint`, `IndexSet` and the
// `ArrayQeConfig`/`ArrayQeStats` aliases at this module's public surface
// would present a design scratchpad as first-class, usable API next to
// `plugin`'s real implementation above.
//
// The functioning, `TermManager`-backed array quantifier eliminator is
// `nixie_theories::array::quantifier_elim::ArrayQuantifierEliminator`; use
// that instead. `quantifier_elim` remains a `pub mod` here (reachable via
// its full path) only for callers that have already read its module doc
// and accepted those limitations.
