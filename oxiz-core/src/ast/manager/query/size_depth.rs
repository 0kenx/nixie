//! Iterative term-size and term-depth queries.
//!
//! Split out of `ast/manager/query.rs`. [`TermManager::term_size`] and
//! [`TermManager::term_depth`] walk a term's *entire* structure, recursing
//! once per level of nesting. The prior implementation did this via native
//! recursion with no depth guard at all: a pathologically deep (but validly
//! constructed, e.g. built via a long chain of `mk_not`/`mk_add` calls) term
//! could overflow the call stack and abort the process. Both functions
//! return a plain `usize` with no error channel, so a depth cap (the way
//! `substitute`/`simplify` used to have one -- see `super::substitute`'s
//! module doc comment) could only ever produce a silently *wrong* number
//! past the cap, which would be worse than the crash it replaces. The fix
//! here is instead to walk with an explicit, heap-allocated stack: a `Vec`
//! can grow arbitrarily (bounded only by available memory, not the fixed
//! native stack), so there is no depth at which this crashes or silently
//! misbehaves.
//!
//! Reference: Z3's `ast.cpp` computes analogous term metrics.

use super::TermManager;
use crate::ast::term::{TermId, TermKind};
use crate::ast::traversal::get_children;
#[allow(unused_imports)]
use crate::prelude::*;

impl TermManager {
    // ===== Term Analysis =====

    /// Compute the size (number of nodes) of a term.
    #[must_use]
    pub fn term_size(&self, id: TermId) -> usize {
        self.term_size_cached(id, &mut FxHashMap::default())
    }

    /// Compute the size with memoization, using an explicit heap stack
    /// instead of native recursion (see the module doc comment).
    ///
    /// Two-phase iterative post-order: a frame is first pushed *unexpanded*
    /// (`expanded = false`); popping an unexpanded frame pushes it back
    /// *expanded* followed by whichever of its children are not already
    /// cached (so, LIFO, the children are fully processed -- including
    /// their own nested children -- before the parent's expanded frame is
    /// popped). Popping an expanded frame therefore finds every child
    /// already in `cache` and combines them.
    ///
    /// `get_children` (see `ast/traversal.rs`) is used uniformly for every
    /// `TermKind` here. That is faithful to what the prior recursive
    /// implementation's explicit per-variant arms summed over in *every*
    /// case, including the ones that don't just mean "every operand":
    /// `Forall`/`Exists` count only their body (patterns excluded, and
    /// `get_children` likewise excludes patterns), and `Let` counts every
    /// binding's value plus the body (`get_children` returns exactly that
    /// set, in that order). A missing term (`self.get` returning `None`)
    /// is handled outside the `get_children` uniformity, matching the old
    /// `None => 1` arm exactly.
    fn term_size_cached(&self, id: TermId, cache: &mut FxHashMap<TermId, usize>) -> usize {
        if let Some(&size) = cache.get(&id) {
            return size;
        }

        let mut stack: Vec<(TermId, bool)> = vec![(id, false)];
        while let Some((current, expanded)) = stack.pop() {
            // Already resolved, e.g. reached again via a second parent that
            // shares this subterm (structural sharing) -- nothing to redo.
            if cache.contains_key(&current) {
                continue;
            }

            if expanded {
                let size = match self.get(current).map(|t| &t.kind) {
                    None => 1,
                    Some(kind) => {
                        // Every child is guaranteed to already be in `cache`
                        // here: it was pushed (and therefore fully resolved,
                        // by LIFO ordering) below this very frame. `unwrap_or`
                        // is a defensive fallback for that structurally
                        // unreachable case, not a real "missing data" path.
                        1 + get_children(kind)
                            .iter()
                            .map(|child| cache.get(child).copied().unwrap_or(0))
                            .sum::<usize>()
                    }
                };
                cache.insert(current, size);
            } else {
                stack.push((current, true));
                if let Some(term) = self.get(current) {
                    for &child in &get_children(&term.kind) {
                        if !cache.contains_key(&child) {
                            stack.push((child, false));
                        }
                    }
                }
            }
        }

        cache.get(&id).copied().unwrap_or(0)
    }

    /// Compute the depth of a term.
    #[must_use]
    pub fn term_depth(&self, id: TermId) -> usize {
        self.term_depth_cached(id, &mut FxHashMap::default())
    }

    /// Compute the depth with memoization, using an explicit heap stack
    /// (see [`TermManager::term_size_cached`] for the traversal shape,
    /// which this mirrors exactly).
    ///
    /// Unlike size, depth is *not* uniform over every zero-child kind: the
    /// prior recursive implementation special-cased the "core" leaves
    /// (`True`/`False`/`IntConst`/`RealConst`/`BitVecConst`/`StringLit`/
    /// `Var`, and a missing term) as depth `0`, while every *other*
    /// zero-child kind -- the FP literals `FpLit`/`FpPlusInfinity`/
    /// `FpMinusInfinity`/`FpPlusZero`/`FpMinusZero`/`FpNaN` -- fell through
    /// its catch-all arm to `1 + max(children).unwrap_or(0)`, i.e. depth
    /// `1` (an empty `max` over zero children still adds the node's own
    /// level). That distinction is preserved here verbatim, so memoized
    /// results are bit-for-bit identical to what the old code returned for
    /// every term it could handle.
    fn term_depth_cached(&self, id: TermId, cache: &mut FxHashMap<TermId, usize>) -> usize {
        if let Some(&depth) = cache.get(&id) {
            return depth;
        }

        let mut stack: Vec<(TermId, bool)> = vec![(id, false)];
        while let Some((current, expanded)) = stack.pop() {
            if cache.contains_key(&current) {
                continue;
            }

            if expanded {
                let depth = match self.get(current).map(|t| &t.kind) {
                    None => 0,
                    Some(
                        TermKind::True
                        | TermKind::False
                        | TermKind::IntConst(_)
                        | TermKind::RealConst(_)
                        | TermKind::BitVecConst { .. }
                        | TermKind::StringLit(_)
                        | TermKind::Var(_),
                    ) => 0,
                    Some(kind) => {
                        1 + get_children(kind)
                            .iter()
                            .map(|child| cache.get(child).copied().unwrap_or(0))
                            .max()
                            .unwrap_or(0)
                    }
                };
                cache.insert(current, depth);
            } else {
                stack.push((current, true));
                if let Some(term) = self.get(current) {
                    for &child in &get_children(&term.kind) {
                        if !cache.contains_key(&child) {
                            stack.push((child, false));
                        }
                    }
                }
            }
        }

        cache.get(&id).copied().unwrap_or(0)
    }
}
