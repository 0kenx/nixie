//! Structural and alpha equivalence between two terms, walked in lockstep.
//!
//! Both [`structurally_equal`] and [`alpha_equivalent`] compare a *pair* of
//! terms recursively; the iterative version therefore needs a stack of
//! pending *pairs* rather than a stack of single term ids. Unlike
//! [`super::hash::structural_hash`], neither function accumulates anything
//! order-sensitive -- each is a boolean conjunction ("this pair matches, AND
//! all of its children pairs match") -- so the pending pairs can be pushed in
//! any order; a mismatch found anywhere aborts the whole comparison
//! immediately (`return false`), matching the original's `&&`/`.all()`
//! short-circuit chains exactly.
//!
//! This module is split into two files along the one real difference between
//! the two functions (whether bound variables can be renamed) plus a small
//! file of helpers shared by both:
//!
//! * `structural` -- [`structurally_equal`]: no renaming permitted anywhere,
//!   so two `Var`s must be the literal same name and a binder's variable list
//!   must match exactly.
//! * `alpha` -- [`alpha_equivalent`]: the same walk, but `Var` consults an
//!   environment of bound-variable correspondences that the four binder
//!   kinds populate as they are entered. See that file's module docs for the
//!   environment's design and, especially, why the `visited` cycle-guard
//!   below needed to change once results can depend on it.
//! * `shape` -- payload-extraction helpers used by both, so that e.g. "the
//!   set of `TermKind`s that are exactly two bare `TermId`s and nothing else"
//!   is spelled out once rather than twice.
//!
//! ## Both functions are now exhaustive over `TermKind`, with no catch-all
//!
//! Before this fix, both functions had arms only for a subset of `TermKind`
//! (`structurally_equal` was missing `Forall`/`Exists`/`Let`, every
//! floating-point operator, every `Dt*` datatype kind, *and* every `Str*`
//! string operator; `alpha_equivalent` had the binders but was missing the
//! same floating-point/datatype/string kinds) and fell back to a bare
//! `_ => false` for anything else -- so e.g. two *identical* quantified or
//! floating-point terms compared unequal, indistinguishable from a genuine
//! mismatch. Both match arms now dispatch on `lt.kind` alone with **no
//! wildcard anywhere in the outer match**, mirroring the discipline
//! `ast/manager/query/substitute.rs::rebuild_substituted` uses for the same
//! reason: adding a new `TermKind` variant in the future is a compile error
//! at this match, not a silent `false`. There is no longer any
//! "genuinely-uncomparable" kind left uncovered -- every one of `TermKind`'s
//! variants is either compared by direct field equality (the constant/leaf
//! kinds) or by recursing into its `TermId` children (everything else), so
//! neither function needs an explicit "cannot compare" case.
//!
//! ## Why `patterns` (quantifier trigger hints) are not compared
//!
//! `Forall`/`Exists` carry a `patterns: SmallVec<[SmallVec<[TermId; 2]>; 2]>`
//! field -- e-matching trigger hints that guide quantifier instantiation.
//! Neither function compares it, and this is a deliberate, considered choice
//! rather than an oversight: patterns are proof-search hints, not part of a
//! quantified formula's logical content -- SMT-LIB gives `(forall ((x Int))
//! (! (> x 0) :pattern ((f x))))` and the same formula without the `:pattern`
//! annotation identical semantics. Treating them as structurally significant
//! would mean two formulas that mean exactly the same thing, and every
//! caller of `structurally_equal` that wants "same logical content" (e.g.
//! deduplication) would have to know to strip patterns first. This also
//! matches the *existing*, separately-established precedent of this exact
//! module: [`super::hash::structural_hash`] already ignores `patterns`
//! (inherited unchanged from the pre-iterative-conversion original -- see
//! that file's `Forall`/`Exists` arm), so leaving them out here keeps all
//! three sibling functions in this module consistent about what counts as a
//! term's "structure". The tradeoff is genuine, though: two terms differing
//! *only* in their triggers are logically equivalent but not *operationally*
//! identical (they can e-match differently and thus solve differently) --
//! see `ast/traversal.rs::get_children`'s doc comment for where this same
//! question shows up again for generic tree-walking, and why it matters more
//! there.
//!
//! ## Why the `visited`/cycle-guard shortcut is still sound for `structurally_equal`
//!
//! The original recursive function marks a pair `(lhs, rhs)` as `visited`
//! *before* comparing it, and immediately returns `true` if a pair is ever
//! seen again. That looks unsound in isolation (it does not remember what
//! the first visit actually concluded), but it is safe *because* every
//! combinator in this function is `&&` or `.all()`/`zip().all()` -- there is
//! no `||` anywhere. The moment any sub-comparison is found unequal, `false`
//! propagates immediately through every enclosing frame and the whole
//! top-level call returns, without visiting anything else. So a pair can only
//! ever be *revisited* if the first visit's entire subtree already finished
//! and concluded "equal" (otherwise the function would already have
//! returned). Treating a revisit as "equal" is therefore always correct, not
//! an approximation. A LIFO stack preserves the same property: pushing a
//! node's children and draining them via `pop()` still fully exhausts one
//! branch (and everything it spawns) before an earlier, still-pending sibling
//! is popped, so the "revisit implies already-equal" invariant holds
//! regardless of the order children are pushed in. Crucially, this argument
//! never depends on anything beyond the two term ids themselves -- there is
//! no environment threading through `structurally_equal` for the answer to
//! depend on -- which is exactly the property that stops holding for
//! `alpha_equivalent`; see `alpha.rs`'s module docs for what changed there.

mod alpha;
mod shape;
mod structural;

pub use alpha::alpha_equivalent;
pub use structural::structurally_equal;
