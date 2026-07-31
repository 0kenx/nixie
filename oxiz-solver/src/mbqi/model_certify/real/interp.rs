//! The candidate interpretation the real certifier verifies.
//!
//! An uninterpreted function over the reals is interpreted as a finite table of
//! pinned argument values extended by one *affine* default — `λy. a·y + b` —
//! rather than by a single constant.  That is the difference that makes an
//! infinite real domain tractable: `∀x. f(x) = x` has no pins-plus-constant
//! model at all, but `f := λy. y` satisfies it outright, and the same shape
//! covers a macro definition (`g(x) = 2·x + 1`), a constant (`a = 0`) and the
//! identity in one representation.

use oxiz_core::interner::Spur;

#[allow(unused_imports)]
use crate::prelude::*;

use super::affine::{Affine, Rat};

/// The interpretation of one unary function over the reals.
#[derive(Clone, Debug)]
pub(crate) enum RealFunc {
    /// A real-valued function: pinned points plus an affine default.
    Num {
        /// Argument values the goal or the ground model already fixed, sorted.
        pins: Vec<(Rat, Rat)>,
        /// The value at every argument not pinned.
        default: Affine,
    },
    /// A boolean-valued predicate: pinned points plus a constant default.
    Bool {
        /// Argument values the goal or the ground model already fixed, sorted.
        pins: Vec<(Rat, bool)>,
        /// The value at every argument not pinned.
        default: bool,
    },
}

impl RealFunc {
    /// The pinned argument values, sorted and distinct.
    pub(crate) fn pin_args(&self) -> Vec<Rat> {
        match self {
            RealFunc::Num { pins, .. } => pins.iter().map(|(arg, _)| arg.clone()).collect(),
            RealFunc::Bool { pins, .. } => pins.iter().map(|(arg, _)| arg.clone()).collect(),
        }
    }

    /// The pinned real value at `arg`, if any.
    pub(crate) fn pin_num(&self, arg: &Rat) -> Option<&Rat> {
        match self {
            RealFunc::Num { pins, .. } => pins
                .binary_search_by(|(key, _)| key.cmp(arg))
                .ok()
                .and_then(|index| pins.get(index).map(|(_, value)| value)),
            RealFunc::Bool { .. } => None,
        }
    }

    /// The pinned boolean value at `arg`, if any.
    pub(crate) fn pin_bool(&self, arg: &Rat) -> Option<bool> {
        match self {
            RealFunc::Bool { pins, .. } => pins
                .binary_search_by(|(key, _)| key.cmp(arg))
                .ok()
                .and_then(|index| pins.get(index).map(|(_, value)| *value)),
            RealFunc::Num { .. } => None,
        }
    }
}

/// A total interpretation of every symbol a real goal mentions.
#[derive(Clone, Debug, Default)]
pub(crate) struct RealInterp {
    /// Unary uninterpreted functions.
    pub(crate) funcs: FxHashMap<Spur, RealFunc>,
    /// Real-valued free (declared or Skolem) constants.
    pub(crate) consts: FxHashMap<Spur, Rat>,
    /// Boolean free constants.
    pub(crate) bool_consts: FxHashMap<Spur, bool>,
}
