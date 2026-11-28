//! Prelude for no_std / std compatibility.

#[cfg(not(feature = "std"))]
pub(crate) use alloc::{
    boxed::Box,
    collections::{BTreeSet, BinaryHeap},
    format,
    string::{String, ToString},
    vec,
    vec::Vec,
};

#[cfg(not(feature = "std"))]
#[allow(unused_imports)]
pub(crate) use hashbrown::{HashMap, HashSet};

#[cfg(feature = "std")]
#[allow(unused_imports)]
pub(crate) use std::collections::{BTreeSet, BinaryHeap, HashMap, HashSet};
#[cfg(feature = "std")]
#[allow(unused_imports)]
pub(crate) use std::{boxed::Box, format, string::String, vec};

#[cfg(feature = "std")]
#[allow(unused_imports)]
pub(crate) use rustc_hash::{FxHashMap, FxHashSet};

#[cfg(not(feature = "std"))]
pub(crate) type FxHashMap<K, V> =
    hashbrown::HashMap<K, V, core::hash::BuildHasherDefault<rustc_hash::FxHasher>>;
#[cfg(not(feature = "std"))]
pub(crate) type FxHashSet<K> =
    hashbrown::HashSet<K, core::hash::BuildHasherDefault<rustc_hash::FxHasher>>;

// Diagnostics that print to stderr keep their `eprintln!` call sites in both
// configurations: under `std` the macro is the real one, under `no_std` the
// crate's own no-op shadows it (the same shape as the nixie-sat, -theories
// and -solver preludes).
#[cfg(not(feature = "std"))]
#[allow(unused_macros)]
macro_rules! eprintln {
    ($($arg:tt)*) => {};
}
#[cfg(not(feature = "std"))]
#[allow(unused_imports)]
pub(crate) use eprintln;

// Under `no_std` the `std`-only `f64` methods come from `F64Ext` (see the
// crate root), which every module gets through this glob.
#[cfg(not(feature = "std"))]
#[allow(unused_imports)]
pub(crate) use crate::F64Ext;
