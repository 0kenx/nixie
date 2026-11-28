//! Prelude for no_std / std compatibility.

#[cfg(not(feature = "std"))]
#[allow(unused_imports)]
pub(crate) use alloc::{
    borrow::{Cow, ToOwned},
    boxed::Box,
    collections::{BTreeMap, BTreeSet, BinaryHeap, VecDeque},
    format,
    rc::Rc,
    string::{String, ToString},
    vec,
    vec::Vec,
};

#[cfg(not(feature = "std"))]
#[allow(unused_imports)]
pub(crate) use portable_atomic_util::Arc;

#[cfg(not(feature = "std"))]
#[allow(unused_imports)]
pub(crate) use hashbrown::{HashMap, HashSet, hash_map};

#[cfg(feature = "std")]
#[allow(unused_imports)]
pub(crate) use std::collections::{
    BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, VecDeque, hash_map,
};
#[cfg(feature = "std")]
#[allow(unused_imports)]
pub(crate) use std::{borrow::Cow, rc::Rc};
#[cfg(feature = "std")]
#[allow(unused_imports)]
pub(crate) use std::{boxed::Box, format, string::String, vec};

#[cfg(feature = "std")]
#[allow(unused_imports)]
pub(crate) use std::sync::Arc;

#[cfg(feature = "std")]
#[allow(unused_imports)]
pub(crate) use rustc_hash::{FxHashMap, FxHashSet};

#[cfg(not(feature = "std"))]
pub(crate) type FxHashMap<K, V> =
    hashbrown::HashMap<K, V, core::hash::BuildHasherDefault<rustc_hash::FxHasher>>;
#[cfg(not(feature = "std"))]
pub(crate) type FxHashSet<K> =
    hashbrown::HashSet<K, core::hash::BuildHasherDefault<rustc_hash::FxHasher>>;

#[cfg(not(feature = "std"))]
#[allow(unused_macros)]
macro_rules! println {
    ($($arg:tt)*) => {};
}
#[cfg(not(feature = "std"))]
#[allow(unused_imports)]
pub(crate) use println;

#[cfg(not(feature = "std"))]
#[allow(unused_macros)]
macro_rules! eprintln {
    ($($arg:tt)*) => {};
}
#[cfg(not(feature = "std"))]
#[allow(unused_imports)]
pub(crate) use eprintln;

// Under `no_std` the `std`-only `f64` methods (`sqrt`, `ln`, ...) come from
// `F64Ext` and `std::sync::{Mutex, OnceLock}` from their stand-ins (all
// defined in `nixie_core::no_std`); every module gets them through this glob.
#[cfg(not(feature = "std"))]
#[allow(unused_imports)]
pub(crate) use nixie_core::no_std::{F64Ext, Mutex, OnceLock};
#[cfg(feature = "std")]
#[allow(unused_imports)]
pub(crate) use std::sync::{Mutex, OnceLock};
