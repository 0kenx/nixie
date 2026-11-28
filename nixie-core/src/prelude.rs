//! Prelude for no_std / std compatibility.

#[cfg(not(feature = "std"))]
#[allow(unused_imports)]
pub(crate) use alloc::{
    borrow::ToOwned,
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
pub(crate) use std::collections::hash_map::DefaultHasher;
#[cfg(feature = "std")]
#[allow(unused_imports)]
pub(crate) use std::collections::{
    BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, VecDeque, hash_map,
};
#[cfg(feature = "std")]
#[allow(unused_imports)]
pub(crate) use std::rc::Rc;
#[cfg(feature = "std")]
#[allow(unused_imports)]
pub(crate) use std::{boxed::Box, format, string::String, vec};

#[cfg(feature = "std")]
#[allow(unused_imports)]
pub(crate) use std::sync::Arc;

// FxHash types: use rustc_hash in std mode, hashbrown+FxHasher in no_std
#[cfg(feature = "std")]
#[allow(unused_imports)]
pub(crate) use rustc_hash::{FxHashMap, FxHashSet};

#[cfg(not(feature = "std"))]
pub(crate) type FxHashMap<K, V> =
    hashbrown::HashMap<K, V, core::hash::BuildHasherDefault<rustc_hash::FxHasher>>;
#[cfg(not(feature = "std"))]
pub(crate) type FxHashSet<K> =
    hashbrown::HashSet<K, core::hash::BuildHasherDefault<rustc_hash::FxHasher>>;

// Under `no_std` the `std`-only `f64` methods come from `F64Ext` and
// `std::sync::{Mutex, OnceLock}` from their stand-ins (see `no_std` at the crate root);
// every module gets both through this glob.
#[cfg(not(feature = "std"))]
#[allow(unused_imports)]
pub(crate) use crate::no_std::{F64Ext, Mutex, OnceLock};
#[cfg(feature = "std")]
#[allow(unused_imports)]
pub(crate) use std::sync::{Mutex, OnceLock};

/// [`std::collections::hash_map::DefaultHasher`]'s shape under `no_std`:
/// the default builder's hasher (foldhash), behind the `new` the call sites
/// construct it with. hashbrown's own type is only built through a builder.
#[cfg(not(feature = "std"))]
pub(crate) struct DefaultHasher(hashbrown::DefaultHasher);

#[cfg(not(feature = "std"))]
impl DefaultHasher {
    pub(crate) fn new() -> Self {
        use core::hash::BuildHasher;
        Self(hashbrown::DefaultHashBuilder::default().build_hasher())
    }
}

#[cfg(not(feature = "std"))]
impl core::hash::Hasher for DefaultHasher {
    fn finish(&self) -> u64 {
        self.0.finish()
    }

    fn write(&mut self, bytes: &[u8]) {
        self.0.write(bytes);
    }
}
