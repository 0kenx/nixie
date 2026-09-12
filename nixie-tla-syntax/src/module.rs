//! Resolving `EXTENDS` into a loadable spec.
//!
//! A TLA+ module is rarely self-contained: `MC.tla` extends `EWD998.tla`,
//! which extends `Integers` and `FiniteSets`. Until those are followed, every
//! imported name is unknown, and [`crate::level`] can only mark the levels
//! that depend on them as untrusted. Measured over the corpora, that was
//! 1 806 of 7 774 definitions — the single largest source of lost coverage.
//!
//! # Scope
//!
//! This resolves **`EXTENDS`** and nothing else, on purpose.
//!
//! `EXTENDS` performs no substitution: the extended module's declarations and
//! definitions become visible exactly as they are, so their levels carry over
//! exactly. That makes the import sound rather than approximate.
//!
//! `INSTANCE` is different — `I == INSTANCE N WITH v <- e` substitutes into
//! `N`, and a substitution can *lower* a level (replacing a variable with a
//! constant). Computing that needs the substitution applied, so instance
//! members stay untrusted until the lowering pass in `nixie-tla` can do it
//! properly. Implementing what can be exact and marking the rest is the same
//! contract the level checker already works under.

use crate::ast::Module;
use crate::error::SyntaxError;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

/// Modules SANY provides itself; there is no `.tla` file to find.
///
/// Their operators are all constant level and already known to
/// [`crate::level`], so a missing file for one of these is not a gap.
/// Only modules that ship *inside* `tla2tools.jar` belong here. Community
/// modules such as `Functions`, `Folds` and `SequencesExt` are real `.tla`
/// files: listing them here made the loader skip them, so their operators
/// stayed unresolved even with the community checkout on the search path.
pub const BUILTIN_MODULES: &[&str] = &[
    "Naturals",
    "Integers",
    "Reals",
    "Sequences",
    "FiniteSets",
    "Bags",
    "TLC",
    "TLCExt",
    "TLAPS",
    "Randomization",
];

/// What went wrong while loading a spec.
#[derive(Debug)]
pub enum LoadError {
    /// The root file could not be read.
    Io {
        /// The path that failed.
        path: PathBuf,
        /// The underlying error.
        source: std::io::Error,
    },
    /// A file was found but did not parse.
    Syntax {
        /// The path that failed.
        path: PathBuf,
        /// The parse error.
        source: SyntaxError,
    },
}

impl core::fmt::Display for LoadError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Io { path, source } => write!(f, "{}: {source}", path.display()),
            Self::Syntax { path, source } => write!(f, "{}: {source}", path.display()),
        }
    }
}

impl std::error::Error for LoadError {}

/// A root module together with everything it transitively extends.
#[derive(Debug)]
pub struct LoadedSpec {
    /// Name of the root module.
    pub root: String,
    /// Every loaded module, **dependency-first**: a module always appears
    /// after everything it extends, so one pass in this order suffices for
    /// any analysis that needs its imports resolved first.
    pub modules: Vec<(String, Module)>,
    /// Extended modules that are neither built in nor findable on the search
    /// path. Reported rather than ignored: they are exactly the names that
    /// will stay unresolved, and a caller deciding whether to trust a result
    /// needs to know.
    pub missing: Vec<String>,
    /// Modules involved in an `EXTENDS` cycle, which TLA+ forbids. Reported
    /// rather than looped on.
    pub cycles: Vec<String>,
}

impl LoadedSpec {
    /// The root module.
    #[must_use]
    pub fn root_module(&self) -> Option<&Module> {
        self.modules
            .iter()
            .find(|(n, _)| *n == self.root)
            .map(|(_, m)| m)
    }
}

/// Finds and parses the modules a spec extends.
#[derive(Debug, Default, Clone)]
pub struct Loader {
    search_paths: Vec<PathBuf>,
}

impl Loader {
    /// A loader that searches only the root file's own directory.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a directory to search for `.tla` files.
    #[must_use]
    pub fn with_search_path(mut self, dir: impl Into<PathBuf>) -> Self {
        self.search_paths.push(dir.into());
        self
    }

    /// Load `path` and everything it transitively extends.
    ///
    /// # Errors
    ///
    /// Fails only if the *root* cannot be read or parsed. A dependency that
    /// cannot be found is recorded in [`LoadedSpec::missing`], and one that
    /// cannot be parsed is skipped and recorded there too — a spec is still
    /// worth analysing when one of its imports is unavailable, as long as the
    /// caller is told.
    pub fn load(&self, path: &Path) -> Result<LoadedSpec, LoadError> {
        let src = std::fs::read_to_string(path).map_err(|source| LoadError::Io {
            path: path.to_path_buf(),
            source,
        })?;
        let parsed = crate::parser::parse_file(&src).map_err(|source| LoadError::Syntax {
            path: path.to_path_buf(),
            source,
        })?;
        let root_name = parsed.module.name.name.clone();

        let mut dirs: Vec<PathBuf> = Vec::new();
        if let Some(parent) = path.parent() {
            dirs.push(parent.to_path_buf());
        }
        dirs.extend(self.search_paths.iter().cloned());

        let mut loaded: BTreeMap<String, Module> = BTreeMap::new();
        let mut deps: BTreeMap<String, Vec<String>> = BTreeMap::new();
        let mut missing: BTreeSet<String> = BTreeSet::new();

        // Breadth-first over EXTENDS, iteratively: the import graph is
        // user-controlled and may be deep.
        let mut queue: Vec<(String, Module)> = vec![(root_name.clone(), parsed.module)];
        while let Some((name, module)) = queue.pop() {
            let extends: Vec<String> = module
                .extends()
                .into_iter()
                .map(|i| i.name.clone())
                .collect();
            // `INSTANCE` targets are loaded too, but are *not* dependencies
            // for ordering or for imports: `INSTANCE` substitutes rather than
            // importing, so its names must not become visible. They still have
            // to be on hand, since a member cannot be resolved without the
            // module that defines it.
            let instantiated: Vec<String> = module
                .instantiated()
                .into_iter()
                .map(|i| i.name.clone())
                .collect();
            deps.insert(name.clone(), extends.clone());
            loaded.insert(name, module);

            for dep in extends.iter().cloned().chain(instantiated) {
                if loaded.contains_key(&dep) || deps.contains_key(&dep) {
                    continue;
                }
                if BUILTIN_MODULES.contains(&dep.as_str()) {
                    continue;
                }
                match self.find_and_parse(&dep, &dirs) {
                    Some(m) => queue.push((dep, m)),
                    None => {
                        missing.insert(dep);
                    }
                }
            }
        }

        let (order, cycles) = topological_order(&root_name, &deps, &loaded);
        let modules = order
            .into_iter()
            .filter_map(|n| loaded.remove(&n).map(|m| (n, m)))
            .collect();

        Ok(LoadedSpec {
            root: root_name,
            modules,
            missing: missing.into_iter().collect(),
            cycles,
        })
    }

    fn find_and_parse(&self, name: &str, dirs: &[PathBuf]) -> Option<Module> {
        for dir in dirs {
            let candidate = dir.join(format!("{name}.tla"));
            if !candidate.is_file() {
                continue;
            }
            let Ok(src) = std::fs::read_to_string(&candidate) else {
                continue;
            };
            // A dependency that does not parse is reported as missing rather
            // than failing the whole load: the root may still be analysable.
            if let Ok(parsed) = crate::parser::parse_file(&src) {
                return Some(parsed.module);
            }
        }
        None
    }
}

/// Dependency-first order, with any `EXTENDS` cycle reported rather than
/// looped on. Iterative depth-first search with an explicit stack.
fn topological_order(
    root: &str,
    deps: &BTreeMap<String, Vec<String>>,
    loaded: &BTreeMap<String, Module>,
) -> (Vec<String>, Vec<String>) {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Mark {
        Open,
        Done,
    }
    let mut mark: BTreeMap<String, Mark> = BTreeMap::new();
    let mut order: Vec<String> = Vec::new();
    let mut cycles: BTreeSet<String> = BTreeSet::new();

    // Frames carry resume state: which dependency index to visit next.
    let mut stack: Vec<(String, usize)> = vec![(root.to_string(), 0)];
    mark.insert(root.to_string(), Mark::Open);

    while let Some((name, idx)) = stack.pop() {
        let empty = Vec::new();
        let children = deps.get(&name).unwrap_or(&empty);
        if idx < children.len() {
            stack.push((name.clone(), idx + 1));
            let child = children[idx].clone();
            if !loaded.contains_key(&child) {
                continue; // built-in or missing
            }
            match mark.get(&child) {
                Some(Mark::Done) => {}
                Some(Mark::Open) => {
                    cycles.insert(child);
                }
                None => {
                    mark.insert(child.clone(), Mark::Open);
                    stack.push((child, 0));
                }
            }
        } else {
            mark.insert(name.clone(), Mark::Done);
            order.push(name);
        }
    }

    // Anything loaded but unreachable from the root (it cannot normally
    // happen, but a caller may hand us one) still gets analysed.
    for name in loaded.keys() {
        if !mark.contains_key(name) {
            order.push(name.clone());
        }
    }
    (order, cycles.into_iter().collect())
}
