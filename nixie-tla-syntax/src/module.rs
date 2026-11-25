//! Resolving `EXTENDS` into a loadable spec.
//!
//! A TLA+ module is rarely self-contained: `MC.tla` extends `EWD998.tla`,
//! which extends `Integers` and `FiniteSets`. Until those are followed, every
//! imported name is unknown, and [`crate::level`] can only mark the levels
//! that depend on them as untrusted. Measured over the corpora, that was
//! 1 806 of 7 774 definitions – the single largest source of lost coverage.
//!
//! # Scope
//!
//! This resolves **`EXTENDS`** and nothing else, on purpose.
//!
//! `EXTENDS` performs no substitution: the extended module's declarations and
//! definitions become visible exactly as they are, so their levels carry over
//! exactly. That makes the import sound rather than approximate.
//!
//! `INSTANCE` is different – `I == INSTANCE N WITH v <- e` substitutes into
//! `N`, and a substitution can *lower* a level (replacing a variable with a
//! constant). Computing that needs the substitution applied, so instance
//! members stay untrusted until the lowering pass in `nixie-tla` can do it
//! properly. Implementing what can be exact and marking the rest is the same
//! contract the level checker already works under.

use crate::ast::Module;
use crate::error::SyntaxError;
use crate::span::Span;
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
    /// `@type:` annotations, attached to the declaration that follows them,
    /// with the module they belong to. The text is raw: the Type1 grammar
    /// lives one layer up, where the type system does.
    pub annotations: Vec<Annotation>,
    /// `@typeAlias: NAME = TYPE;` definitions (issue #17), module-name-agnostic
    /// and in source order. A `@type:` annotation naming `NAME` resolves to
    /// the aliased type at seeding time.
    pub type_aliases: Vec<(String, String)>,
}

/// One `@type:` annotation, bound to the declaration that follows it.
#[derive(Debug, Clone)]
pub struct Annotation {
    /// The module the annotated declaration belongs to.
    pub module: String,
    /// The annotated declaration's name (a CONSTANT, VARIABLE, or operator
    /// definition – whichever unit the comment precedes).
    pub name: String,
    /// The annotation text after `@type:`, untrimmed of nothing.
    pub text: String,
    /// Where the comment was, for diagnostics.
    pub span: Span,
    /// The start offset of the declaration's **name** the annotation bound
    /// to – the anchor the attach pass chose, precise whatever the name's
    /// scope (module level, or a `LET` definition inside a body).
    pub decl_offset: u32,
}

impl LoadedSpec {
    /// A spec consisting of one already-parsed module.
    ///
    /// The single-file case, with nothing to resolve: no `EXTENDS` are
    /// followed, so `missing` and `cycles` are empty by construction rather
    /// than by assumption. Anything the module extends stays unresolved, which
    /// is exactly what a caller that did not ask for a search path should get.
    #[must_use]
    pub fn single(parsed: crate::ParsedFile) -> Self {
        let name = parsed.module.name.name.clone();
        let annotations = attach_annotations(&name, &parsed.module, &parsed.comments);
        let type_aliases = collect_type_aliases(&parsed.comments);
        Self {
            root: name.clone(),
            modules: vec![(name, parsed.module)],
            missing: Vec::new(),
            cycles: Vec::new(),
            annotations,
            type_aliases,
        }
    }

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
    /// cannot be parsed is skipped and recorded there too – a spec is still
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
        let mut comments_by_module: BTreeMap<String, Vec<crate::token::Comment>> = BTreeMap::new();
        // Names wanted by INSTANCE that no file supplied; nested submodules
        // may satisfy them.
        let mut submodule_wanted: BTreeSet<String> = BTreeSet::new();
        comments_by_module.insert(root_name.clone(), parsed.comments);
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
                // A nested `---- MODULE dep ----` inside an already-loaded
                // module satisfies the dependency without any file: Rec12's
                // `I == INSTANCE inner` is exactly this. Collected after
                // the whole queue drains, so a submodule declared *later*
                // in the same file is found too.
                match self.find_and_parse(&dep, &dirs) {
                    Some(m) => {
                        // `@type:` annotations travel with the module they
                        // annotate; the file's comments are kept until the
                        // attachment pass at the end.
                        comments_by_module.insert(dep.clone(), m.comments.clone());
                        queue.push((dep, m))
                    }
                    None => {
                        submodule_wanted.insert(dep);
                    }
                }
            }
        }

        // Nested modules: registered under their own names so `INSTANCE`
        // can find them, and their own `EXTENDS` become dependencies. A
        // submodule's definitions do NOT join any visible name space – the
        // loader only registers the module; visibility is the lowerer's
        // instance machinery, which substitutes rather than imports.
        loop {
            // Collect this round's additions first (submodules are cheap
            // clones of already-parsed ASTs), then insert – no borrow of
            // `loaded` may survive the mutation.
            let mut round: Vec<(String, Module, Vec<String>)> = Vec::new();
            for module in loaded.values() {
                for unit in &module.units {
                    if let crate::ast::UnitKind::Submodule(sub) = &unit.kind {
                        let sub_name = sub.name.name.clone();
                        if loaded.contains_key(&sub_name)
                            || round.iter().any(|(n, _, _)| *n == sub_name)
                        {
                            continue;
                        }
                        let sub_extends: Vec<String> =
                            sub.extends().into_iter().map(|i| i.name.clone()).collect();
                        round.push((sub_name, (**sub).clone(), sub_extends));
                    }
                }
            }
            if round.is_empty() {
                break;
            }
            for (sub_name, sub, sub_extends) in round {
                comments_by_module.insert(sub_name.clone(), sub.comments.clone());
                deps.insert(sub_name.clone(), sub_extends);
                loaded.insert(sub_name, sub);
            }
        }
        for name in &submodule_wanted {
            if !loaded.contains_key(name) {
                missing.insert(name.clone());
            }
        }

        let (order, cycles) = topological_order(&root_name, &deps, &loaded);
        let modules: Vec<(String, Module)> = order
            .into_iter()
            .filter_map(|n| loaded.remove(&n).map(|m| (n, m)))
            .collect();

        let annotations: Vec<Annotation> = modules
            .iter()
            .flat_map(|(name, module)| {
                let empty = Vec::new();
                let comments = comments_by_module.get(name).unwrap_or(&empty);
                attach_annotations(name, module, comments)
            })
            .collect();

        let type_aliases: Vec<(String, String)> = comments_by_module
            .values()
            .flat_map(|cs| collect_type_aliases(cs).into_iter())
            .collect();

        Ok(LoadedSpec {
            root: root_name,
            modules,
            missing: missing.into_iter().collect(),
            cycles,
            annotations,
            type_aliases,
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

/// Attach each `\* @type: …` comment to the declaration that follows it.
///
/// "Follows" is by source position: the annotated unit is the first one
/// whose span starts after the comment ends, in the same module. A comment
/// that precedes nothing (end of module) is dropped – there is no
/// declaration to annotate, and inventing one would be the silent-gap
/// pattern this codebase refuses elsewhere.
/// The operator definition whose **name** starts at `decl_offset` – a
/// module-level definition or a `LET`-scoped one inside a body, whichever
/// the attach pass bound an annotation to.
///
/// Walked iteratively; `LET` bodies are reached through
/// [`crate::ast::Expr::subexprs`].
#[must_use]
pub fn operator_at<'m>(
    module: &'m Module,
    decl_offset: u32,
) -> Option<(&'m [crate::ast::OpDecl], &'m crate::ast::Expr)> {
    let find_in_body =
        |body: &'m crate::ast::Expr| -> Option<(&'m [crate::ast::OpDecl], &'m crate::ast::Expr)> {
            let mut work = vec![body];
            while let Some(cur) = work.pop() {
                if let crate::ast::ExprKind::Let { defs, .. } = &cur.kind {
                    for d in defs {
                        if let crate::ast::UnitKind::OpDef {
                            name, params, body, ..
                        } = &d.kind
                            && name.span.start.offset == decl_offset
                        {
                            return Some((params, body));
                        }
                    }
                }
                work.extend(cur.subexprs());
            }
            None
        };
    for unit in &module.units {
        match &unit.kind {
            crate::ast::UnitKind::OpDef {
                name, params, body, ..
            } => {
                if name.span.start.offset == decl_offset {
                    return Some((params, body));
                }
                if let Some(hit) = find_in_body(body) {
                    return Some(hit);
                }
            }
            crate::ast::UnitKind::FnDef { body, .. }
            | crate::ast::UnitKind::Assume { body, .. }
            | crate::ast::UnitKind::Theorem { body, .. } => {
                if let Some(hit) = find_in_body(body) {
                    return Some(hit);
                }
            }
            _ => {}
        }
    }
    None
}

/// Collect `@typeAlias: NAME = TYPE;` comments as `(name, type-text)`
/// pairs. The alias body is the raw text after `=` (the trailing `;` is
/// stripped here, matching how `@type:` treats one); parsing it is the
/// annotation layer's business, where the Type1 grammar lives.
fn collect_type_aliases(comments: &[crate::token::Comment]) -> Vec<(String, String)> {
    let mut out = Vec::new();
    for c in comments {
        let body = c.text.trim();
        let Some(rest) = body.strip_prefix("@typeAlias:") else {
            continue;
        };
        let rest = rest.trim();
        let Some(eq) = rest.find('=') else {
            continue;
        };
        let name = rest[..eq].trim().to_string();
        let mut ty = rest[eq + 1..].trim().to_string();
        if let Some(semi) = ty.rfind(';') {
            ty.truncate(semi);
        }
        if !name.is_empty() && !ty.is_empty() {
            out.push((name, ty));
        }
    }
    out
}

fn attach_annotations(
    module: &str,
    m: &Module,
    comments: &[crate::token::Comment],
) -> Vec<Annotation> {
    use crate::token::Comment;
    let named: Vec<(u32, &str)> = comments
        .iter()
        .filter_map(|c: &Comment| {
            let body = c.text.trim();
            let rest = body.strip_prefix("@type:")?;
            Some((c.span.start.offset, rest.trim()))
        })
        .collect();
    if named.is_empty() {
        return Vec::new();
    }

    // Declaration anchors – the **name's** position, not the unit's: a
    // `CONSTANT`/`VARIABLE` unit's span starts at the keyword, which is
    // *before* the annotation comment that precedes the name inside it –
    // anchoring on the unit start mis-bound every such annotation to the
    // *next* declaration, found the moment the first annotated spec ran.
    // A declaration block declares **several** names, each with its own
    // position, and an interleaved comment annotates the *next* name,
    // not the block: `VARIABLES \* @type: Int; x, \* @type: Str; y`
    // (Test1226's very shape) binds each annotation to the name that
    // follows it. One anchor per name.
    //
    // A `LET` definition is an anchor too, wherever it sits in a body: an
    // annotation inside a definition binds to the *next* definition at its
    // own level, and binding it to the next module-level unit instead
    // attributed NestedCallByName's `LET F` signature to `Init` – the
    // operator-signature check then declined a specification Apalache
    // accepts. The walk is iterative (`Expr::subexprs`), LET bodies
    // included through it.
    let mut decls: Vec<(u32, String)> = Vec::new();
    let collect_body = |body: &crate::ast::Expr, decls: &mut Vec<(u32, String)>| {
        let mut work = vec![body];
        while let Some(cur) = work.pop() {
            if let crate::ast::ExprKind::Let { defs, .. } = &cur.kind {
                for d in defs {
                    if let crate::ast::UnitKind::OpDef { name, .. } = &d.kind {
                        decls.push((name.span.start.offset, name.name.clone()));
                    }
                }
            }
            work.extend(cur.subexprs());
        }
    };
    for unit in &m.units {
        let named: Vec<(u32, String)> = match &unit.kind {
            crate::ast::UnitKind::OpDef { name, body, .. } => {
                let mut out = vec![(name.span.start.offset, name.name.clone())];
                collect_body(body, &mut out);
                out
            }
            crate::ast::UnitKind::FnDef { body, .. } => {
                let mut out = Vec::new();
                collect_body(body, &mut out);
                out
            }
            crate::ast::UnitKind::VariableDecl(ids) => ids
                .iter()
                .map(|i| (i.span.start.offset, i.name.clone()))
                .collect(),
            crate::ast::UnitKind::ConstantDecl(ds) => ds
                .iter()
                .map(|d| (d.name.span.start.offset, d.name.name.clone()))
                .collect(),
            _ => Vec::new(),
        };
        decls.extend(named);
    }
    decls.sort_by_key(|(off, _)| *off);
    let mut out = Vec::new();
    for (off, text) in named {
        // The first declaration after the comment.
        let Some((doff, name)) = decls.iter().find(|(doff, _)| *doff > off) else {
            continue;
        };
        out.push(Annotation {
            module: module.to_string(),
            name: name.clone(),
            text: text.to_string(),
            span: crate::span::Span::default(),
            decl_offset: *doff,
        });
    }
    out
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
