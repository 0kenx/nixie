//! `INSTANCE` substitution.
//!
//! `EXTENDS` makes another module's definitions visible unchanged; `INSTANCE`
//! makes them visible *after substituting* for that module's declared
//! constants and variables. The substitution is the whole difference, and it
//! is why an instance member cannot simply be inlined the way an extended one
//! can.

use nixie_tla::Lowerer;
use nixie_tla_syntax::Loader;
use std::path::PathBuf;

struct Scratch(PathBuf);

impl Scratch {
    fn new(tag: &str, files: &[(&str, &str)]) -> Self {
        let dir = std::env::temp_dir().join(format!(
            "nixie-tla-inst-{tag}-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("scratch dir");
        for (name, body) in files {
            std::fs::write(dir.join(name), body).expect("write module");
        }
        Self(dir)
    }
    fn path(&self, n: &str) -> PathBuf {
        self.0.join(n)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// Lower `name` in the root module of the spec rooted at `file`.
fn lower_in(dir: &Scratch, file: &str, name: &str) -> String {
    let spec = Loader::new().load(&dir.path(file)).expect("spec loads");
    let root = spec.root_module().expect("root module").clone();
    let mut low = Lowerer::new();
    low.add_spec(&spec);
    match low.lower_named(&root, name) {
        Ok(k) => format!("{k:?}"),
        Err(e) => panic!("lowering {name} failed: {e}"),
    }
}

#[test]
fn a_named_instance_substitutes_its_with_clause() {
    let s = Scratch::new(
        "named",
        &[
            (
                "Inner.tla",
                "---- MODULE Inner ----\nVARIABLE v\nCONSTANT c\nBoth == v = c\n====\n",
            ),
            (
                "Outer.tla",
                "---- MODULE Outer ----\nVARIABLE w\nI == INSTANCE Inner WITH v <- w, c <- 7\n\
                 A == I!Both\n====\n",
            ),
        ],
    );
    let out = lower_in(&s, "Outer.tla", "A");
    // The substitution must have happened: `w` and 7, never Inner's own
    // `v` and `c`.
    assert!(out.contains("\"w\""), "substituted variable missing: {out}");
    assert!(out.contains("\"7\""), "substituted constant missing: {out}");
    assert!(!out.contains("\"v\""), "Inner's own name leaked: {out}");
    assert!(!out.contains("\"c\""), "Inner's own name leaked: {out}");
}

#[test]
fn an_unsubstituted_declaration_takes_the_same_name_here() {
    // TLA+ substitutes a declared name with no `WITH` clause by the same-named
    // symbol of the instantiating module.
    let s = Scratch::new(
        "implicit",
        &[
            (
                "Inner.tla",
                "---- MODULE Inner ----\nVARIABLE v\nGet == v\n====\n",
            ),
            (
                "Outer.tla",
                "---- MODULE Outer ----\nVARIABLE v\nI == INSTANCE Inner\nA == I!Get\n====\n",
            ),
        ],
    );
    let out = lower_in(&s, "Outer.tla", "A");
    assert!(out.contains("\"v\""), "{out}");
}

#[test]
fn instance_members_may_take_arguments() {
    let s = Scratch::new(
        "args",
        &[
            (
                "Inner.tla",
                "---- MODULE Inner ----\nEXTENDS Integers\nCONSTANT c\nAdd(a) == a + c\n====\n",
            ),
            (
                "Outer.tla",
                "---- MODULE Outer ----\nEXTENDS Integers\nI == INSTANCE Inner WITH c <- 5\n\
                 A == I!Add(3)\n====\n",
            ),
        ],
    );
    let out = lower_in(&s, "Outer.tla", "A");
    assert!(out.contains("\"3\"") && out.contains("\"5\""), "{out}");
}

#[test]
fn a_member_reaching_another_member_stays_inside_the_instance() {
    // `Outer` also defines `Helper`. The one `Inner!Uses` sees must be
    // `Inner`'s, under `Inner`'s substitution -- not the instantiating
    // module's same-named definition.
    let s = Scratch::new(
        "shadow",
        &[
            (
                "Inner.tla",
                "---- MODULE Inner ----\nVARIABLE v\nHelper == v\nUses == Helper\n====\n",
            ),
            (
                "Outer.tla",
                "---- MODULE Outer ----\nVARIABLE w\nHelper == 999\n\
                 I == INSTANCE Inner WITH v <- w\nA == I!Uses\n====\n",
            ),
        ],
    );
    let out = lower_in(&s, "Outer.tla", "A");
    assert!(out.contains("\"w\""), "{out}");
    assert!(
        !out.contains("999"),
        "the instantiating module's `Helper` must not be used: {out}"
    );
}

#[test]
fn an_unnamed_instance_makes_members_visible_unprefixed() {
    let s = Scratch::new(
        "open",
        &[
            (
                "Inner.tla",
                "---- MODULE Inner ----\nVARIABLE v\nGet == v\n====\n",
            ),
            (
                "Outer.tla",
                "---- MODULE Outer ----\nVARIABLE w\nINSTANCE Inner WITH v <- w\nA == Get\n====\n",
            ),
        ],
    );
    let out = lower_in(&s, "Outer.tla", "A");
    assert!(out.contains("\"w\""), "{out}");
}

#[test]
fn the_loader_follows_instance_targets() {
    // `INSTANCE` targets are not `EXTENDS` dependencies, but they still have
    // to be loaded or the member cannot be resolved at all.
    let s = Scratch::new(
        "load",
        &[
            ("Inner.tla", "---- MODULE Inner ----\nK == 1\n====\n"),
            (
                "Outer.tla",
                "---- MODULE Outer ----\nI == INSTANCE Inner\nA == I!K\n====\n",
            ),
        ],
    );
    let spec = Loader::new().load(&s.path("Outer.tla")).expect("loads");
    assert!(
        spec.modules.iter().any(|(n, _)| n == "Inner"),
        "the instantiated module must be loaded: {:?}",
        spec.modules.iter().map(|(n, _)| n).collect::<Vec<_>>()
    );
    // …but it must not become an import: `INSTANCE` substitutes, it does not
    // make names visible.
    let Some(root) = spec.root_module() else {
        panic!("no root");
    };
    assert!(root.extends().is_empty());
}

#[test]
fn an_unknown_instance_is_reported_by_name() {
    let s = Scratch::new(
        "unknown",
        &[(
            "Outer.tla",
            "---- MODULE Outer ----\nA == Missing!Op\n====\n",
        )],
    );
    let spec = Loader::new().load(&s.path("Outer.tla")).expect("loads");
    let root = spec.root_module().expect("root").clone();
    let mut low = Lowerer::new();
    low.add_spec(&spec);
    let e = low.lower_named(&root, "A").map(|_| ()).unwrap_err();
    assert!(
        format!("{e}").contains("Missing!Op"),
        "the diagnostic must name it: {e}"
    );
}
