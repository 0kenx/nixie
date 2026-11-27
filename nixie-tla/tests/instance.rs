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

/// A declared **operator** constant is substituted by an operator:
/// `CONSTANT P(_, _)` in the instantiated module, `WITH P <- Q` in the
/// instance, and every `P(a, b)` inside the module is `Q(a, b)`. Lowered as
/// a value, the replacement never applied and `P` stayed an opaque constant
/// the encoder declines (`ConstantOperatorImpl.tla`, a cell of Apalache's
/// suite). A `LAMBDA` is an operator too.
#[test]
fn an_operator_constant_is_substituted_by_an_operator() {
    let s = Scratch::new(
        "operator",
        &[
            (
                "Inner.tla",
                "---- MODULE Inner ----\nCONSTANTS A, B, P(_, _)\nGood == \\E a \\in A, b \\in B: P(a, b)\n====\n",
            ),
            (
                "Outer.tla",
                "---- MODULE Outer ----\nEqual(x, y) == x = y\nI == INSTANCE Inner WITH A <- {0, 1}, B <- {1, 2}, P <- Equal\n\
                 L == INSTANCE Inner WITH A <- {0, 1}, B <- {2, 3}, P <- LAMBDA x, y: x + 1 = y\n\
                 A == I!Good\nB == L!Good\n====\n",
            ),
        ],
    );
    let out = lower_in(&s, "Outer.tla", "A");
    assert!(
        out.contains("Eq("),
        "the replacement operator's body is applied: {out}"
    );
    assert!(out.contains("\"1\""), "{out}");
    assert!(
        !out.contains("Opaque(\"P\""),
        "the operator constant stayed opaque: {out}"
    );
    assert!(!out.contains("Opaque(\"Equal\""), "{out}");
    let out = lower_in(&s, "Outer.tla", "B");
    assert!(
        out.contains("Arith(Add"),
        "the LAMBDA's body is applied: {out}"
    );
    assert!(!out.contains("Opaque(\"P\""), "{out}");
}

/// The replacement must take as many arguments as the declaration: a
/// mismatch is reported at the instance, by name.
#[test]
fn an_operator_replacement_of_the_wrong_arity_is_reported() {
    let s = Scratch::new(
        "operator-arity",
        &[
            (
                "Inner.tla",
                "---- MODULE Inner ----\nCONSTANT P(_, _)\nGood == P(1, 2)\n====\n",
            ),
            (
                "Outer.tla",
                "---- MODULE Outer ----\nOne(x) == x = 1\nI == INSTANCE Inner WITH P <- One\nA == I!Good\n====\n",
            ),
        ],
    );
    let spec = Loader::new()
        .load(&s.path("Outer.tla"))
        .expect("spec loads");
    let root = spec.root_module().expect("root module");
    let mut low = Lowerer::new();
    low.add_spec(&spec);
    let err = low.lower_named(root, "A").expect_err("the arity is wrong");
    assert!(
        err.to_string().contains("argument") && err.to_string().contains("P"),
        "{err}"
    );
}

/// An `INSTANCE` of a **built-in** module – `INSTANCE Apalache`
/// (`TestSequencesExt.tla`), `LOCAL INSTANCE Bags` inside the community
/// `BagsExt` – has no text to look through and needs none: its members are
/// the built-in operators, and `A!SetToBag({1})` lowers as `SetToBag({1})`
/// does. It was "neither defined in this file nor loaded from the search
/// path". A `WITH` clause on one substitutes for nothing the module
/// declares, and is reported.
#[test]
fn an_instance_of_a_built_in_module_resolves_its_members_by_name() {
    let s = Scratch::new(
        "builtin",
        &[(
            "Outer.tla",
            "---- MODULE Outer ----\nEXTENDS Integers, Bags\nA == INSTANCE Bags\n\
             B == A!SetToBag({1})\nC == SetToBag({1})\nD == A!EmptyBag\n====\n",
        )],
    );
    let through = lower_in(&s, "Outer.tla", "B");
    let direct = lower_in(&s, "Outer.tla", "C");
    assert_eq!(through, direct, "the member lowers as the bare name does");
    assert!(!through.contains("Opaque(\"SetToBag\""), "{through}");
    // A nullary member, the same way.
    let s = Scratch::new(
        "builtin-nullary",
        &[(
            "Outer.tla",
            "---- MODULE Outer ----\nEXTENDS Integers, Bags\nA == INSTANCE Bags\n\
             B == A!EmptyBag\nC == EmptyBag\n====\n",
        )],
    );
    assert_eq!(
        lower_in(&s, "Outer.tla", "B"),
        lower_in(&s, "Outer.tla", "C")
    );
    let spec = Loader::new()
        .load(&s.path("Outer.tla"))
        .expect("spec loads");
    let root = spec.root_module().expect("root module").clone();
    let mut low = Lowerer::new();
    low.add_spec(&spec);
    low.lower_named(&root, "B").expect("lowers");
    assert!(
        low.missing_instances().is_empty(),
        "a built-in target is not missing"
    );
    assert!(low.instance_problems().is_empty());

    let s = Scratch::new(
        "builtin-with",
        &[(
            "Outer.tla",
            "---- MODULE Outer ----\nEXTENDS Integers, Bags\nA == INSTANCE Bags WITH x <- 1\n\
             B == TRUE\n====\n",
        )],
    );
    let spec = Loader::new()
        .load(&s.path("Outer.tla"))
        .expect("spec loads");
    let root = spec.root_module().expect("root module").clone();
    let mut low = Lowerer::new();
    low.add_spec(&spec);
    low.lower_named(&root, "B").expect("lowers");
    let problems = low.instance_problems();
    assert_eq!(problems.len(), 1, "{problems:?}");
    assert_eq!(problems[0].0, "Bags");
    assert!(problems[0].2.contains("built-in"), "{problems:?}");
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

#[test]
fn an_instance_inside_a_let_resolves_and_substitutes() {
    let s = Scratch::new(
        "letinst",
        &[
            (
                "A.tla",
                "---- MODULE A ----\nVARIABLE v\nCONSTANT c\nF == v + c\n====\n",
            ),
            (
                "B.tla",
                "---- MODULE B ----\nVARIABLES w, q\n\
                 N == LET M == INSTANCE A WITH v <- w, c <- 41 IN M!F\n\
                 ==== \n",
            ),
        ],
    );
    let out = lower_in(&s, "B.tla", "N");
    // Under the LET-level substitution: `w + 41`, never A's own `v` or `c`.
    assert!(out.contains("w"), "substituted variable: {out}");
    assert!(out.contains("41"), "substituted constant: {out}");
}

/// The LET-scoped instance must vanish after the LET: a same-named
/// module-level instance is what `M!F` means outside the body.
#[test]
fn a_let_instance_is_scoped_and_restores_the_outer_one() {
    let s = Scratch::new(
        "letshadow",
        &[
            ("A.tla", "---- MODULE A ----\nCONSTANT c\nF == c\n====\n"),
            (
                "B.tla",
                "---- MODULE B ----\n\
                 I == INSTANCE A WITH c <- 1\n\
                 In == LET I == INSTANCE A WITH c <- 2 IN I!F\n\
                 Out == I!F\n\
                 ====\n",
            ),
        ],
    );
    let inner = lower_in(&s, "B.tla", "In");
    assert!(inner.contains('2'), "the LET instance wins inside: {inner}");
    assert!(!inner.contains('1'), "not the outer one inside: {inner}");
    let outer = lower_in(&s, "B.tla", "Out");
    assert!(
        outer.contains('1'),
        "the module-level one after the LET: {outer}"
    );
}

/// A LET-level instance whose target was never loaded is a hard error at
/// the instance itself, not a name error at the use.
#[test]
fn a_let_instance_with_a_missing_target_errors_at_the_instance() {
    let s = Scratch::new(
        "letmissing",
        &[(
            "B.tla",
            "---- MODULE B ----\nN == LET M == INSTANCE Nowhere IN M!F\n====\n",
        )],
    );
    let spec = Loader::new().load(&s.path("B.tla")).expect("loads");
    let root = spec.root_module().expect("root").clone();
    let mut low = Lowerer::new();
    low.add_spec(&spec);
    let e = low.lower_named(&root, "N").map(|_| ()).unwrap_err();
    assert!(
        format!("{e}").contains("Nowhere"),
        "the diagnostic names the missing module: {e}"
    );
}

/// test59.tla's exact shape: the LET also mixes an ordinary definition
/// with the instance, and the member is used under a prime-relevant
/// expression.
#[test]
fn a_let_instance_with_a_sibling_definition_test59_shape() {
    let s = Scratch::new(
        "test59",
        &[
            (
                "test59a.tla",
                "---- MODULE test59a ----\nEXTENDS Naturals\nVARIABLE x\nxplus1 == x+1\n====\n",
            ),
            (
                "test59.tla",
                "---- MODULE test59 ----\nEXTENDS Naturals\nVARIABLE y\n\
                 Next == LET x == y+1\n\
                 \t\t  M == INSTANCE test59a\n\
                 \t\tIN  y' = (M!xplus1 - 1) % 5\n\
                 ====\n",
            ),
        ],
    );
    let out = lower_in(&s, "test59.tla", "Next");
    // The LET's `x == y+1` is test59a's `VARIABLE x` implicit substitution,
    // so `M!xplus1` is `(y+1) + 1` – never test59a's own free `x`.
    assert!(
        out.contains("Prime(Var(Name(\"y\")))"),
        "the next-state relation: {out}"
    );
    assert!(
        !out.contains("Var(Name(\"x\"))"),
        "test59a's variable never appears free: {out}"
    );
    assert!(
        out.contains("Arith(Add, Arith(Add, Var(Name(\"y\")), Int(\"1\")), Int(\"1\"))"),
        "M!xplus1 is (y+1)+1: {out}"
    );
}
