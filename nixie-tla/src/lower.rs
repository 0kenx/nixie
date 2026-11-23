//! Lowering the surface tree to [`crate::kera`].
//!
//! # Shape of the walk
//!
//! `AGENTS.md` forbids new unbounded native recursion over user-controlled
//! input, and a surface tree parsed from a `.tla` file is exactly that. The
//! walk therefore carries its own stack, with resume state in the frame: a
//! an `Expand` frame pushes one kernel value, a `Build` frame pops the
//! children it asked for and pushes the node built from them, and scope frames
//! bracket the parts of a term where a binder or an inlined parameter is
//! visible.
//!
//! # Inlining
//!
//! Operator applications are inlined by *re-lowering the operator's body* with
//! its parameters bound to the already-lowered arguments, rather than by
//! building a term and substituting afterwards. That keeps one mechanism
//! instead of two, and it is what makes `LET` free: a `LET` definition is just
//! a binding in scope.
//!
//! Every binder is renamed to a unique name on the way down (`x` becomes
//! `x#3`), which removes variable capture as a concern entirely — an inlined
//! argument can mention any name at all and still cannot be captured by a
//! binder in the body it is substituted into.
//!
//! Recursive operators have no finite unfolding, so inlining is bounded and
//! reports [`crate::LowerErrorKind::InlineLimit`] rather than looping.

use crate::error::{LowerError, LowerErrorKind, Result};
use crate::kera::{ArithOp, CmpOp, FoldOver, Kera, KeraRef, Name, SetOp};
use nixie_tla_syntax::Span;
use nixie_tla_syntax::ast::{
    Bound, CaseArm, ExceptSel, Expr, ExprKind, Module, Pattern, QuantKind, Unit, UnitKind,
};
use std::collections::HashMap;
use std::rc::Rc;

/// Default maximum inlining depth.
pub const DEFAULT_MAX_INLINE_DEPTH: usize = 64;
/// Default budget, in steps of the lowering walk.
///
/// Bounds total work rather than nesting: inlining splices a body in at every
/// use, so a term can be enormous without being deep.
///
/// Set to fail *fast*. Inlining is memoised on the identity of an operator's
/// already-lowered arguments, which collapses the common
/// `F(x) == G(x) + G(x)` blowup, but the memo misses when two structurally
/// equal arguments are lowered separately and so are not pointer-identical.
/// A handful of corpus files (`test23.tla` and relatives, ~1.3% of
/// definitions) still exhaust the budget. Hash-consing the kernel would close
/// it properly; until then the budget keeps the failure to a prompt
/// diagnostic instead of an apparent hang.
pub const DEFAULT_STEP_BUDGET: usize = 100_000;

/// The built-in operator symbol a name denotes, if it is one that can be
/// passed as an operator argument. The AC, unambiguously-binary set —
/// Apalache's own `ToEtcExpr` accepts exactly these as first-class.
fn builtin_operator_symbol(name: &str) -> Option<&'static str> {
    match name {
        "+" => Some("+"),
        "*" => Some("*"),
        "\\cup" | "\\union" => Some("\\cup"),
        "\\cap" | "\\intersect" => Some("\\cap"),
        "\\/" => Some("\\/"),
        "/\\" => Some("/\\"),
        _ => None,
    }
}

/// A module instantiation: `I == INSTANCE M WITH a <- e`.
///
/// `EXTENDS` makes another module's definitions visible unchanged; `INSTANCE`
/// makes them visible *after substituting* for the declared constants and
/// variables of the instantiated module. That substitution is the whole
/// difference, and it is why an instance member cannot simply be inlined the
/// way an extended one can.
#[derive(Debug, Clone)]
struct Instantiation<'a> {
    module: &'a Module,
    /// The module where the instance was declared — the scope an implicit
    /// substitution (a declared name with no `WITH`) resolves against.
    /// `None` for a `LET`-scoped instance, whose declaring scope is whatever
    /// module the lowering walk is inside at the use site.
    source: Option<&'a Module>,
    /// Explicit `WITH` replacements, by the instantiated module's name.
    with: Vec<(String, &'a Expr)>,
    /// Parameters of a parameterised instance, `I(p) == INSTANCE M WITH …`.
    params: Vec<String>,
}

/// Where the replacement for one substituted name comes from.
#[derive(Debug, Clone)]
enum SubstSource<'a> {
    /// A surface expression to lower (`WITH v <- e`, or a same-named
    /// nullary definition visible at the instance).
    Expr(&'a Expr),
    /// An already-lowered kernel value (an enclosing instance's
    /// substitution, a `.cfg`-pinned constant, a declared variable).
    Value(KeraRef),
    /// A function definition `f[x \\in S] == e` visible at the instance,
    /// which denotes its function value.
    Fun(String, &'a [Bound], &'a Expr),
}

/// The instance being looked through while lowering.
///
/// Names inside an instantiated module's definition resolve against *that*
/// module and through *its* substitution, not against the module doing the
/// instantiating.
#[derive(Debug)]
struct InstanceCtx<'a> {
    module: &'a Module,
    subst: HashMap<String, KeraRef>,
}

/// A user operator definition available for inlining.
#[derive(Debug, Clone)]
struct Def<'a> {
    /// Parameter names with their arities. A non-zero arity marks a
    /// *higher-order* parameter: `Op(F(_), x)` takes an operator, not a value,
    /// and the argument has to be bound as an operator to be applied.
    params: Vec<(String, usize)>,
    body: &'a Expr,
    /// Whether the lowered form may be cached and shared.
    ///
    /// True for a module-level definition: TLA+ has no dynamic scoping, so a
    /// top-level body can only mention other top-level names, declared
    /// symbols and its own binders — its lowering does not depend on where it
    /// is used. False for a `LET` definition, whose name is scoped and may be
    /// shadowed.
    cacheable: bool,
}

/// Skolemize positive existentials over the **standard infinite sets**.
///
/// `\\E x \\in Nat : P(x)`, in a position the solver is asked to *satisfy*,
/// becomes a fresh constant `c` with `c \\in Nat /\\ P(c)` — Apalache's
/// `QuantRule.skolemExists` for the one domain family that needs it, since
/// the alternative is enumerating an infinite set. Only the standard
/// infinite sets are touched: a finite set's existential is already served
/// exactly by the arena's candidate instantiation, and skolemizing it would
/// *lose* precision for no gain.
///
/// **Polarity is soundness here.** An existential under an odd number of
/// negations is a universal claim (`\\A x \\in Nat : ...` is `~\\E x \\in
/// Nat : ~...`), and skolemizing that answers a different question; the
/// walk tracks polarity through `Not` and `Implies` arms, and the
/// both-polarity positions (`Equiv` arms, `Ite` conditions) are never
/// rewritten. A negative-position `\\A` over an infinite set becomes, by
/// the same reading, a positive `\\E` and **is** skolemized — after
/// rewriting `~\\A x : P` to `\\E x : ~P` by hand, which keeps one rule.
///
/// **The root polarity is the caller's to know.** `Init`, `Next` and the
/// constraint definitions are asserted as they stand — polarity true. An
/// invariant enters the solver **negated**, so its positive-position `\\E`
/// is the query's negative-position `\\E` (a universal claim, never
/// skolemized) and its positive-position `\\A` is the query's existential
/// (skolemized): callers pass `false` for the invariant role. Getting this
/// backwards was the first version of this pass, and it manufactured a
/// counterexample out of `\\E y \\in Nat : x < y` — the witness the model
/// picked made the *invariant* false, which is not what an existential
/// invariant means.
///
/// Walked with an explicit stack: the tree is user input. The rewrite
/// rebuilds only the spine it changed; shared subtrees are reused as they
/// are.
pub fn skolemize_infinite_existentials_at(root: &KeraRef, root_positive: bool) -> KeraRef {
    let counter = std::cell::RefCell::new(0usize);
    skolemize_walk(root, root_positive, &counter)
}

/// The walk proper, sharing one name counter with everything it spawns.
///
/// One counter per top-level pass is load-bearing: the rewritten body of a
/// skolemized quantifier is itself walked (through the cached form below),
/// and independently-numbered sub-walks would mint the same `%`-fresh or
/// `!skolem` name twice — two witnesses or binders the encoder would then
/// read as one.
fn skolemize_walk(
    root: &KeraRef,
    root_positive: bool,
    counter: &std::cell::RefCell<usize>,
) -> KeraRef {
    /// What a frame still owes.
    enum Frame<'a> {
        /// Visit a term at a polarity.
        Visit(&'a KeraRef, bool),
        /// All children visited; rebuild this node from the `n` rewritten
        /// children sitting on the value stack.
        Rebuild(&'a KeraRef, bool, usize),
        /// Insert a marker into the value stack (so children of different
        /// parents cannot interleave when a rewrite drops or adds pieces).
        Mark(usize),
    }

    let mut seen: std::collections::HashMap<(*const Kera, bool), KeraRef> =
        std::collections::HashMap::new();
    let mut stack: Vec<Frame> = vec![Frame::Visit(root, root_positive)];
    let mut values: Vec<KeraRef> = Vec::new();

    while let Some(frame) = stack.pop() {
        match frame {
            Frame::Visit(t, pos) => {
                // A lowered tree is a shared DAG: the same subterm can sit
                // under many parents. Visiting it once per parent would redo
                // (and re-copy) any rewrite inside it once per occurrence —
                // identical binder names in several nodes, which the
                // binder-uniqueness invariant exists to refuse. One result
                // per (node, polarity), shared by pointer, is both the fix
                // and the cheaper walk.
                if let Some(hit) = seen.get(&(Rc::as_ptr(t), pos)) {
                    values.push(Rc::clone(hit));
                    continue;
                }
                // The rewrite: a positive `\\E x \\in S : P` (or a negative
                // `\\A`) with `S` a standard infinite set.
                if pos
                    && let Kera::Exists { var, set, body } = t.as_ref()
                    && infinite_set_of(set).is_some()
                {
                    let mut c = counter.borrow_mut();
                    *c += 1;
                    let fresh = Name(format!("{var}!skolem{}", *c));
                    drop(c);
                    let member = Kera::In(Kera::Var(fresh.clone()).rc(), Rc::clone(set)).rc();
                    let renamed = alpha_refresh_binders(&rename_var(body, var, &fresh), counter);
                    let body =
                        skolemize_infinite_existentials_cached(&renamed, &mut seen, counter, true);
                    let out = Kera::And(vec![member, body]).rc();
                    seen.insert((Rc::as_ptr(t), pos), Rc::clone(&out));
                    values.push(out);
                    continue;
                }
                if !pos
                    && let Kera::Forall { var, set, body } = t.as_ref()
                    && infinite_set_of(set).is_some()
                {
                    // `~\\A x \\in S : P` is `\\E x \\in S : ~P`.
                    let mut c = counter.borrow_mut();
                    *c += 1;
                    let fresh = Name(format!("{var}!skolem{}", *c));
                    drop(c);
                    let member = Kera::In(Kera::Var(fresh.clone()).rc(), Rc::clone(set)).rc();
                    let neg_body = Kera::Not(Rc::clone(body)).rc();
                    let renamed =
                        alpha_refresh_binders(&rename_var(&neg_body, var, &fresh), counter);
                    let body =
                        skolemize_infinite_existentials_cached(&renamed, &mut seen, counter, true);
                    let out = Kera::Not(Kera::And(vec![member, body]).rc()).rc();
                    seen.insert((Rc::as_ptr(t), pos), Rc::clone(&out));
                    values.push(out);
                    continue;
                }
                // No rewrite: descend with the polarity each child carries.
                let n = t.as_ref().children().len();
                if n == 0 {
                    values.push(Rc::clone(t));
                    continue;
                }
                stack.push(Frame::Rebuild(t, pos, n));
                stack.push(Frame::Mark(values.len()));
                for (child, polarity) in children_with_polarity(t, pos).into_iter().rev() {
                    stack.push(Frame::Visit(child, polarity));
                }
            }
            Frame::Mark(m) => {
                // The value stack must hold exactly `m` entries below the
                // children this frame produced.
                debug_assert_eq!(values.len(), m);
            }
            Frame::Rebuild(t, pos, n) => {
                let kids: Vec<KeraRef> = values.split_off(values.len() - n);
                // Preserve sharing: if every child is the *same* `Rc` it was,
                // the node is unchanged and the original is returned — not a
                // structural copy. This is not an optimization: lowering
                // shares one inlined definition across its uses, the
                // binder-uniqueness invariant deduplicates by pointer, and a
                // rebuilt-everything pass would put one binder in two nodes
                // and trip that invariant where the source never did.
                let old_kids = t.as_ref().children();
                let unchanged = old_kids
                    .iter()
                    .zip(kids.iter())
                    .all(|(o, k)| std::rc::Rc::ptr_eq(o, k));
                let rebuilt = if unchanged {
                    Rc::clone(t)
                } else {
                    refresh_own_binders(rebuild(t, pos, &kids), counter)
                };
                seen.insert((Rc::as_ptr(t), pos), Rc::clone(&rebuilt));
                values.push(rebuilt);
            }
        }
    }
    values.pop().unwrap_or_else(|| Rc::clone(root))
}

/// [`skolemize_infinite_existentials_at`] at positive polarity — the form
/// for formulas asserted as they stand.
pub fn skolemize_infinite_existentials(root: &KeraRef) -> KeraRef {
    skolemize_infinite_existentials_at(root, true)
}

/// The cached recursive form used inside a rewrite (the rewritten body of a
/// skolemized existential is itself walked at positive polarity).
fn skolemize_infinite_existentials_cached(
    t: &KeraRef,
    seen: &mut std::collections::HashMap<(*const Kera, bool), KeraRef>,
    counter: &std::cell::RefCell<usize>,
    pos: bool,
) -> KeraRef {
    // Cheap outer reuse: a body already rewritten at this polarity is the
    // same term. (The full driver above does its own memoism by identity.)
    if let Some(hit) = seen.get(&(Rc::as_ptr(t), pos)) {
        return Rc::clone(hit);
    }
    let _ = pos;
    let out = skolemize_walk(t, true, counter);
    seen.insert((Rc::as_ptr(t), pos), Rc::clone(&out));
    out
}

/// Rename every binder in `t` to a globally new name.
///
/// A skolem rewrite copies the quantifier's body — `rename_var` rebuilds
/// the spine — and a lowered tree is a shared DAG: the same subterm can sit
/// under the copy *and* elsewhere in the original. Both copies would carry
/// the same binder names, and the binder-uniqueness invariant (rightly)
/// refuses the result. Refreshing every binder in the copied side, once,
/// with names from the pass's shared counter (`<old>%<n>`, a spelling the
/// lowerer never mints) keeps the copy's meaning and the invariant.
///
/// This is a true α-renaming — binder *fields* and their occurrences move
/// together — which [`rename_var`] alone is not: it substitutes free
/// occurrences and leaves binder fields verbatim, so using it here would
/// detach occurrences from their binders and keep the collision it was
/// meant to remove.
fn alpha_refresh_binders(t: &KeraRef, counter: &std::cell::RefCell<usize>) -> KeraRef {
    let mut binders: Vec<Name> = Vec::new();
    let mut visited: std::collections::HashSet<*const Kera> = std::collections::HashSet::new();
    let mut stack: Vec<&KeraRef> = vec![t];
    while let Some(x) = stack.pop() {
        if !visited.insert(Rc::as_ptr(x)) {
            continue;
        }
        for b in x.as_ref().binders() {
            binders.push(b.clone());
        }
        for c in x.as_ref().children() {
            stack.push(c);
        }
    }
    let mut renames: std::collections::HashMap<Name, Name> = std::collections::HashMap::new();
    for b in binders {
        let fresh = {
            let mut c = counter.borrow_mut();
            *c += 1;
            Name(format!("{b}%{}", *c))
        };
        renames.insert(b, fresh);
    }
    alpha_rename(t, &renames)
}

/// Refresh the binders *of this node itself* (not its descendants'), for a
/// node the walk rebuilt because a child changed.
///
/// The unchanged-children shortcut above returns the original pointer, so a
/// shared subterm stays shared. A rebuilt one is a *copy* that may coexist
/// with the original at another position (a definition inlined at two
/// polarities) — and the copy carries the node's binder. Renaming it, with
/// occurrences confined to this node, restores global uniqueness.
fn refresh_own_binders(t: KeraRef, counter: &std::cell::RefCell<usize>) -> KeraRef {
    let own: Vec<Name> = t.as_ref().binders().iter().map(|b| (*b).clone()).collect();
    if own.is_empty() {
        return t;
    }
    let mut renames: std::collections::HashMap<Name, Name> = std::collections::HashMap::new();
    for b in own {
        let fresh = {
            let mut c = counter.borrow_mut();
            *c += 1;
            Name(format!("{b}%{}", *c))
        };
        renames.insert(b, fresh);
    }
    alpha_rename(&t, &renames)
}

/// α-rename `t`: map binder fields *and* variable occurrences through
/// `renames`, preserving sharing.
///
/// A lowered term's binder names are globally unique, so a flat map is
/// capture-free by construction: no occurrence of a mapped name can be
/// under a *different* binder of the same spelling. The walk is explicit
/// (user-controlled depth), memoised by pointer (a shared DAG stays
/// shared), and returns the *original* `Rc` for any subtree with nothing to
/// rename — so unchanged parts keep their identity with the source tree,
/// which is what the binder-uniqueness invariant and the encoder's term
/// interning both rely on.
fn alpha_rename(t: &KeraRef, renames: &std::collections::HashMap<Name, Name>) -> KeraRef {
    if renames.is_empty() {
        return Rc::clone(t);
    }
    enum Frame<'a> {
        Visit(&'a KeraRef),
        Rebuild(&'a KeraRef, usize),
    }
    let mut memo: std::collections::HashMap<*const Kera, KeraRef> =
        std::collections::HashMap::new();
    let mut stack: Vec<Frame> = vec![Frame::Visit(t)];
    let mut values: Vec<KeraRef> = Vec::new();
    while let Some(frame) = stack.pop() {
        match frame {
            Frame::Visit(x) => {
                if let Some(hit) = memo.get(&Rc::as_ptr(x)) {
                    values.push(Rc::clone(hit));
                    continue;
                }
                if let Kera::Var(n) = x.as_ref()
                    && let Some(to) = renames.get(n)
                {
                    let out = Kera::Var(to.clone()).rc();
                    memo.insert(Rc::as_ptr(x), Rc::clone(&out));
                    values.push(out);
                    continue;
                }
                let n = x.as_ref().children().len();
                if n == 0 {
                    values.push(Rc::clone(x));
                    continue;
                }
                stack.push(Frame::Rebuild(x, n));
                for c in x.as_ref().children().into_iter().rev() {
                    stack.push(Frame::Visit(c));
                }
            }
            Frame::Rebuild(x, n) => {
                let kids: Vec<KeraRef> = values.split_off(values.len() - n);
                let old_kids = x.as_ref().children();
                let binders_renamed = x.as_ref().binders().iter().any(|b| renames.contains_key(b));
                let out = if !binders_renamed
                    && old_kids
                        .iter()
                        .zip(kids.iter())
                        .all(|(o, k)| Rc::ptr_eq(o, k))
                {
                    Rc::clone(x)
                } else {
                    rebuild_renamed(x, &kids, renames)
                };
                memo.insert(Rc::as_ptr(x), Rc::clone(&out));
                values.push(out);
            }
        }
    }
    values.pop().unwrap_or_else(|| Rc::clone(t))
}

/// Rename every occurrence of `from` in `t` to `to`.
///
/// The skolem rewrite's body substitution: `\E y \\in S : P(y)` becomes
/// `c \\in S /\\ P(c)`, and `P(y)` still speaks of `y` until this runs.
/// Walked with an explicit stack; the spine rebuild reuses [`rebuild`], so
/// one shape serves both passes.
fn rename_var(t: &KeraRef, from: &Name, to: &Name) -> KeraRef {
    enum Frame<'a> {
        Visit(&'a KeraRef),
        Rebuild(&'a KeraRef, usize),
    }
    // Memoised by pointer, and returning the *original* `Rc` wherever
    // nothing below changed: a lowered term is a shared DAG, and a rewrite
    // that copied per occurrence would put one binder name in several
    // nodes — the exact shape the binder-uniqueness invariant refuses.
    // Keeping the copy shared keeps the (unique) names unique.
    let mut memo: std::collections::HashMap<*const Kera, KeraRef> =
        std::collections::HashMap::new();
    let mut stack = vec![Frame::Visit(t)];
    let mut values: Vec<KeraRef> = Vec::new();
    while let Some(frame) = stack.pop() {
        match frame {
            Frame::Visit(x) => {
                if let Some(hit) = memo.get(&Rc::as_ptr(x)) {
                    values.push(Rc::clone(hit));
                    continue;
                }
                if matches!(x.as_ref(), Kera::Var(n) if n == from) {
                    values.push(Kera::Var(to.clone()).rc());
                    continue;
                }
                let n = x.as_ref().children().len();
                if n == 0 {
                    values.push(Rc::clone(x));
                    continue;
                }
                stack.push(Frame::Rebuild(x, n));
                for c in x.as_ref().children().into_iter().rev() {
                    stack.push(Frame::Visit(c));
                }
            }
            Frame::Rebuild(x, n) => {
                let kids: Vec<KeraRef> = values.split_off(values.len() - n);
                let old_kids = x.as_ref().children();
                let rebuilt = if old_kids
                    .iter()
                    .zip(kids.iter())
                    .all(|(o, k)| Rc::ptr_eq(o, k))
                {
                    Rc::clone(x)
                } else {
                    rebuild(x, true, &kids)
                };
                memo.insert(Rc::as_ptr(x), Rc::clone(&rebuilt));
                values.push(rebuilt);
            }
        }
    }
    values.pop().unwrap_or_else(|| Rc::clone(t))
}

/// [`rebuild`] with the node's binder fields mapped through `renames`.
///
/// Only the binder-carrying kinds differ; everything else is [`rebuild`]
/// exactly. Binder fields and their occurrences are renamed *together* by
/// the caller ([`alpha_rename`]) — renaming one without the other is how a
/// bound occurrence becomes a free variable wearing the wrong name.
fn rebuild_renamed(
    t: &KeraRef,
    kids: &[KeraRef],
    renames: &std::collections::HashMap<Name, Name>,
) -> KeraRef {
    let k = |i: usize| Rc::clone(&kids[i]);
    let mv = |n: &Name| renames.get(n).cloned().unwrap_or_else(|| n.clone());
    match t.as_ref() {
        Kera::Forall { var, .. } => Kera::Forall {
            var: mv(var),
            set: k(0),
            body: k(1),
        }
        .rc(),
        Kera::Exists { var, .. } => Kera::Exists {
            var: mv(var),
            set: k(0),
            body: k(1),
        }
        .rc(),
        Kera::Choose { var, .. } => Kera::Choose {
            var: mv(var),
            set: k(0),
            body: k(1),
        }
        .rc(),
        Kera::ChooseUnbounded { var, .. } => Kera::ChooseUnbounded {
            var: mv(var),
            body: k(0),
        }
        .rc(),
        Kera::RecFun { name, var, .. } => Kera::RecFun {
            name: mv(name),
            var: mv(var),
            set: k(0),
            body: k(1),
        }
        .rc(),
        Kera::FunDef { var, .. } => Kera::FunDef {
            var: mv(var),
            set: k(0),
            body: k(1),
        }
        .rc(),
        Kera::Filter { var, .. } => Kera::Filter {
            var: mv(var),
            set: k(0),
            pred: k(1),
        }
        .rc(),
        Kera::Map { var, .. } => Kera::Map {
            var: mv(var),
            set: k(0),
            expr: k(1),
        }
        .rc(),
        Kera::Fold {
            over, acc, elem, ..
        } => {
            let (base, collection, body) = (k(0), k(1), k(2));
            Kera::Fold {
                over: *over,
                acc: mv(acc),
                elem: mv(elem),
                base,
                collection,
                body,
            }
            .rc()
        }
        _ => rebuild(t, true, kids),
    }
}

/// The standard infinite sets, as membership domains a skolem can be
/// constrained by. `Real` is excluded: the front end has no reals.
fn infinite_set_of(set: &KeraRef) -> Option<&'static str> {
    let name = match set.as_ref() {
        Kera::Var(n) => n.as_str(),
        Kera::Opaque(n, args) if args.is_empty() => n.as_str(),
        _ => return None,
    };
    match name {
        "Nat" | "Int" | "STRING" | "BOOLEAN" => Some(match name {
            "Nat" => "Nat",
            "Int" => "Int",
            "STRING" => "STRING",
            _ => "BOOLEAN",
        }),
        _ => None,
    }
}

/// Each child of `t` with the polarity it inherits at `pos`.
fn children_with_polarity(t: &KeraRef, pos: bool) -> Vec<(&KeraRef, bool)> {
    let kids = t.as_ref().children();
    match t.as_ref() {
        // `Not` flips.
        Kera::Not(_) => kids.into_iter().map(|k| (k, !pos)).collect(),
        // The kernel spells `a => b` as `~a \/ b`, so an `Or` containing a
        // `Not`-headed disjunct is implication-shaped: the `Not` arm flips.
        // (Lowering builds exactly this shape for `=>`.)
        Kera::Or(_) => kids
            .into_iter()
            .map(|k| {
                let polarity = match k.as_ref() {
                    Kera::Not(_) => !pos,
                    _ => pos,
                };
                (k, polarity)
            })
            .collect(),
        // An `Ite` condition holds at *both* polarities: never rewritten,
        // never trusted. The arms inherit the position's polarity.
        Kera::Ite(c, a, b) => vec![(c, false), (a, pos), (b, pos)],
        _ => kids.into_iter().map(|k| (k, pos)).collect(),
    }
}

/// Rebuild `t` from rewritten children, preserving the node's meaning.
fn rebuild(t: &KeraRef, _pos: bool, kids: &[KeraRef]) -> KeraRef {
    let k = |i: usize| Rc::clone(&kids[i]);
    let rebuilt = match t.as_ref() {
        Kera::Prime(_) => Kera::Prime(k(0)),
        Kera::Not(_) => Kera::Not(k(0)),
        Kera::Powerset(_) => Kera::Powerset(k(0)),
        Kera::BigUnion(_) => Kera::BigUnion(k(0)),
        Kera::Domain(_) => Kera::Domain(k(0)),
        Kera::Neg(_) => Kera::Neg(k(0)),
        Kera::And(_) => Kera::And(kids.to_vec()),
        Kera::Or(_) => Kera::Or(kids.to_vec()),
        Kera::SetEnum(_) => Kera::SetEnum(kids.to_vec()),
        Kera::Tuple(_) => Kera::Tuple(kids.to_vec()),
        Kera::Times(_) => Kera::Times(kids.to_vec()),
        Kera::Ite(_, _, _) => Kera::Ite(k(0), k(1), k(2)),
        Kera::Forall { var, .. } => Kera::Forall {
            var: var.clone(),
            set: k(0),
            body: k(1),
        },
        Kera::Exists { var, .. } => Kera::Exists {
            var: var.clone(),
            set: k(0),
            body: k(1),
        },
        Kera::Choose { var, .. } => Kera::Choose {
            var: var.clone(),
            set: k(0),
            body: k(1),
        },
        Kera::ChooseUnbounded { var, .. } => Kera::ChooseUnbounded {
            var: var.clone(),
            body: k(0),
        },
        Kera::RecFun { name, var, .. } => Kera::RecFun {
            name: name.clone(),
            var: var.clone(),
            set: k(0),
            body: k(1),
        },
        Kera::FunDef { var, .. } => Kera::FunDef {
            var: var.clone(),
            set: k(0),
            body: k(1),
        },
        Kera::Filter { var, .. } => Kera::Filter {
            var: var.clone(),
            set: k(0),
            pred: k(1),
        },
        Kera::Map { var, .. } => Kera::Map {
            var: var.clone(),
            set: k(0),
            expr: k(1),
        },
        Kera::Eq(_, _) => Kera::Eq(k(0), k(1)),
        Kera::In(_, _) => Kera::In(k(0), k(1)),
        Kera::SetBin(op, _, _) => Kera::SetBin(*op, k(0), k(1)),
        Kera::Range(_, _) => Kera::Range(k(0), k(1)),
        Kera::FunApp(_, _) => Kera::FunApp(k(0), k(1)),
        Kera::Arith(op, _, _) => Kera::Arith(*op, k(0), k(1)),
        Kera::Cmp(op, _, _) => Kera::Cmp(*op, k(0), k(1)),
        Kera::Except { .. } => Kera::Except {
            fun: k(0),
            index: k(1),
            value: k(2),
        },
        Kera::FunSet { .. } => Kera::FunSet {
            set: k(0),
            cod: k(1),
        },
        Kera::Record(fs) => Kera::Record(
            fs.iter()
                .zip(kids.iter())
                .map(|((n, _), v)| (n.clone(), Rc::clone(v)))
                .collect(),
        ),
        Kera::RecordSet(fs) => Kera::RecordSet(
            fs.iter()
                .zip(kids.iter())
                .map(|((n, _), v)| (n.clone(), Rc::clone(v)))
                .collect(),
        ),
        Kera::Fold {
            over, acc, elem, ..
        } => {
            let (base, collection, body) = (k(0), k(1), k(2));
            Kera::Fold {
                over: *over,
                acc: acc.clone(),
                elem: elem.clone(),
                base,
                collection,
                body,
            }
        }
        Kera::Opaque(n, _) => Kera::Opaque(n.clone(), kids.to_vec()),
        // Literals and names have no children; the visitor never rebuilds them.
        Kera::Var(_) | Kera::Int(_) | Kera::Str(_) | Kera::Bool(_) => {
            return Rc::clone(t);
        }
    };
    rebuilt.rc()
}

/// Whether every binder in a lowered tree is unique.
///
/// Lowering's invariant: each binder gets a fresh name, so substitution is
/// capture-free and inference can key bound variables by name alone. A
/// repeated binder breaks both silently — two independent variables read as
/// one — which is exactly how `EmptyBag`'s fixed `bag_e#0` made every bag in
/// a specification share one element type. Checked over the whole tree with
/// an explicit stack and pointer deduplication (a lowered term is a shared
/// DAG).
///
/// Public so the checker and the corpus harness can assert it too.
pub fn binder_uniqueness(root: &KeraRef) -> core::result::Result<(), String> {
    let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut visited: std::collections::HashSet<*const Kera> = std::collections::HashSet::new();
    let mut stack: Vec<&KeraRef> = vec![root];
    while let Some(t) = stack.pop() {
        if !visited.insert(std::rc::Rc::as_ptr(t)) {
            continue;
        }
        for name in t.as_ref().binders() {
            if !seen.insert(name.as_str().to_string()) {
                return Err(format!(
                    "the binder `{name}` occurs more than once: two independent variables \
                     would read as one in inference, substitution and encoding"
                ));
            }
        }
        stack.extend(t.as_ref().children());
    }
    Ok(())
}

/// Why a configuration replacement could not be applied.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ReplaceError {
    /// The right-hand side names nothing this lowerer has.
    #[error("`{0}` is not defined in this specification")]
    NoSuchDefinition(String),
    /// The two definitions take different numbers of parameters.
    #[error("`{name}` takes {wanted} parameter(s) but `{with}` takes {found}")]
    ArityMismatch {
        /// The name being replaced.
        name: String,
        /// Its arity.
        wanted: usize,
        /// The replacement.
        with: String,
        /// The replacement's arity.
        found: usize,
    },
}

/// What a name is bound to while lowering.
#[derive(Debug, Clone)]
enum Binding<'a> {
    /// A built-in operator symbol passed as an argument — `FooBar(7, +)`.
    /// No surface body exists to inline, so the application site lowers
    /// `Op(a, b)` through the ordinary operator table under a two-name
    /// scope: the exact meaning of the symbol, with none of the guessing a
    /// synthesized body would invite.
    BuiltinOp(&'static str),
    /// An inlined value: an operator parameter, a `LET` definition, or a
    /// component of a destructured tuple pattern.
    Value(KeraRef),
    /// A renamed bound variable.
    Bound(Name),
    /// An operator passed as an argument — a named definition or a `LAMBDA`.
    /// Bound rather than lowered, because an operator has no value until it is
    /// applied.
    Op {
        /// Its parameters, with arities.
        params: Vec<(String, usize)>,
        /// Its body.
        body: &'a Expr,
    },
}

/// Lowers surface expressions to the kernel.
pub struct Lowerer<'a> {
    defs: HashMap<String, Def<'a>>,
    /// Values a TLC configuration pinned, `CONSTANT N = 3`.
    ///
    /// Already-lowered kernel terms rather than surface expressions: they come
    /// from a `.cfg`, which has no TLA+ syntax tree behind it, and they are
    /// closed constants so there is nothing to resolve in them.
    constants: HashMap<String, KeraRef>,
    /// Per-module definitions, so a name inside an instantiated module
    /// resolves against that module rather than against the flat root view.
    module_defs: HashMap<String, HashMap<String, Def<'a>>>,
    /// Named instantiations, `I == INSTANCE M …`.
    instances: HashMap<String, Instantiation<'a>>,
    /// Unnamed `INSTANCE M …`, whose members are visible without a prefix.
    open_instances: Vec<Instantiation<'a>>,
    /// The instance contexts currently being looked through, innermost last.
    ctx: Vec<Rc<InstanceCtx<'a>>>,
    /// Function definitions `f[x \in S] == e`, which denote a *value* rather
    /// than an operator and so are expanded as `[x \in S |-> e]` at use sites.
    funs: HashMap<String, (&'a [Bound], &'a Expr)>,
    /// Function definitions currently being lowered, so a reference to one
    /// from inside its own body is *kept* rather than expanded again.
    ///
    /// `Fib[k \in 0..15] == … Fib[k-1] …` is ordinary TLA+ and needs no
    /// `RECURSIVE` keyword. Expanding it reproduces the body inside itself and
    /// the only thing that stops is the lowering budget.
    recursing: std::collections::HashSet<String>,
    scopes: Vec<HashMap<String, Binding<'a>>>,
    /// Binder names chosen during `expand`, keyed by the surface node's start
    /// offset so that `build` can recover them. The walk visits each node's
    /// expand and build exactly once, so one entry per node suffices.
    binder_names: HashMap<u32, Vec<Name>>,
    /// Lowered forms of nullary module-level definitions.
    ///
    /// Inlining re-lowers a body at every use, so `A == B + B` with
    /// `B == C + C` doubles at each level and a chain of a dozen such
    /// definitions is exponential. Sharing the `Rc` collapses that back to
    /// linear, and is sound precisely because a top-level body's meaning does
    /// not depend on where it is used.
    cache: HashMap<String, KeraRef>,
    /// Every loaded module by name, for resolving `INSTANCE`.
    modules: HashMap<String, &'a Module>,
    /// Higher-order arguments resolved by `expand`, keyed by the application's
    /// start offset, waiting for the matching `Inline` frame.
    pending_ops: HashMap<u32, Vec<(String, Binding<'a>)>>,
    /// Names declared `RECURSIVE`, plus definitions that mention
    /// themselves — the inline limit on either is a recursion diagnostic,
    /// not a depth one.
    recursive_names: std::collections::HashSet<String>,
    /// `INSTANCE` targets that could not be resolved, with their spans —
    /// reported once, after `add_spec`, rather than silently dropped.
    missing_instances: Vec<(String, Span)>,
    /// The module whose member the walk is lowering — the scope a
    /// `LET`-scoped instance's implicit substitutions resolve against when
    /// no instance context is open.
    lower_module: Option<&'a Module>,
    fresh: usize,
    inline_depth: usize,
    max_inline_depth: usize,
    step_budget: usize,
}

/// A step of the lowering walk.
enum Frame<'a> {
    Expand(&'a Expr),
    /// Pop `n` kernel values and build this surface node from them.
    Build(&'a Expr, usize),
    PushScope(HashMap<String, Binding<'a>>),
    PopScope,
    /// Bind `@` to the value being replaced, for an `EXCEPT` update. Peeks the
    /// function and index already on the value stack rather than popping them.
    BindExceptAt {
        /// How many index expressions make up this update's path step.
        path_len: usize,
        /// The path lengths of the updates *before* this one, in order.
        ///
        /// Needed for both halves of what `@` means in a multi-update
        /// `EXCEPT`. It locates the function on the shared value stack — which
        /// is not a fixed distance below the top, because each earlier update
        /// left its own indices and value there — and it rebuilds the
        /// partially-updated function that `@` actually refers to.
        before: Vec<usize>,
    },
    /// Inline an operator: pop one value per parameter, bind them, and
    /// continue into `body`.
    Inline {
        name: String,
        params: Vec<(String, usize)>,
        body: &'a Expr,
        span: Span,
        /// Cache the result under this name once the body is lowered.
        cache_as: Option<String>,
    },
    /// Leave an inlined body: drop its scope and the depth it consumed.
    PopInline,
    /// Expand a function definition's `bounds`/`body` as `[x \in S |-> e]`.
    ///
    /// The name is carried so a reference to the function from inside its own
    /// body can be recognised and kept.
    ExpandFun(String, &'a [Bound], &'a Expr),
    /// Stop treating this name as being lowered.
    PopRecursion(String),
    /// Build `BagOfAll(F, B)` from `2` values: `B` first, then `F(elem)`
    /// under a scope binding `F`'s parameter to the fold's element name. The
    /// result is the Apalache rewire in kernel form:
    /// `ApaFoldSet(\\partial, elem => partial (+) [y \\in {F(elem)} |-> B[elem]],
    ///  EmptyBag, DOMAIN B)` — a fold whose step adds one singleton bag, so
    /// the order of the fold is immaterial (bag addition is commutative and
    /// associative, being pointwise `+`).
    BuildBagOfAll {
        /// The fold's accumulator name (the partial bag).
        acc: Name,
        /// The fold's element name.
        elem: Name,
        /// The result function's binder (the mapped-to value `F(elem)`).
        out: Name,
    },
    /// Build `SelectSeq(seq, F(_))` from `1` value: `F(elem)` under a scope
    /// binding `F`'s parameter to the fold's element name. Apalache's own
    /// rewire, in kernel form:
    /// `ApaFoldSeqLeft((s, e) => IF F(e) THEN Append(s, e) ELSE s, <<>>, seq)`.
    BuildSelectSeq {
        /// The fold's accumulator name (the growing sequence).
        acc: Name,
        /// The fold's element name.
        elem: Name,
    },
    /// Build `sym(x, y)` for a built-in operator symbol passed as an
    /// argument: two values on the stack, one infix table lookup.
    BuildBuiltinOp {
        /// The binary operator's canonical spelling.
        sym: &'static str,
        /// For diagnostics.
        span: Span,
    },
    /// Push one prebuilt kernel value. For interceptions that synthesize a
    /// kernel term the surface never wrote (`Repeat`'s `<<1..N>>`).
    Kera(KeraRef),
    /// Bind a mapped fold's operator parameters: pop the lowered mapping
    /// function, bind `p0` to `map[x]` and `p1` to the accumulator, and
    /// enter that scope for the operator body.
    BindMappedFold {
        /// The operator's element parameter, bound to `fun[elem]`.
        p0: String,
        /// The operator's accumulator parameter.
        p1: String,
        /// The fold's element binder.
        elem: Name,
        /// The fold's accumulator binder.
        acc: Name,
        /// The collection: `DOMAIN fun` when `None`, the surface index set
        /// otherwise.
        indices: Option<&'a Expr>,
    },
    /// Build `FunAsSeq(f, len)` from the lowered `f` (below) and `len`
    /// (top): `Opaque("FunAsSeq", [f, len])`, for the encoder's window
    /// construction.
    BuildFunAsSeq,
    /// Build `MkSeq` from the mapped body: the `[i \\in 1..n |-> body]`
    /// function constructor over the literal range.
    BuildMkSeq {
        /// The domain binder (the operator's parameter).
        var: Name,
        /// The literal length.
        n: i128,
    },
    /// Build a fold from `3` values (base, collection, operator body).
    BuildFold {
        /// Whether the collection is a set or a sequence.
        over: FoldOver,
        /// The name the operator's accumulator parameter was renamed to.
        acc: Name,
        /// The name its element parameter was renamed to.
        elem: Name,
    },
    /// Build that function definition from `domains + 1` values: one term per
    /// bound variable's domain, then the body. Several domains become a
    /// product, matching `[x \in S, y \in T |-> e]`.
    BuildFun {
        /// The variable the function binds.
        var: Name,
        /// How many domains are on the value stack.
        domains: usize,
        /// The name the body refers to itself by, when it does.
        recursive: Option<Name>,
    },
    /// Restore operator definitions shadowed by a `LET`, and any `LET`-scoped
    /// instances (`LET M == INSTANCE A IN …`) with the module-level bindings
    /// they shadowed, in the same order.
    PopLetDefs(
        Vec<(String, Option<Def<'a>>)>,
        Vec<(String, Option<Instantiation<'a>>)>,
    ),
    /// Push a ready-made kernel value (a record field name in an `EXCEPT`
    /// path, which has no surface expression of its own).
    PushLiteral(KeraRef),
    /// Pop `n` values and push them as one tuple. Used for a multi-argument
    /// `EXCEPT` selector, `![i, j]`, which is one index and not two.
    BuildTuple(usize),
    /// Enter an instance: pop the lowered `WITH` replacements and the member's
    /// arguments, and look through the instantiated module under them.
    PushInstanceCtx {
        module: &'a Module,
        /// Names the popped substitution values belong to, in order — every
        /// substituted name, `WITH` and implicit alike.
        subst_names: Vec<String>,
        /// The member's own parameters, bound to the popped arguments.
        member_params: Vec<(String, usize)>,
    },
    /// Leave an instance.
    PopInstanceCtx,
    /// Remember the lowered form of a nullary module-level definition.
    CacheStore(String),
}

impl<'a> Lowerer<'a> {
    /// A lowerer with no definitions in scope.
    #[must_use]
    pub fn new() -> Self {
        Self {
            defs: HashMap::new(),
            constants: HashMap::new(),
            module_defs: HashMap::new(),
            instances: HashMap::new(),
            open_instances: Vec::new(),
            ctx: Vec::new(),
            funs: HashMap::new(),
            recursing: std::collections::HashSet::new(),
            scopes: Vec::new(),
            binder_names: HashMap::new(),
            cache: HashMap::new(),
            modules: HashMap::new(),
            pending_ops: HashMap::new(),
            missing_instances: Vec::new(),
            lower_module: None,
            recursive_names: std::collections::HashSet::new(),
            fresh: 0,
            inline_depth: 0,
            max_inline_depth: DEFAULT_MAX_INLINE_DEPTH,
            step_budget: DEFAULT_STEP_BUDGET,
        }
    }

    /// Pin `name` to a constant value, as a TLC configuration's
    /// `CONSTANT name = value` does.
    ///
    /// A substitution, not an assumption. TLC's own description is "replace
    /// the constant in the left-hand side with the constant expression in the
    /// right-hand side", and the difference is load-bearing rather than
    /// stylistic: an assumption `N = 3` reaches the solver, but the *encoder*
    /// needs the value earlier than that — `1..N` has no candidate list until
    /// `N` is literally `3`, and no amount of solver-level knowledge supplies
    /// one.
    ///
    /// Shadowed by any binder of the same name, and it wins over a definition
    /// of that name, which is the order TLC uses.
    pub fn bind_constant(&mut self, name: &str, value: KeraRef) {
        self.cache.remove(name);
        self.constants.insert(name.to_string(), value);
    }

    /// Rebind `name` to the definition of `with`, as a TLC configuration's
    /// `name <- with` does.
    ///
    /// This is how a model-checking harness makes an infinite specification
    /// finite: `MCPaxos` replaces `Ballot` — declared a `CONSTANT`, or defined
    /// as `Nat` — with `MCBallot == 0..2`. It is a rebinding of the flat name
    /// space rather than a substitution pass, which is exactly what TLC does
    /// and what makes it work for a `CONSTANT` as well as a definition: a
    /// declared constant has no entry here, so adding one turns a name that
    /// was free into one that inlines.
    ///
    /// # Errors
    ///
    /// Fails if `with` is not defined, or if the two have different arities.
    /// An arity mismatch is a malformed configuration, and substituting across
    /// one would produce a term that means nothing — so it is reported rather
    /// than coerced. A `name` that is not itself defined is *not* an error: it
    /// is the ordinary case of replacing a declared `CONSTANT`.
    pub fn replace_definition(
        &mut self,
        name: &str,
        with: &str,
    ) -> core::result::Result<(), ReplaceError> {
        let Some(def) = self.defs.get(with).cloned() else {
            return Err(ReplaceError::NoSuchDefinition(with.to_string()));
        };
        if let Some(old) = self.defs.get(name)
            && old.params.len() != def.params.len()
        {
            return Err(ReplaceError::ArityMismatch {
                name: name.to_string(),
                wanted: old.params.len(),
                with: with.to_string(),
                found: def.params.len(),
            });
        }
        // The cache is keyed by name and holds the *previous* body's lowering,
        // so it has to go or the replacement silently does nothing.
        self.cache.remove(name);
        self.defs.insert(name.to_string(), def);
        Ok(())
    }

    /// Register every operator definition in `module` for inlining.
    ///
    /// Definitions are registered in source order, so a later definition can
    /// use an earlier one — which is all TLA+ permits anyway.
    pub fn add_module(&mut self, module: &'a Module) {
        self.index_module(module);
        for unit in &module.units {
            self.add_unit(unit);
        }
    }

    /// Index a module without making its definitions visible.
    ///
    /// Visibility is the whole point of the distinction. A module reached only
    /// through `INSTANCE` must **not** contribute to the flat name space: its
    /// definitions mean something only under that instance's substitution, and
    /// letting them resolve directly would silently use the *unsubstituted*
    /// body — reading the wrong module's variables.
    pub fn index_module(&mut self, module: &'a Module) {
        self.modules.insert(module.name.name.clone(), module);
        // Nested modules are registered in their own right, and FIRST:
        // `I == INSTANCE inner` names one, and an `INSTANCE` unit in this
        // module resolves its target while `add_instance_unit` walks the
        // units below. Before this they were silently invisible — the
        // instance target was never found and `add_instance_unit` returned
        // quietly, the exact silent-gap shape this codebase refuses
        // elsewhere. Registering is safe because an instance target
        // resolves *only* through the instance machinery: a nested module's
        // definitions never join the flat name space.
        for unit in &module.units {
            if let UnitKind::Submodule(sub) = &unit.kind {
                self.index_module(sub);
            }
        }
        for unit in &module.units {
            self.add_instance_unit(module, unit);
        }
        // A per-module view, so that a definition reached through an instance
        // resolves its own module's names rather than the root's.
        let mut own: HashMap<String, Def<'a>> = HashMap::new();
        for unit in &module.units {
            if let UnitKind::OpDef {
                name, params, body, ..
            } = &unit.kind
            {
                own.insert(
                    name.name.clone(),
                    Def {
                        params: params
                            .iter()
                            .map(|p| (p.name.name.clone(), p.arity))
                            .collect(),
                        body,
                        cacheable: true,
                    },
                );
            }
        }
        self.module_defs.insert(module.name.name.clone(), own);
    }

    fn add_instance_unit(&mut self, module: &'a Module, unit: &'a Unit) {
        let (name, params, instance) = match &unit.kind {
            UnitKind::ModuleDef {
                name,
                params,
                instance,
                ..
            } => (
                Some(name.name.clone()),
                params.iter().map(|p| p.name.name.clone()).collect(),
                instance,
            ),
            UnitKind::Instance { instance, .. } => (None, Vec::new(), instance),
            _ => return,
        };
        let Some(target) = self.modules.get(&instance.module.name).copied() else {
            // The instantiated module was not loaded. That is an error to
            // report *now*, at registration, with the instance's own span —
            // a use of it would fail much later with a name error that
            // points at the use, not at the cause. (The previous behaviour
            // — return quietly and let a use fail — is exactly the
            // silent-fallthrough class AGENTS.md opens with.)
            self.missing_instances
                .push((instance.module.name.clone(), unit.span));
            return;
        };
        let inst = Instantiation {
            module: target,
            source: Some(module),
            with: instance
                .substitutions
                .iter()
                .map(|(n, e)| (n.name.clone(), e))
                .collect(),
            params,
        };
        match name {
            Some(n) => {
                self.instances.insert(n, inst);
            }
            None => self.open_instances.push(inst),
        }
    }

    fn add_unit(&mut self, unit: &'a Unit) {
        match &unit.kind {
            UnitKind::OpDef {
                name, params, body, ..
            } => {
                self.defs.insert(
                    name.name.clone(),
                    Def {
                        params: params
                            .iter()
                            .map(|p| (p.name.name.clone(), p.arity))
                            .collect(),
                        body,
                        cacheable: true,
                    },
                );
            }
            // A function definition `f[x \in S] == e` denotes the function
            // itself, not an operator, so it is expanded as `[x \in S |-> e]`
            // wherever `f` is used.
            UnitKind::FnDef {
                name, bounds, body, ..
            } => {
                self.funs
                    .insert(name.name.clone(), (bounds.as_slice(), body));
            }
            UnitKind::ConstantDecl(_)
            | UnitKind::VariableDecl(_)
            | UnitKind::Recursive(_)
            | UnitKind::Extends(_)
            | UnitKind::Instance { .. }
            | UnitKind::ModuleDef { .. }
            | UnitKind::Assume { .. }
            | UnitKind::Theorem { .. }
            | UnitKind::ProofDirective(_)
            | UnitKind::Separator
            | UnitKind::Submodule(_) => {}
        }
    }

    /// Register every module of a loaded spec, dependency-first.
    ///
    /// Without this a spec's imports are invisible and `Sequences`' `\o`,
    /// `TLC`'s `:>` and every operator a module extends fail to lower. The
    /// order matters: `LoadedSpec::modules` is dependency-first, so the root's
    /// own definitions are registered last and shadow anything it extends —
    /// which is what TLA+ means by overriding.
    /// The \`INSTANCE\` targets that could not be resolved, with their
    /// spans. Empty is the good case; a non-empty list is the caller's to
    /// report, because it names a defect in the specification (a module
    /// that was never defined), not a limitation of the checker.
    #[must_use]
    pub fn missing_instances(&self) -> &[(String, Span)] {
        &self.missing_instances
    }

    /// Note every `RECURSIVE`-declared name and every self-referential
    /// definition, so the inline limit can name recursion as the cause.
    fn collect_recursive(&mut self, module: &'a Module) {
        for unit in &module.units {
            if let UnitKind::Recursive(decls) = &unit.kind {
                for d in decls {
                    self.recursive_names.insert(d.name.name.clone());
                }
            }
            if let UnitKind::OpDef { name, body, .. } = &unit.kind
                && mentions_name(body, &name.name)
            {
                self.recursive_names.insert(name.name.clone());
            }
            if let UnitKind::Submodule(sub) = &unit.kind {
                self.collect_recursive(sub);
            }
        }
    }

    /// Index every module of a loaded specification: modules first, then
    /// instances, then the recursion census. Called once per
    /// []; a second call would re-register the same names, which
    /// is harmless but wasted.
    pub fn add_spec(&mut self, spec: &'a nixie_tla_syntax::LoadedSpec) {
        // Two passes: every module must be findable before any `INSTANCE` is
        // resolved, since a module may instantiate one that appears later.
        for (name, module) in &spec.modules {
            self.modules.insert(name.clone(), module);
        }
        for (_, module) in &spec.modules {
            self.index_module(module);
            self.collect_recursive(module);
        }
        // Only the root and what it *extends* contribute visible names.
        // `EXTENDS` re-exports, so the closure is taken transitively; an
        // `INSTANCE` target reached along the way does not join it.
        let mut visible: Vec<&str> = vec![spec.root.as_str()];
        let mut i = 0;
        while i < visible.len() {
            let Some((_, m)) = spec.modules.iter().find(|(n, _)| n == visible[i]) else {
                i += 1;
                continue;
            };
            for dep in m.extends() {
                if !visible.iter().any(|v| *v == dep.name) {
                    visible.push(&dep.name);
                }
            }
            i += 1;
        }
        // Dependency-first, so the root's own definitions are registered last
        // and shadow anything it extends — which is what overriding means.
        for (name, module) in &spec.modules {
            if visible.iter().any(|v| *v == name) {
                for unit in &module.units {
                    self.add_unit(unit);
                }
            }
        }
    }

    /// Lower the body of the named top-level definition.
    ///
    /// # Errors
    ///
    /// Returns [`LowerErrorKind::Unsupported`] if there is no such definition,
    /// or the first lowering error.
    /// Whether `name` is a nullary member of some **unnamed** instance —
    /// visible unprefixed, which is what a role names.
    #[must_use]
    pub fn open_instances_visible(&self, name: &str) -> bool {
        self.open_instances.iter().any(|i| {
            self.module_defs
                .get(&i.module.name.name)
                .is_some_and(|m| m.get(name).is_some_and(|d| d.params.is_empty()))
        })
    }

    /// Lower the body of the named top-level definition — a unit of this
    /// module, or a member of one of its **unnamed** instances (visible
    /// unprefixed, which is what a role names).
    ///
    /// # Errors
    ///
    /// Returns [`LowerErrorKind::Unsupported`] if there is no such definition,
    /// or the first lowering error.
    pub fn lower_named(&mut self, module: &'a Module, name: &str) -> Result<KeraRef> {
        self.lower_module = Some(module);
        let found = module.units.iter().find_map(|u| match &u.kind {
            UnitKind::OpDef { name: n, body, .. } if n.name == name => Some(body),
            _ => None,
        });
        if let Some(body) = found {
            return self.lower(body);
        }
        // A member of an **unnamed** instance is visible unprefixed, so a
        // role may name it (`--inv=Safety` with `INSTANCE y2k WITH …`):
        // lower it through the instance machinery, substitution and all —
        // exactly what a bare use of the name inside a body does.
        let inst = self
            .open_instances
            .iter()
            .position(|i| {
                self.module_defs
                    .get(&i.module.name.name)
                    .is_some_and(|m| m.contains_key(name))
            })
            .map(|ix| self.open_instances[ix].clone());
        if let Some(inst) = inst {
            let mut stack: Vec<Frame<'a>> = Vec::new();
            self.push_instance_body(
                &inst,
                name,
                &[],
                nixie_tla_syntax::Span::default(),
                &mut stack,
            )?;
            return self.run_frames(stack, nixie_tla_syntax::Span::default());
        }
        Err(LowerError::unsupported(
            &format!("`{name}`"),
            "no operator definition with that name in this module (or its open instances)",
            nixie_tla_syntax::Span::default(),
        ))
    }

    /// Override the inlining depth budget.
    #[must_use]
    pub fn with_max_inline_depth(mut self, n: usize) -> Self {
        self.max_inline_depth = n;
        self
    }

    /// The `Bags` standard-module vocabulary, desugared to the module's own
    /// definitions (`Bags.tla`, tla2tools) as kernel nodes — the same macro
    /// expansion TLA+ itself gives these operators. What desugars here
    /// evaluates and encodes through the ordinary function machinery,
    /// because a bag IS a function whose range is the positive naturals:
    ///
    /// ```text
    /// SetToBag(S)   == [e ∈ S |-> 1]
    /// BagToSet(B)   == DOMAIN B
    /// BagIn(e, B)   == e ∈ DOMAIN B
    /// CopiesIn(e,B) == IF e ∈ DOMAIN B THEN B[e] ELSE 0
    /// B1 (+) B2     == [e ∈ DOMAIN B1 ∪ DOMAIN B2 |->
    ///                    CopiesIn(e,B1) + CopiesIn(e,B2)]
    /// B1 (-) B2     == [e ∈ {d ∈ DOMAIN B1 : B1[d] − CopiesIn(d,B2) > 0} |->
    ///                    B1[e] − CopiesIn(e,B2)]
    ///                 (the module writes a `LET B == …` and filters its
    ///                  positive part; `B[d] > 0` there is exactly
    ///                  `B1[d] − CopiesIn(d,B2) > 0` on `DOMAIN B1`, so
    ///                  this is the same function without the local)
    /// B1 ⊑ B2       == (∀ e ∈ DOMAIN B1 : e ∈ DOMAIN B2)
    ///                 ∧ (∀ e ∈ DOMAIN B1 : B1[e] ≤ B2[e])
    /// ```
    ///
    /// The operators whose definitions need `CHOOSE` or recursion
    /// (`BagCardinality`'s `Sum`, `SubBag`, `BagUnion`, `BagOfAll`)
    /// deliberately do **not** desugar — they stay opaque and are declined
    /// by name downstream rather than approximated.
    /// The Apalache standard-library operators that lower exactly
    /// (`StandardLibrary.scala:59-80`).
    ///
    /// Everything not here stays `Opaque` and is typed by `standard_sig` or
    /// declined by name. `Guess` and `Gen` are **never** lowered — see the
    /// soundness note on each.
    fn apalache_op(
        &mut self,
        name: &str,
        args: &[KeraRef],
        _span: Span,
    ) -> Result<Option<KeraRef>> {
        // A user's local definition of the same name still wins: this is
        // reachable only after name resolution failed to find one, but a
        // `LET`-bound operator or parameter of the same name must not be
        // captured by the built-in either. (The call site has already failed
        // `lookup`, which covers both.)
        let k = |i: usize| Rc::clone(&args[i]);
        match (name, args.len()) {
            // TLC's `x :> y` / `f @@ g` pair with `:=`'s family: exact
            // function constructors, cheaper than the general ones.
            (":=", 2) | (":>", 2) => Ok(Some(
                Kera::FunDef {
                    var: self.fresh_name("apa_dom"),
                    set: Kera::SetEnum(vec![k(0)]).rc(),
                    body: k(1),
                }
                .rc(),
            )),
            ("@@", 2) => {
                // `f @@ g`: g's entries win over f's where domains overlap —
                // Apalache's `__rewire_functions_in_apalache` defines it as a
                // fold of single-entry updates; the direct kernel form is the
                // same function, built as one definition over the union of
                // domains with `CopiesIn`-style reads that consult g first.
                let var = self.fresh_name("apa_e");
                let e = Kera::Var(var.clone()).rc();
                let dom = Kera::SetBin(
                    SetOp::Union,
                    Kera::Domain(k(0)).rc(),
                    Kera::Domain(k(1)).rc(),
                )
                .rc();
                let in_f = Kera::In(Rc::clone(&e), Kera::Domain(k(0)).rc()).rc();
                let read_f = Kera::FunApp(k(0), Rc::clone(&e)).rc();
                let read_g = Kera::FunApp(k(1), Rc::clone(&e)).rc();
                let body = Kera::Ite(in_f, read_f, read_g).rc();
                Ok(Some(
                    Kera::FunDef {
                        var,
                        set: dom,
                        body,
                    }
                    .rc(),
                ))
            }
            // `Skolem`, `Expand`, `ConstCardinality`: identity on their
            // argument — Apalache's own rewires (`__rewire_*_in_apalache.tla`)
            // make each a no-op hint to *its* encoder; this encoder's sets are
            // already exact where they are decidable at all, so the hint is the
            // value.
            ("Skolem", 1) | ("Expand", 1) | ("ConstCardinality", 1) => Ok(Some(k(0))),
            // `SetAsFun(S)`: the function `[p[1] \\in {p[2] : p \\in S} ...]` —
            // exact as one `FunDef` over the *pairs*: domain =
            // `{p[1] : p \in S}`, value at `d` = `CHOOSE p \in S : p[1] = d`,
            // then `p[2]`. CHOOSE over a symbolic set is its own gap, so this
            // lowers to the same kernel shape and the encoder's `CHOOSE`
            // decides.
            ("SetAsFun", 1) => {
                // `[d \\in DOMAIN-of-pairs |-> CHOOSE p \\in S : p[1] = d][2]`
                // needs `CHOOSE` in the kernel body — lowered here as such.
                let var = self.fresh_name("apa_d");
                let d = Kera::Var(var.clone()).rc();
                let one = Kera::Int("1".into()).rc();
                let two = Kera::Int("2".into()).rc();
                let p1 = |p: &KeraRef| Kera::FunApp(Rc::clone(p), Rc::clone(&one)).rc();
                let p2 = |p: &KeraRef| Kera::FunApp(Rc::clone(p), Rc::clone(&two)).rc();
                let pvar_name = self.fresh_name("apa_p");
                let p = Kera::Var(pvar_name.clone()).rc();
                let eq = Kera::Eq(p1(&p), Rc::clone(&d)).rc();
                let chosen = Kera::Choose {
                    var: pvar_name,
                    set: k(0),
                    body: eq,
                }
                .rc();
                let body = p2(&chosen);
                let dom_var = self.fresh_name("apa_q");
                let q = Kera::Var(dom_var.clone()).rc();
                let dom = Kera::Map {
                    var: dom_var,
                    set: k(0),
                    expr: p1(&q),
                }
                .rc();
                Ok(Some(
                    Kera::FunDef {
                        var,
                        set: dom,
                        body,
                    }
                    .rc(),
                ))
            }
            _ => Ok(None),
        }
    }

    fn bag_desugar(&mut self, name: &str, args: &[KeraRef]) -> Option<KeraRef> {
        // `IF e ∈ DOMAIN b THEN b[e] ELSE 0` over a shared operand pair.
        let copies_in = |_this: &mut Self, e: &KeraRef, b: &KeraRef| -> KeraRef {
            let dom = Kera::Domain(Rc::clone(b)).rc();
            Kera::Ite(
                Kera::In(Rc::clone(e), dom).rc(),
                Kera::FunApp(Rc::clone(b), Rc::clone(e)).rc(),
                Kera::Int("0".into()).rc(),
            )
            .rc()
        };
        let int0 = || Kera::Int("0".into()).rc();
        let int1 = || Kera::Int("1".into()).rc();
        match (name, args.len()) {
            ("SetToBag", 1) => Some(
                Kera::FunDef {
                    var: self.fresh_name("bag_e"),
                    set: Rc::clone(&args[0]),
                    body: int1(),
                }
                .rc(),
            ),
            ("BagToSet", 1) => Some(Kera::Domain(Rc::clone(&args[0])).rc()),

            // `BagUnion(S) == ApaFoldSet((+)-as-prefix, EmptyBag, S)`: a
            // fold adding each bag to the accumulator. Bag addition is
            // pointwise `+`, so the fold's value does not depend on the
            // order — the `ApaFoldSet` order-independence audit recognizes
            // exactly this body.
            ("BagUnion", 1) => {
                let acc = self.fresh_name("bag_acc");
                let elem = self.fresh_name("bag_e");
                let body = self.bag_desugar(
                    "\\oplus",
                    &[Kera::Var(acc.clone()).rc(), Kera::Var(elem.clone()).rc()],
                )?;
                Some(
                    Kera::Fold {
                        over: FoldOver::Set,
                        acc,
                        elem,
                        base: self.builtin_constant("EmptyBag")?,
                        collection: Rc::clone(&args[0]),
                        body,
                    }
                    .rc(),
                )
            }
            // `BagCardinality(B) == \\Sigma_{e \\in DOMAIN B} B[e]` —
            // Apalache's rewire folds `i + B[e]` from 0, and so does this.
            // A `+`-chain fold whose accumulator leaf is bare is provably
            // order-independent, which the `ApaFoldSet` audit checks.
            ("BagCardinality", 1) => {
                let acc = self.fresh_name("bag_i");
                let elem = self.fresh_name("bag_e");
                Some(
                    Kera::Fold {
                        over: FoldOver::Set,
                        acc: acc.clone(),
                        elem: elem.clone(),
                        base: Kera::Int("0".into()).rc(),
                        collection: Kera::Domain(Rc::clone(&args[0])).rc(),
                        body: Kera::Arith(
                            ArithOp::Add,
                            Kera::Var(acc).rc(),
                            Kera::FunApp(Rc::clone(&args[0]), Kera::Var(elem).rc()).rc(),
                        )
                        .rc(),
                    }
                    .rc(),
                )
            }
            ("BagIn", 2) => {
                Some(Kera::In(Rc::clone(&args[0]), Kera::Domain(Rc::clone(&args[1])).rc()).rc())
            }
            ("CopiesIn", 2) => Some(copies_in(self, &args[0], &args[1])),
            // `B1 (+) B2`.
            ("\\oplus", 2) => {
                let var = self.fresh_name("bag_e");
                let e = Kera::Var(var.clone()).rc();
                let dom = Kera::SetBin(
                    SetOp::Union,
                    Kera::Domain(Rc::clone(&args[0])).rc(),
                    Kera::Domain(Rc::clone(&args[1])).rc(),
                )
                .rc();
                let sum = Kera::Arith(
                    ArithOp::Add,
                    copies_in(self, &e, &args[0]),
                    copies_in(self, &e, &args[1]),
                )
                .rc();
                Some(
                    Kera::FunDef {
                        var,
                        set: dom,
                        body: sum,
                    }
                    .rc(),
                )
            }
            // `B1 (-) B2`, on the filtered positive part.
            ("\\ominus", 2) => {
                let dvar = self.fresh_name("bag_d");
                let d = Kera::Var(dvar.clone()).rc();
                let diff_d = Kera::Arith(
                    ArithOp::Sub,
                    Kera::FunApp(Rc::clone(&args[0]), Rc::clone(&d)).rc(),
                    copies_in(self, &d, &args[1]),
                )
                .rc();
                let positive = Kera::Filter {
                    var: dvar,
                    set: Kera::Domain(Rc::clone(&args[0])).rc(),
                    pred: Kera::Cmp(CmpOp::Gt, diff_d, int0()).rc(),
                }
                .rc();
                let var = self.fresh_name("bag_e");
                let e = Kera::Var(var.clone()).rc();
                let body = Kera::Arith(
                    ArithOp::Sub,
                    Kera::FunApp(Rc::clone(&args[0]), Rc::clone(&e)).rc(),
                    copies_in(self, &e, &args[1]),
                )
                .rc();
                Some(
                    Kera::FunDef {
                        var,
                        set: positive,
                        body,
                    }
                    .rc(),
                )
            }
            // `B1 \sqsubseteq B2`.
            ("\\sqsubseteq", 2) => {
                let var = self.fresh_name("bag_e");
                let e = Kera::Var(var.clone()).rc();
                let in_dom2 = Kera::In(Rc::clone(&e), Kera::Domain(Rc::clone(&args[1])).rc()).rc();
                let ordered = Kera::Cmp(
                    CmpOp::Le,
                    Kera::FunApp(Rc::clone(&args[0]), Rc::clone(&e)).rc(),
                    Kera::FunApp(Rc::clone(&args[1]), Rc::clone(&e)).rc(),
                )
                .rc();
                let body = Kera::And(vec![in_dom2, ordered]).rc();
                Some(
                    Kera::Forall {
                        var,
                        set: Kera::Domain(Rc::clone(&args[0])).rc(),
                        body,
                    }
                    .rc(),
                )
            }
            _ => None,
        }
    }

    /// Override the total work budget, in steps of the lowering walk.
    #[must_use]
    pub fn with_step_budget(mut self, n: usize) -> Self {
        self.step_budget = n;
        self
    }

    /// `TRUE`, `FALSE` and `BOOLEAN` are part of the language, not names a
    /// module declares. Falling through to `Var("TRUE")` made them *free
    /// names*: the evaluator refused them, and an encoder would have seen an
    /// undeclared symbol where a boolean was meant.
    ///
    /// Checked only after scopes and definitions, so a binding of the same
    /// name still wins — the language reserves them, but nothing here
    /// depends on that.
    fn builtin_constant(&mut self, name: &str) -> Option<KeraRef> {
        match name {
            "TRUE" => Some(Kera::Bool(true).rc()),
            "FALSE" => Some(Kera::Bool(false).rc()),
            "BOOLEAN" => {
                Some(Kera::SetEnum(vec![Kera::Bool(false).rc(), Kera::Bool(true).rc()]).rc())
            }
            // The nullary `Bags` operator lowers to its definition —
            // `SetToBag({})` is `[e \in {} |-> 1]` — so every consumer sees
            // the same function it would see for the spelled-out form. The
            // binder comes from `fresh_name` like every other binder: inference
            // keys bound variables by **name**, so one fixed name here meant
            // every `EmptyBag` in a specification shared a single element type
            // — `TestBags.tla` failed with "Str and Int" the moment a second
            // bag appeared.
            "EmptyBag" => {
                let var = self.fresh_name("bag_e");
                Some(
                    Kera::FunDef {
                        var,
                        set: Kera::SetEnum(Vec::new()).rc(),
                        body: Kera::Int("1".into()).rc(),
                    }
                    .rc(),
                )
            }
            _ => None,
        }
    }

    /// The  a ground value denotes, or a decline-shaped  the
    /// caller turns into its own error.
    fn int_of(&self, v: &crate::value::Value) -> Option<i128> {
        match v {
            crate::value::Value::Int(i) => Some(*i),
            _ => None,
        }
    }

    /// The integer a **ground surface** expression denotes, spot-lowered in
    /// a throwaway lowerer so nothing lands in the real caches. For
    /// `Repeat`/`MkSeq` counts, whose finiteness the lowering depends on.
    fn ground_int_expr(&mut self, e: &'a Expr) -> Option<crate::value::Value> {
        let mut probe = Lowerer::new();
        probe.scopes = self.scopes.clone();
        probe.defs = self.defs.clone();
        probe.funs = self.funs.clone();
        let k = probe.lower(e).ok()?;
        match crate::eval::Evaluator::new().eval(&k) {
            Ok(v @ crate::value::Value::Int(_)) => Some(v),
            _ => None,
        }
    }

    /// Whether [`Self::builtin_constant`] would produce a value for `name`,
    /// without borrowing the lowerer mutably for the common no case.
    fn builtin_constant_probe(&self, name: &str) -> bool {
        matches!(name, "TRUE" | "FALSE" | "BOOLEAN" | "EmptyBag")
    }

    fn fresh_name(&mut self, base: &str) -> Name {
        self.fresh += 1;
        Name(format!("{base}#{}", self.fresh))
    }

    /// Read an argument as an *operator*: a defined name, an operator
    /// parameter already in scope, or a `LAMBDA`.
    fn as_operator(&self, arg: &'a Expr) -> Option<Binding<'a>> {
        match &arg.kind {
            ExprKind::Lambda { params, body } => Some(Binding::Op {
                params: params.iter().map(|p| (p.name.clone(), 0)).collect(),
                body,
            }),
            ExprKind::Name(q) if !q.is_qualified() => {
                let id = q.base()?;
                if let Some(b @ Binding::Op { .. }) = self.lookup(&id.name) {
                    return Some(b);
                }
                // A built-in operator symbol: `FooBar(7, +)`, `FoldSet(\\cup,
                // 0, S)`. Only unambiguously-binary symbols (the AC set:
                // `+ * \\cup \\cap \\/ /\\`, plus the `\\union`/
                // `\\intersect` spellings) — unary and binary `-` must stay
                // distinct, and the token's fixity has already decided
                // which one a bare `-` is by the time it is a Name.
                if let Some(sym) = builtin_operator_symbol(&id.name) {
                    return Some(Binding::BuiltinOp(sym));
                }
                let def = self.defs.get(&id.name)?;
                Some(Binding::Op {
                    params: def.params.clone(),
                    body: def.body,
                })
            }
            ExprKind::Paren(inner) => self.as_operator(inner),
            _ => None,
        }
    }

    fn lookup(&self, name: &str) -> Option<Binding<'a>> {
        self.scopes.iter().rev().find_map(|s| s.get(name).cloned())
    }

    /// Lower one expression.
    ///
    /// # Errors
    ///
    /// Returns the first [`LowerError`] encountered.
    pub fn lower(&mut self, expr: &'a Expr) -> Result<KeraRef> {
        let stack: Vec<Frame<'a>> = vec![Frame::Expand(expr)];
        self.run_frames(stack, expr.span)
    }

    /// The lowering walk over a pre-seeded frame stack; [`Self::lower`] with
    /// one `Expand` frame, and [`Self::lower_named`]'s open-instance path
    /// with the instance frames an unprefixed member needs.
    fn run_frames(&mut self, stack: Vec<Frame<'a>>, root_span: Span) -> Result<KeraRef> {
        let mut stack = stack;
        let mut values: Vec<KeraRef> = Vec::new();
        let mut steps = 0usize;

        while let Some(frame) = stack.pop() {
            // Inlining splices a definition's body in at every use, so a term
            // can be enormous without being deep. The budget bounds total work
            // and exists only to keep a pathological input from exhausting
            // memory.
            steps += 1;
            if steps > self.step_budget {
                return Err(LowerError::new(
                    LowerErrorKind::BudgetExhausted {
                        limit: self.step_budget,
                    },
                    root_span,
                ));
            }
            match frame {
                Frame::PushScope(s) => self.scopes.push(s),
                Frame::BindMappedFold {
                    p0,
                    p1,
                    elem,
                    acc,
                    indices,
                } => {
                    // The function is the value this frame's expansion put
                    // directly beneath it: the body reads it as `fun[elem]`,
                    // and the collection is its `DOMAIN` — or the surface
                    // index set, lowered like any other expression.
                    let Some(fun) = values.pop() else {
                        return Err(LowerError::unsupported(
                            "a fold over a function",
                            "internal: missing the function to fold over",
                            root_span,
                        ));
                    };
                    let read = Kera::FunApp(Rc::clone(&fun), Kera::Var(elem).rc()).rc();
                    let mut scope = HashMap::new();
                    scope.insert(p0, Binding::Value(read));
                    scope.insert(p1, Binding::Value(Kera::Var(acc).rc()));
                    self.scopes.push(scope);
                    match indices {
                        Some(ix) => stack.push(Frame::Expand(ix)),
                        None => {
                            let dom = Kera::Domain(fun).rc();
                            stack.push(Frame::Kera(dom));
                        }
                    }
                }
                Frame::PopScope => {
                    self.scopes.pop();
                }
                Frame::BindExceptAt { path_len, before } => {
                    // `@` in the k-th update of `[f EXCEPT !p1 = v1, !p2 = v2]`
                    // denotes the **partially updated** function applied at
                    // this update's path — not the original `f`, and certainly
                    // not the previous update's value.
                    //
                    // TLC settles it: `[[a |-> 1] EXCEPT !.a = 5, !.a = @ + 100].a`
                    // is 105, not 101, so `@` sees the 5. That follows from
                    // the language definition, where the multi-update form is
                    // an abbreviation for nested single updates and `@` in
                    // `[g EXCEPT ![c] = e]` denotes `g[c]`.
                    //
                    // The old code took the function to be a fixed
                    // `path_len + 1` below the top of the value stack. That
                    // holds only for the *first* update; by the second, the
                    // first update's indices and value sit in between, so it
                    // picked up `v1` and lowered `@` to `v1[c2]`. Silent, and
                    // a wrong value rather than a refusal — it typed as a
                    // record where a model value belonged, which is how it
                    // was found.
                    let n = values.len();
                    let skipped: usize = before.iter().map(|p| p + 1).sum();
                    let base_at = n
                        .checked_sub(path_len)
                        .and_then(|i| i.checked_sub(skipped))
                        .and_then(|i| i.checked_sub(1));
                    let Some(base_at) = base_at else {
                        return Err(LowerError::unsupported(
                            "an `EXCEPT` update",
                            "internal: the function being updated was not on the stack",
                            root_span,
                        ));
                    };
                    let Some(mut acc) = values.get(base_at).cloned() else {
                        return Err(LowerError::unsupported(
                            "an `EXCEPT` update",
                            "internal: the function being updated was not on the stack",
                            root_span,
                        ));
                    };
                    // Replay the earlier updates, exactly as `build_except`
                    // will, so `@` sees what they wrote.
                    let mut cursor = base_at + 1;
                    for pl in &before {
                        let Some(path) = values.get(cursor..cursor + pl).map(<[KeraRef]>::to_vec)
                        else {
                            break;
                        };
                        let Some(value) = values.get(cursor + pl).cloned() else {
                            break;
                        };
                        acc = nest_except(acc, &path, value, root_span)?;
                        cursor += pl + 1;
                    }
                    let mut at = acc;
                    for k in 0..path_len {
                        let Some(idx) = values.get(cursor + k) else {
                            break;
                        };
                        at = Kera::FunApp(at, Rc::clone(idx)).rc();
                    }
                    let mut scope = HashMap::new();
                    scope.insert("@".to_string(), Binding::Value(at));
                    self.scopes.push(scope);
                }
                Frame::CacheStore(name) => {
                    if let Some(v) = values.last() {
                        self.cache.insert(name, Rc::clone(v));
                    }
                }
                Frame::Inline {
                    name,
                    params,
                    body,
                    span,
                    cache_as,
                } => {
                    if self.inline_depth >= self.max_inline_depth {
                        // A RECURSIVE-declared (or self-referential)
                        // definition hitting the limit is not "too deep",
                        // it is *infinite*: the named diagnostic says what
                        // to do instead, in Apalache's own terms.
                        if self.recursive_names.contains(&name) {
                            return Err(LowerError::unsupported(
                                &format!("the recursive operator `{name}`"),
                                "recursive operators have no finite inlining; Apalache \
                                 dropped them too — spell the recursion as ApaFoldSet / \
                                 ApaFoldSeqLeft, or as a recursive function",
                                span,
                            ));
                        }
                        return Err(LowerError::new(
                            LowerErrorKind::InlineLimit {
                                name,
                                limit: self.max_inline_depth,
                            },
                            span,
                        ));
                    }
                    let mut scope = HashMap::new();
                    for (p, arity) in params.iter().rev() {
                        if *arity > 0 {
                            // Bound by `expand` as an operator, not a value.
                            continue;
                        }
                        let Some(v) = values.pop() else {
                            return Err(LowerError::new(
                                LowerErrorKind::Arity {
                                    name: name.clone(),
                                    expected: params.len(),
                                    found: 0,
                                },
                                span,
                            ));
                        };
                        scope.insert(p.clone(), Binding::Value(v));
                    }
                    if let Some(extra) = self.pending_ops.remove(&span.start.offset) {
                        for (k, v) in extra {
                            scope.insert(k, v);
                        }
                    }
                    self.inline_depth += 1;
                    self.scopes.push(scope);
                    if let Some(key) = cache_as {
                        stack.push(Frame::CacheStore(key));
                    }
                    stack.push(Frame::PopInline);
                    stack.push(Frame::Expand(body));
                }
                Frame::PopInline => {
                    self.scopes.pop();
                    self.inline_depth = self.inline_depth.saturating_sub(1);
                }
                Frame::PushLiteral(v) => values.push(v),
                Frame::BuildTuple(n) => {
                    let at = values.len().checked_sub(n).ok_or_else(|| {
                        LowerError::unsupported(
                            "an `EXCEPT` index",
                            "internal: missing index expressions",
                            root_span,
                        )
                    })?;
                    let parts: Vec<KeraRef> = values.split_off(at);
                    values.push(Kera::Tuple(parts).rc());
                }
                Frame::PushInstanceCtx {
                    module,
                    subst_names,
                    member_params,
                } => {
                    // Arguments were pushed last, so they come off first.
                    let mut scope = HashMap::new();
                    for (p, arity) in member_params.iter().rev() {
                        if *arity > 0 {
                            continue;
                        }
                        let Some(v) = values.pop() else {
                            return Err(LowerError::unsupported(
                                "an instance member application",
                                "internal: missing argument",
                                root_span,
                            ));
                        };
                        scope.insert(p.clone(), Binding::Value(v));
                    }
                    let mut subst = HashMap::new();
                    for n in subst_names.iter().rev() {
                        let Some(v) = values.pop() else {
                            return Err(LowerError::unsupported(
                                "an `INSTANCE` substitution",
                                "internal: missing replacement",
                                root_span,
                            ));
                        };
                        subst.insert(n.clone(), v);
                    }
                    // Every substituted name — `WITH` replacements and
                    // implicit same-named symbols alike — arrives as a value
                    // pushed by `push_instance_body`; the resolution rules
                    // (enclosing instance, `.cfg` constant, definition,
                    // declared symbol, hard error) live in
                    // `resolve_implicit`, where the spans still point at the
                    // instance rather than at a late name error.
                    self.ctx.push(Rc::new(InstanceCtx { module, subst }));
                    self.scopes.push(scope);
                }
                Frame::PopInstanceCtx => {
                    self.ctx.pop();
                    self.scopes.pop();
                }
                Frame::PopLetDefs(saved_defs, saved_insts) => {
                    for (name, prev) in saved_defs {
                        match prev {
                            Some(d) => {
                                self.defs.insert(name, d);
                            }
                            None => {
                                self.defs.remove(&name);
                                self.funs.remove(&name);
                            }
                        }
                    }
                    for (name, prev) in saved_insts {
                        match prev {
                            Some(i) => {
                                self.instances.insert(name, i);
                            }
                            None => {
                                self.instances.remove(&name);
                            }
                        }
                    }
                }
                // `f[x \in S] == e` at a use site: it denotes a *value*, so
                // it expands as `[x \in S |-> e]`.
                //
                // `f[x \in S, y \in T] == e` is a function of one variable
                // ranging over `S \X T`, exactly as the expression form
                // `[x \in S, y \in T |-> e]` already was — the two differ
                // only in where they are written, and lowering them
                // differently was the whole defect. Nesting binders instead
                // would be a different function: one that returns a function.
                Frame::PopRecursion(name) => {
                    self.recursing.remove(&name);
                }
                Frame::ExpandFun(name, bounds, body) => {
                    // Self-referential? Then the body must be lowered with the
                    // name *free*, and the result is a `RecFun` rather than an
                    // ordinary function constructor.
                    let recursive = mentions_name(body, &name);
                    if recursive {
                        self.recursing.insert(name.clone());
                        stack.push(Frame::PopRecursion(name.clone()));
                    }
                    let total: usize = bounds.iter().map(|b| b.patterns.len()).sum();
                    let mut scope = HashMap::new();
                    let var = if total == 1 {
                        let mut first = None;
                        for b in bounds {
                            for p in &b.patterns {
                                first = Some(self.bind_pattern(p, &mut scope));
                            }
                        }
                        first
                    } else if total == 0 {
                        None
                    } else {
                        Some(self.bind_product(bounds, &mut scope))
                    };
                    let Some(var) = var else {
                        return Err(LowerError::unsupported(
                            "a function definition with no bound variable",
                            "internal",
                            root_span,
                        ));
                    };
                    // The recursive name is a binder like any other, so it
                    // gets a fresh one and the body sees the fresh name
                    // through its scope: two recursive functions called
                    // `f` in sibling `LET`s would otherwise lower with the
                    // *same* binder, and inference — which keys free names
                    // by name — would fuse two unrelated functions into
                    // one variable. The binder-uniqueness check exists to
                    // make that impossible to reintroduce.
                    let rec_name = recursive.then(|| self.fresh_name(&name));
                    if let Some(rn) = &rec_name {
                        scope.insert(name.clone(), Binding::Value(Kera::Var(rn.clone()).rc()));
                    }
                    stack.push(Frame::BuildFun {
                        var,
                        domains: total,
                        recursive: rec_name,
                    });
                    stack.push(Frame::PopScope);
                    stack.push(Frame::Expand(body));
                    stack.push(Frame::PushScope(scope));
                    for b in bounds.iter().rev() {
                        for _ in 0..b.patterns.len() {
                            stack.push(Frame::Expand(&b.domain));
                        }
                    }
                }
                Frame::BuildFun {
                    var,
                    domains,
                    recursive,
                } => {
                    let Some(body) = values.pop() else {
                        return Err(LowerError::unsupported(
                            "a function definition",
                            "internal: missing body",
                            root_span,
                        ));
                    };
                    let mut doms = Vec::with_capacity(domains);
                    for _ in 0..domains {
                        let Some(d) = values.pop() else {
                            return Err(LowerError::unsupported(
                                "a function definition",
                                "internal: missing domain",
                                root_span,
                            ));
                        };
                        doms.push(d);
                    }
                    doms.reverse();
                    let set = if doms.len() == 1 {
                        doms.swap_remove(0)
                    } else {
                        Kera::Times(doms).rc()
                    };
                    values.push(match recursive {
                        Some(name) => Kera::RecFun {
                            name,
                            var,
                            set,
                            body,
                        }
                        .rc(),
                        None => Kera::FunDef { var, set, body }.rc(),
                    });
                }
                Frame::BuildBagOfAll { acc, elem, out } => {
                    let (Some(f_of_elem), Some(bag)) = (values.pop(), values.pop()) else {
                        return Err(LowerError::unsupported(
                            "`BagOfAll`",
                            "internal: missing children",
                            root_span,
                        ));
                    };
                    // `B[elem]`: the copies carried over for this element.
                    let copies = Kera::FunApp(bag.clone(), Kera::Var(elem.clone()).rc()).rc();
                    // `[out \\in {F(elem)} |-> B[elem]]`: the singleton bag.
                    let single = Kera::FunDef {
                        var: out,
                        set: Kera::SetEnum(vec![f_of_elem]).rc(),
                        body: copies,
                    }
                    .rc();
                    // `acc (+) single`, through the same `\\oplus` desugaring
                    // every bag addition takes, so encoders and the evaluator
                    // see one shape.
                    let step = self
                        .bag_desugar("\\oplus", &[Kera::Var(acc.clone()).rc(), single])
                        .ok_or_else(|| {
                            LowerError::unsupported(
                                "`BagOfAll`",
                                "internal: bag addition has no lowering",
                                root_span,
                            )
                        })?;
                    values.push(
                        Kera::Fold {
                            over: FoldOver::Set,
                            acc,
                            elem,
                            base: self.builtin_constant("EmptyBag").ok_or_else(|| {
                                LowerError::unsupported(
                                    "`BagOfAll`",
                                    "internal: EmptyBag has no lowering",
                                    root_span,
                                )
                            })?,
                            collection: Kera::Domain(bag).rc(),
                            body: step,
                        }
                        .rc(),
                    );
                }
                Frame::BuildSelectSeq { acc, elem } => {
                    let (Some(f_of_elem), Some(seq)) = (values.pop(), values.pop()) else {
                        return Err(LowerError::unsupported(
                            "`SelectSeq`",
                            "internal: missing children",
                            root_span,
                        ));
                    };
                    let keep = Kera::Ite(
                        f_of_elem,
                        Kera::Opaque(
                            Name("Append".into()),
                            vec![Kera::Var(acc.clone()).rc(), Kera::Var(elem.clone()).rc()],
                        )
                        .rc(),
                        Kera::Var(acc.clone()).rc(),
                    )
                    .rc();
                    values.push(
                        Kera::Fold {
                            over: FoldOver::SeqLeft,
                            acc,
                            elem,
                            base: Kera::Tuple(Vec::new()).rc(),
                            collection: seq,
                            body: keep,
                        }
                        .rc(),
                    );
                }
                Frame::BuildBuiltinOp { sym, span } => {
                    let (Some(y), Some(x)) = (values.pop(), values.pop()) else {
                        return Err(LowerError::unsupported(
                            "a built-in operator argument",
                            "internal: missing children",
                            span,
                        ));
                    };
                    let built = build_infix(sym, x, y, span, &mut self.fresh)?;
                    values.push(built);
                }
                Frame::Kera(k) => values.push(k),
                Frame::BuildFunAsSeq => {
                    let (Some(len), Some(f)) = (values.pop(), values.pop()) else {
                        return Err(LowerError::unsupported(
                            "`FunAsSeq`",
                            "internal: missing children",
                            root_span,
                        ));
                    };
                    values.push(Kera::Opaque(Name("FunAsSeq".into()), vec![f, len]).rc());
                }
                Frame::BuildMkSeq { var, n } => {
                    let Some(body) = values.pop() else {
                        return Err(LowerError::unsupported(
                            "`MkSeq`",
                            "internal: missing children",
                            root_span,
                        ));
                    };
                    let lo = Kera::Int("1".into()).rc();
                    let hi = Kera::Int(n.to_string()).rc();
                    values.push(
                        Kera::FunDef {
                            var,
                            set: Kera::Range(lo, hi).rc(),
                            body,
                        }
                        .rc(),
                    );
                }
                Frame::BuildFold { over, acc, elem } => {
                    let (Some(body), Some(collection), Some(base)) =
                        (values.pop(), values.pop(), values.pop())
                    else {
                        return Err(LowerError::unsupported(
                            "a fold",
                            "internal: missing children",
                            root_span,
                        ));
                    };
                    values.push(
                        Kera::Fold {
                            over,
                            acc,
                            elem,
                            base,
                            collection,
                            body,
                        }
                        .rc(),
                    );
                }
                Frame::Build(e, n) => {
                    let built = self.build(e, &mut values, n)?;
                    values.push(built);
                }
                Frame::Expand(e) => self.expand(e, &mut stack, &mut values)?,
            }
        }

        values.pop().ok_or_else(|| {
            LowerError::unsupported(
                "this expression",
                "internal: lowering produced no value",
                root_span,
            )
        })
    }
}

impl Default for Lowerer<'_> {
    fn default() -> Self {
        Self::new()
    }
}

/// Sort record fields so two records written in different orders compare equal.
fn sort_fields(mut fs: Vec<(String, KeraRef)>) -> Vec<(String, KeraRef)> {
    fs.sort_by(|a, b| a.0.cmp(&b.0));
    fs
}

/// Convert a based numeral to decimal digits.
fn digits_to_decimal(base: nixie_tla_syntax::NumBase, digits: &str) -> Option<String> {
    use nixie_tla_syntax::NumBase;
    let radix = match base {
        NumBase::Decimal => return Some(digits.to_string()),
        NumBase::Binary => 2,
        NumBase::Octal => 8,
        NumBase::Hex => 16,
    };
    // Accumulate in decimal by hand so that a wide literal is exact rather
    // than truncated through `u64` — `AGENTS.md`: wide values stay exact.
    let mut acc: Vec<u8> = vec![0];
    for c in digits.chars() {
        let d = c.to_digit(radix)? as u8;
        let mut carry = u32::from(d);
        for slot in acc.iter_mut() {
            let v = u32::from(*slot) * radix + carry;
            *slot = (v % 10) as u8;
            carry = v / 10;
        }
        while carry > 0 {
            acc.push((carry % 10) as u8);
            carry /= 10;
        }
    }
    let s: String = acc.iter().rev().map(|d| (b'0' + d) as char).collect();
    Some(s.trim_start_matches('0').to_string()).map(|t| if t.is_empty() { "0".into() } else { t })
}

impl<'a> Lowerer<'a> {
    /// Bind one bound group, producing the scope entries and the binder name.
    ///
    /// A plain pattern binds a fresh name directly. A tuple pattern binds one
    /// fresh name and projects the components out of it, which is what keeps
    /// every kernel binder single-variable.
    fn bind_pattern(&mut self, pat: &Pattern, scope: &mut HashMap<String, Binding<'a>>) -> Name {
        match pat {
            Pattern::Name(id) => {
                let fresh = self.fresh_name(&id.name);
                scope.insert(id.name.clone(), Binding::Bound(fresh.clone()));
                fresh
            }
            Pattern::Tuple(ids) => {
                let fresh = self.fresh_name("tuple");
                let tv = Kera::Var(fresh.clone()).rc();
                for (i, id) in ids.iter().enumerate() {
                    let idx = Kera::Int((i + 1).to_string()).rc();
                    scope.insert(
                        id.name.clone(),
                        Binding::Value(Kera::FunApp(Rc::clone(&tv), idx).rc()),
                    );
                }
                fresh
            }
        }
    }

    /// Push the frames for a chain of binders over `bounds`, ending in `body`.
    ///
    /// `make` turns (var, set, body) into the kernel node, so the same
    /// machinery serves `\A`, `\E`, `{x \in S : p}`, `{e : x \in S}` and
    /// `[x \in S |-> e]`.
    fn expand_binder_chain(
        &mut self,
        expr: &'a Expr,
        bounds: &'a [Bound],
        body: &'a Expr,
        stack: &mut Vec<Frame<'a>>,
    ) {
        // Children pushed, in evaluation order: every domain, then the body.
        // `Build` rebuilds the chain from them.
        let total: usize = bounds.iter().map(|b| b.patterns.len()).sum();
        let mut scope = HashMap::new();
        let mut names = Vec::with_capacity(total);
        for b in bounds {
            for p in &b.patterns {
                names.push(self.bind_pattern(p, &mut scope));
            }
        }
        self.binder_names.insert(expr.span.start.offset, names);

        stack.push(Frame::Build(expr, total + 1));
        stack.push(Frame::PopScope);
        stack.push(Frame::Expand(body));
        stack.push(Frame::PushScope(scope));
        // Domains are outside the binder's scope.
        for b in bounds.iter().rev() {
            for _ in 0..b.patterns.len() {
                stack.push(Frame::Expand(&b.domain));
            }
        }
    }

    /// Inline a user-defined operator that was written in operator position.
    fn push_symbol_inline(
        &mut self,
        op: &str,
        args: &[&'a Expr],
        span: Span,
        stack: &mut Vec<Frame<'a>>,
    ) -> Result<()> {
        let Some(def) = self.defs.get(op).cloned() else {
            return Err(LowerError::unsupported(
                &format!("the operator `{op}`"),
                "internal: it was reported as defined but is not",
                span,
            ));
        };
        if def.params.len() != args.len() {
            return Err(LowerError::new(
                LowerErrorKind::Arity {
                    name: op.to_string(),
                    expected: def.params.len(),
                    found: args.len(),
                },
                span,
            ));
        }
        stack.push(Frame::Inline {
            name: op.to_string(),
            params: def.params.clone(),
            body: def.body,
            span,
            cache_as: None,
        });
        for a in args.iter().rev() {
            stack.push(Frame::Expand(a));
        }
        Ok(())
    }

    /// Push the frames that look through `inst` at its member `member`,
    /// applied to `args`.
    fn push_instance_member(
        &mut self,
        inst_name: &str,
        member: &str,
        args: &[&'a Expr],
        span: Span,
        stack: &mut Vec<Frame<'a>>,
    ) -> Result<()> {
        let Some(inst) = self.instances.get(inst_name).cloned() else {
            return Err(LowerError::unsupported(
                &format!("`{inst_name}!{member}`"),
                "no `INSTANCE` with that name is in scope, or the instantiated module was \
                 not found on the search path",
                span,
            ));
        };
        if !inst.params.is_empty() {
            return Err(LowerError::unsupported(
                &format!("`{inst_name}!{member}`"),
                "a parameterised instance must be applied, as `I(e)!Op`",
                span,
            ));
        }
        self.push_instance_body(&inst, member, args, span, stack)
    }

    fn push_instance_body(
        &mut self,
        inst: &Instantiation<'a>,
        member: &str,
        args: &[&'a Expr],
        span: Span,
        stack: &mut Vec<Frame<'a>>,
    ) -> Result<()> {
        let target = inst.module;
        let Some(def) = self
            .module_defs
            .get(&target.name.name)
            .and_then(|m| m.get(member))
            .cloned()
        else {
            return Err(LowerError::unsupported(
                &format!("`{member}`"),
                &format!(
                    "module `{}` has no operator definition with that name",
                    target.name.name
                ),
                span,
            ));
        };
        if def.params.len() != args.len() {
            return Err(LowerError::new(
                LowerErrorKind::Arity {
                    name: member.to_string(),
                    expected: def.params.len(),
                    found: args.len(),
                },
                span,
            ));
        }

        // Every constant and variable the instantiated module declares must be
        // substituted: explicitly by `WITH`, or implicitly by the same-named
        // symbol at the instance's declaring scope. Leaving one unsubstituted
        // would silently read the *wrong* module's symbol — and the old
        // fallback here did exactly that, minting a free kernel variable for
        // any name it could not resolve, which the solver then treated as
        // unconstrained. test59.tla is the shape that exposed it: the
        // `LET x == y+1` before `M == INSTANCE test59a` is the same-named
        // symbol test59a's `VARIABLE x` implicitly substitutes to.
        let declared: Vec<String> = target
            .constants()
            .iter()
            .map(|d| d.name.name.clone())
            .chain(target.variables().iter().map(|v| v.name.clone()))
            .collect();
        let mut subst_names: Vec<String> = Vec::new();
        let mut subst_sources: Vec<SubstSource<'a>> = Vec::new();
        for (n, e) in &inst.with {
            subst_names.push(n.clone());
            subst_sources.push(SubstSource::Expr(e));
        }
        for d in declared {
            if subst_names.contains(&d) {
                continue;
            }
            let src = self.resolve_implicit(&d, inst, span)?;
            subst_names.push(d);
            subst_sources.push(src);
        }

        stack.push(Frame::PopInstanceCtx);
        stack.push(Frame::Expand(def.body));
        stack.push(Frame::PushInstanceCtx {
            module: target,
            subst_names,
            member_params: def.params.clone(),
        });
        // Arguments last so they are on top of the value stack.
        for a in args.iter().rev() {
            stack.push(Frame::Expand(a));
        }
        for src in subst_sources.into_iter().rev() {
            match src {
                SubstSource::Expr(e) => stack.push(Frame::Expand(e)),
                SubstSource::Value(v) => stack.push(Frame::PushLiteral(v)),
                SubstSource::Fun(name, bounds, body) => {
                    stack.push(Frame::ExpandFun(name, bounds, body));
                }
            }
        }
        Ok(())
    }

    /// Resolve one *implicit* substitution: a declared name of the
    /// instantiated module that no `WITH` clause covers. The replacement is
    /// the same-named symbol at the instance's declaring scope, in the same
    /// order a bare name there would resolve:
    ///
    /// 1. an enclosing instance's substitution (nested instances compose);
    /// 2. a `.cfg`-pinned constant;
    /// 3. a visible nullary definition — module-level, or `LET`-scoped when
    ///    the instance itself sits in that `LET`;
    /// 4. a visible function definition `f[x \\in S] == e`;
    /// 5. a variable or constant the declaring module itself declares,
    ///    which lowers as the free kernel name of that symbol;
    /// 6. nothing — a hard error. The specification is ill-formed (TLA+
    ///    requires every declared name to be substituted), and inventing a
    ///    value here would fabricate a verdict.
    fn resolve_implicit(
        &self,
        name: &str,
        inst: &Instantiation<'a>,
        span: Span,
    ) -> Result<SubstSource<'a>> {
        // The declaring scope: the module the instance unit lives in, or —
        // for a `LET`-scoped instance — the module (or instance member) the
        // lowering walk is currently inside.
        let source = inst
            .source
            .or_else(|| self.ctx.last().map(|c| c.module))
            .or(self.lower_module);
        if let Some(v) = self.ctx.last().and_then(|c| c.subst.get(name)) {
            return Ok(SubstSource::Value(Rc::clone(v)));
        }
        if let Some(v) = self.constants.get(name) {
            return Ok(SubstSource::Value(Rc::clone(v)));
        }
        if let Some(def) = self.defs.get(name) {
            if def.params.is_empty() {
                return Ok(SubstSource::Expr(def.body));
            }
            return Err(LowerError::unsupported(
                &format!("`{name}`"),
                &format!(
                    "it substitutes for a declared value of module `{}`, but is an \
                     operator of {} argument(s); `WITH {name} <- \\dots` must name a value",
                    inst.module.name.name,
                    def.params.len()
                ),
                span,
            ));
        }
        if let Some(&(bounds, body)) = self.funs.get(name) {
            return Ok(SubstSource::Fun(name.to_string(), bounds, body));
        }
        if let Some(m) = source
            && self.declares_in_closure(m, name)
        {
            return Ok(SubstSource::Value(Kera::Var(Name(name.to_string())).rc()));
        }
        Err(LowerError::unsupported(
            &format!("`{name}`"),
            &format!(
                "module `{}` declares it and no `WITH` replacement or same-named \
                 symbol is in scope at the instance",
                inst.module.name.name
            ),
            span,
        ))
    }

    /// Is `name` declared as a constant or variable of `m`, or of any module
    /// `m` transitively extends? `EXTENDS` re-exports declarations, so a
    /// declaration reached through it is as good as `m`'s own.
    fn declares_in_closure(&self, m: &'a Module, name: &str) -> bool {
        let mut work: Vec<&'a Module> = vec![m];
        let mut seen: std::collections::HashSet<&str> = std::collections::HashSet::new();
        while let Some(cur) = work.pop() {
            if !seen.insert(cur.name.name.as_str()) {
                continue;
            }
            let declared = cur.constants().iter().any(|d| d.name.name == name)
                || cur.variables().iter().any(|v| v.name == name);
            if declared {
                return true;
            }
            for e in cur.extends() {
                if let Some(em) = self.modules.get(&e.name) {
                    work.push(em);
                }
            }
        }
        false
    }

    /// Resolve a bare name through the instance being looked through, if any.
    fn ctx_resolve(&self, name: &str) -> Option<CtxResolution<'a>> {
        let ctx = self.ctx.last()?;
        if let Some(v) = ctx.subst.get(name) {
            return Some(CtxResolution::Value(Rc::clone(v)));
        }
        let def = self.module_defs.get(&ctx.module.name.name)?.get(name)?;
        Some(CtxResolution::Def(def.clone()))
    }

    /// Bind one fresh variable standing for a *tuple* of the `bounds`'
    /// variables, with each original name bound to its projection, and return
    /// that variable.
    ///
    /// Shared by every multi-variable binder, and shared on purpose: the
    /// projection rule is a semantic decision (`x` is component `i` of the
    /// bound tuple, counting across all the bounds, and a tuple pattern
    /// projects again inside that), and two copies of it would be two
    /// semantics to keep in agreement.
    fn bind_product(
        &mut self,
        bounds: &'a [Bound],
        scope: &mut HashMap<String, Binding<'a>>,
    ) -> Name {
        let tv = self.fresh_name("arg");
        let tvar = Kera::Var(tv.clone()).rc();
        let mut i = 0usize;
        for b in bounds {
            for p in &b.patterns {
                i += 1;
                let proj = Kera::FunApp(Rc::clone(&tvar), Kera::Int(i.to_string()).rc()).rc();
                match p {
                    Pattern::Name(id) => {
                        scope.insert(id.name.clone(), Binding::Value(proj));
                    }
                    Pattern::Tuple(ids) => {
                        for (j, id) in ids.iter().enumerate() {
                            let inner =
                                Kera::FunApp(Rc::clone(&proj), Kera::Int((j + 1).to_string()).rc())
                                    .rc();
                            scope.insert(id.name.clone(), Binding::Value(inner));
                        }
                    }
                }
            }
        }
        tv
    }

    /// Bind one fresh variable over the product of `bounds`, projecting the
    /// components out of it.
    ///
    /// Shared by `[x \in S, y \in T |-> e]` and `{e : x \in S, y \in T}`:
    /// both range over every *combination*, and both must end up with a single
    /// kernel binder. Nesting binders instead is wrong for the set map — it
    /// yields a set of sets — and wrong for the function, whose domain is the
    /// product.
    fn expand_product_binder(
        &mut self,
        e: &'a Expr,
        bounds: &'a [Bound],
        body: &'a Expr,
        stack: &mut Vec<Frame<'a>>,
    ) {
        let total: usize = bounds.iter().map(|b| b.patterns.len()).sum();
        let mut scope = HashMap::new();
        let tv = self.bind_product(bounds, &mut scope);
        self.binder_names.insert(e.span.start.offset, vec![tv]);
        stack.push(Frame::Build(e, total + 1));
        stack.push(Frame::PopScope);
        stack.push(Frame::Expand(body));
        stack.push(Frame::PushScope(scope));
        for b in bounds.iter().rev() {
            for _ in 0..b.patterns.len() {
                stack.push(Frame::Expand(&b.domain));
            }
        }
    }

    /// Whether this application is one of Apalache's folds rather than a
    /// definition that happens to share the name.
    ///
    /// The `Apa` prefix exists to reserve these names, so in practice the
    /// answer is yes. What this guards is the one case where it is not — and
    /// it cannot simply defer whenever a definition exists, because
    /// `Apalache.tla` defines both names itself, `RECURSIVE`, and deferring
    /// would defer to *that*. So a definition wins only when the application
    /// does not look like a fold: its first argument is not a two-parameter
    /// operator, and no reading of it as a fold was ever going to work.
    fn folds_here(&self, name: &str, args: &'a [Expr]) -> bool {
        if self.lookup(name).is_none() && !self.defs.contains_key(name) {
            return true;
        }
        let Some(first) = args.first() else {
            return false;
        };
        matches!(
            self.as_operator(first),
            Some(Binding::Op { params, .. }) if params.len() == 2
        )
    }

    /// Lower `ApaFoldSet(Op, base, S)` / `ApaFoldSeqLeft(Op, base, seq)`.
    ///
    /// The operator's body is lowered **once**, with its two parameters left
    /// free and renamed to fresh names; [`Kera::Fold`] records which names
    /// they are, and whoever consumes the fold binds them. Lowering it once is
    /// the point: a set's members are not known here, so there is nothing to
    /// unroll against, and the encoder is where the candidate list lives.
    ///
    /// The parameters are renamed rather than kept because the body is lowered
    /// into a term that may sit inside an enclosing binder. Every binder
    /// lowering introduces is unique, and a fold's parameters have to join that
    /// discipline: otherwise a fold under `\E p \in S` whose operator also
    /// calls a parameter `p` would capture it.
    fn expand_fold(
        &mut self,
        e: &'a Expr,
        over: FoldOver,
        args: &'a [Expr],
        span: Span,
        stack: &mut Vec<Frame<'a>>,
    ) -> Result<()> {
        self.expand_fold_with(e, over, args, false, span, stack)
    }

    /// The fold expansion proper, with the community modules' argument
    /// order available: their folds (`FoldSet`, `FoldSeq`, …) accumulate in
    /// the operator's **right** parameter — `op(element, accumulator)` —
    /// where `ApaFoldSet`/`ApaFoldSeqLeft` accumulate in the left, so the
    /// rewire binds the parameters the other way around rather than
    /// synthesizing a swapped operator.
    fn expand_fold_with(
        &mut self,
        e: &'a Expr,
        over: FoldOver,
        args: &'a [Expr],
        swapped: bool,
        span: Span,
        stack: &mut Vec<Frame<'a>>,
    ) -> Result<()> {
        let [op, base, collection] = args else {
            return Err(LowerError::unsupported(
                "a fold",
                "internal: a fold takes three arguments",
                span,
            ));
        };
        let Some(Binding::Op { params, body }) = self.as_operator(op) else {
            return Err(LowerError::unsupported(
                "this fold",
                "its first argument must be an operator: pass a defined \
                 two-parameter operator or a `LAMBDA`",
                op.span,
            ));
        };
        if params.len() != 2 {
            return Err(LowerError::new(
                LowerErrorKind::Arity {
                    name: "the folding operator".into(),
                    expected: 2,
                    found: params.len(),
                },
                op.span,
            ));
        }
        if params.iter().any(|(_, arity)| *arity > 0) {
            return Err(LowerError::unsupported(
                "this fold",
                "its operator takes an operator of its own, which the kernel \
                 has no way to carry",
                op.span,
            ));
        }
        let acc = self.fresh_name(&params[0].0);
        let elem = self.fresh_name(&params[1].0);
        let mut scope = HashMap::new();
        if swapped {
            scope.insert(
                params[0].0.clone(),
                Binding::Value(Kera::Var(elem.clone()).rc()),
            );
            scope.insert(
                params[1].0.clone(),
                Binding::Value(Kera::Var(acc.clone()).rc()),
            );
        } else {
            scope.insert(
                params[0].0.clone(),
                Binding::Value(Kera::Var(acc.clone()).rc()),
            );
            scope.insert(
                params[1].0.clone(),
                Binding::Value(Kera::Var(elem.clone()).rc()),
            );
        }
        self.binder_names
            .insert(e.span.start.offset, vec![acc.clone(), elem.clone()]);
        stack.push(Frame::BuildFold { over, acc, elem });
        stack.push(Frame::PopScope);
        stack.push(Frame::Expand(body));
        stack.push(Frame::PushScope(scope));
        stack.push(Frame::Expand(collection));
        stack.push(Frame::Expand(base));
        Ok(())
    }

    /// `FoldFunction(op, base, fun)` / `FoldFunctionOnSet(op, base, fun,
    /// indices)` — the community `Functions` module's folds over a
    /// function's *values*, per Apalache's `__rewire_functions`: a set fold
    /// over the indices whose body reads `op(fun[x], acc)`. The mapping
    /// argument is lowered once; the scope frame that binds the operator's
    /// parameters keeps that value for the body's reads and, for the
    /// three-argument form, builds the collection as `DOMAIN` of it.
    fn expand_mapped_fold(
        &mut self,
        e: &'a Expr,
        op: &'a Expr,
        base: &'a Expr,
        fun: &'a Expr,
        indices: Option<&'a Expr>,
        stack: &mut Vec<Frame<'a>>,
    ) -> Result<()> {
        let Some(Binding::Op { params, body }) = self.as_operator(op) else {
            return Err(LowerError::unsupported(
                "this fold",
                "its first argument must be an operator: pass a defined \
                 two-parameter operator or a `LAMBDA`",
                op.span,
            ));
        };
        if params.len() != 2 {
            return Err(LowerError::new(
                LowerErrorKind::Arity {
                    name: "the folding operator".into(),
                    expected: 2,
                    found: params.len(),
                },
                op.span,
            ));
        }
        if params.iter().any(|(_, arity)| *arity > 0) {
            return Err(LowerError::unsupported(
                "this fold",
                "its operator takes an operator of its own, which the kernel \
                 has no way to carry",
                op.span,
            ));
        }
        // The accumulator is `op`'s second parameter — these folds
        // accumulate on the right — and the element its first, bound to
        // `fun[x]`.
        let acc = self.fresh_name(&params[1].0);
        let elem = self.fresh_name(&params[0].0);
        self.binder_names
            .insert(e.span.start.offset, vec![acc.clone(), elem.clone()]);
        // Run order: base, the function, the collection (from the function's
        // `DOMAIN`, or the surface indices), the scope binding `op`'s
        // parameters, the body, the fold.
        stack.push(Frame::BuildFold {
            over: FoldOver::Set,
            acc: acc.clone(),
            elem: elem.clone(),
        });
        stack.push(Frame::PopScope);
        stack.push(Frame::Expand(body));
        stack.push(Frame::BindMappedFold {
            p0: params[0].0.clone(),
            p1: params[1].0.clone(),
            elem,
            acc,
            indices,
        });
        stack.push(Frame::Expand(fun));
        stack.push(Frame::Expand(base));
        Ok(())
    }

    fn expand(
        &mut self,
        e: &'a Expr,
        stack: &mut Vec<Frame<'a>>,
        values: &mut Vec<KeraRef>,
    ) -> Result<()> {
        let span = e.span;
        match &e.kind {
            ExprKind::Int { base, digits } => {
                let Some(dec) = digits_to_decimal(*base, digits) else {
                    return Err(LowerError::unsupported(
                        "this numeral",
                        "its digits are not valid in the base it was written in",
                        span,
                    ));
                };
                values.push(Kera::Int(dec).rc());
            }
            ExprKind::Str(s) => values.push(Kera::Str(s.clone()).rc()),
            ExprKind::Real(_) => {
                return Err(LowerError::unsupported(
                    "a real literal",
                    "the kernel has no real numbers; use integers, or `Reals` arithmetic \
                     once it is encoded",
                    span,
                ));
            }
            ExprKind::At => match self.lookup("@") {
                Some(Binding::Value(v)) => values.push(v),
                _ => {
                    return Err(LowerError::unsupported(
                        "`@`",
                        "it may only appear inside an `EXCEPT` update",
                        span,
                    ));
                }
            },
            ExprKind::Name(q) => {
                if q.is_qualified() {
                    let names: Vec<&str> = q.path.iter().map(|i| i.name.as_str()).collect();
                    let (Some(inst), Some(member)) = (names.first(), names.get(1)) else {
                        return Err(LowerError::unsupported(
                            "an instance-qualified name",
                            "internal: malformed path",
                            span,
                        ));
                    };
                    if names.len() > 2 {
                        return Err(LowerError::unsupported(
                            &format!("`{}`", names.join("!")),
                            "chained instance qualifiers are not resolved yet",
                            span,
                        ));
                    }
                    return self.push_instance_member(inst, member, &[], span, stack);
                }
                let Some(id) = q.base() else {
                    return Err(LowerError::unsupported("an empty name", "internal", span));
                };
                // Inside an instance, a bare name means the instantiated
                // module's symbol under that instance's substitution -- never
                // the instantiating module's same-named symbol.
                if self.lookup(&id.name).is_none()
                    && let Some(res) = self.ctx_resolve(&id.name)
                {
                    match res {
                        CtxResolution::Value(v) => values.push(v),
                        CtxResolution::Def(def) if def.params.is_empty() => {
                            stack.push(Frame::Inline {
                                name: id.name.clone(),
                                params: Vec::new(),
                                body: def.body,
                                span,
                                cache_as: None,
                            });
                        }
                        CtxResolution::Def(def) => {
                            return Err(LowerError::new(
                                LowerErrorKind::Arity {
                                    name: id.name.clone(),
                                    expected: def.params.len(),
                                    found: 0,
                                },
                                span,
                            ));
                        }
                    }
                    return Ok(());
                }
                match self.lookup(&id.name) {
                    Some(Binding::Value(v)) => values.push(v),
                    Some(Binding::Bound(n)) => values.push(Kera::Var(n).rc()),
                    // An operator parameter has no value of its own; only an
                    // application of it does.
                    Some(Binding::Op { params, .. }) => {
                        return Err(LowerError::new(
                            LowerErrorKind::Arity {
                                name: id.name.clone(),
                                expected: params.len(),
                                found: 0,
                            },
                            span,
                        ));
                    }
                    Some(Binding::BuiltinOp(_)) => {
                        return Err(LowerError::new(
                            LowerErrorKind::Arity {
                                name: id.name.clone(),
                                expected: 2,
                                found: 0,
                            },
                            span,
                        ));
                    }
                    // A value the TLC configuration pinned (`CONSTANT N = 3`).
                    // Substituted here rather than asserted as `N = 3`
                    // downstream, because that is what the configuration
                    // *means* — TLC replaces the constant — and because an
                    // equation the solver knows does not help the encoder:
                    // `1..N` needs a literal bound to have a candidate list at
                    // all, and an assumption arrives far too late for that.
                    None if self.constants.contains_key(&id.name) => {
                        if let Some(v) = self.constants.get(&id.name) {
                            values.push(Rc::clone(v));
                        }
                    }
                    None => match self.defs.get(&id.name).cloned() {
                        Some(def) if def.params.is_empty() => {
                            // Only a module-level definition may be shared,
                            // and only outside an instance, where the
                            // substitution would change what the body means.
                            let shareable = def.cacheable && self.ctx.is_empty();
                            if shareable && let Some(v) = self.cache.get(&id.name) {
                                values.push(Rc::clone(v));
                                return Ok(());
                            }
                            stack.push(Frame::Inline {
                                name: id.name.clone(),
                                params: Vec::new(),
                                body: def.body,
                                span,
                                cache_as: shareable.then(|| id.name.clone()),
                            });
                        }
                        // An operator named but not applied: it is being
                        // passed to something whose signature we do not know
                        // (an unresolved standard-module operator such as
                        // `ApaFoldSet`). Recorded as a zero-argument opaque
                        // reference so the operator's identity survives; the
                        // encoder must recognise it or decline.
                        Some(_) => {
                            values.push(Kera::Opaque(Name(id.name.clone()), Vec::new()).rc())
                        }
                        None => match self.funs.get(&id.name).cloned() {
                            // A reference from *inside* the definition is the
                            // recursion itself: kept as a free name, which
                            // `Kera::RecFun` binds.
                            Some(_) if self.recursing.contains(&id.name) => {
                                values.push(Kera::Var(Name(id.name.clone())).rc());
                            }
                            Some((bounds, body)) => {
                                stack.push(Frame::ExpandFun(id.name.clone(), bounds, body));
                            }
                            None if self.builtin_constant_probe(&id.name) => {
                                if let Some(v) = self.builtin_constant(&id.name) {
                                    values.push(v);
                                }
                            }
                            None => {
                                // An unnamed `INSTANCE M WITH …` makes M's
                                // members visible without a prefix.
                                let open = self.open_instances.iter().find(|i| {
                                    self.module_defs
                                        .get(&i.module.name.name)
                                        .is_some_and(|d| d.contains_key(&id.name))
                                });
                                match open.cloned() {
                                    Some(inst) => {
                                        self.push_instance_body(&inst, &id.name, &[], span, stack)?;
                                    }
                                    None => values.push(Kera::Var(Name(id.name.clone())).rc()),
                                }
                            }
                        },
                    },
                }
            }
            ExprKind::Apply { head, args } => {
                if head.is_qualified() {
                    let names: Vec<&str> = head.path.iter().map(|i| i.name.as_str()).collect();
                    let (Some(inst), Some(member)) = (names.first(), names.get(1)) else {
                        return Err(LowerError::unsupported(
                            "an instance-qualified application",
                            "internal: malformed path",
                            span,
                        ));
                    };
                    if names.len() > 2 {
                        return Err(LowerError::unsupported(
                            &format!("`{}`", names.join("!")),
                            "chained instance qualifiers are not resolved yet",
                            span,
                        ));
                    }
                    let arg_refs: Vec<&'a Expr> = args.iter().collect();
                    return self.push_instance_member(inst, member, &arg_refs, span, stack);
                }
                let Some(id) = head.base() else {
                    return Err(LowerError::unsupported("an empty name", "internal", span));
                };
                // Apalache's folds take an *operator* as their first argument,
                // and they are intercepted here rather than resolved. Two
                // reasons, both load-bearing:
                //
                // * `Apalache.tla` defines them `RECURSIVE`, peeling one
                //   `CHOOSE __x \in __S` at a time. Inlining that reaches the
                //   depth limit, so the specification does not lower at all
                //   wherever that module is on the search path.
                // * Unresolved, the operator argument lowered to a bare
                //   `Opaque(name, [])`: the *identity* survived and the body
                //   did not, so nothing downstream could apply it.
                //
                // A local `LET` or a parameter of the same name still wins, so
                // a specification that defines its own `ApaFoldSet` keeps it.
                if !head.is_qualified()
                    && let Some(over) = fold_kind(&id.name, args.len())
                    && self.folds_here(&id.name, args)
                {
                    return self.expand_fold(e, over, args, span, stack);
                }
                // `BagOfAll(F, B)`, through Apalache's own rewire
                // (`__rewire_bags_in_apalache.tla`): a fold over `DOMAIN B`
                // adding `[y \\in {F(e)} |-> B[e]]` to the accumulator. A
                // local definition of the same name still wins, exactly as
                // for the folds.
                // `SelectSeq(seq, F(_))` — Apalache's rewire to a left fold
                // that appends the elements `F` accepts. A local definition
                // of the same name still wins, exactly as for the folds.
                if !head.is_qualified()
                    && id.name == "SelectSeq"
                    && args.len() == 2
                    && self.lookup("SelectSeq").is_none()
                    && !self.defs.contains_key("SelectSeq")
                {
                    let [seq, test] = args.as_slice() else {
                        return Err(LowerError::unsupported(
                            "`SelectSeq`",
                            "internal: wrong argument count",
                            span,
                        ));
                    };
                    let Some(Binding::Op { params, body }) = self.as_operator(test) else {
                        return Err(LowerError::unsupported(
                            "`SelectSeq`",
                            "its second argument must be an operator: pass a defined \
                             operator name or a `LAMBDA`",
                            test.span,
                        ));
                    };
                    if params.len() != 1 {
                        return Err(LowerError::new(
                            LowerErrorKind::Arity {
                                name: "SelectSeq's operator".into(),
                                expected: 1,
                                found: params.len(),
                            },
                            test.span,
                        ));
                    }
                    let acc = self.fresh_name("sel_acc");
                    let elem = self.fresh_name("sel_e");
                    let mut tscope = HashMap::new();
                    tscope.insert(
                        params[0].0.clone(),
                        Binding::Value(Kera::Var(elem.clone()).rc()),
                    );
                    stack.push(Frame::BuildSelectSeq { acc, elem });
                    stack.push(Frame::PopScope);
                    stack.push(Frame::Expand(body));
                    stack.push(Frame::PushScope(tscope));
                    stack.push(Frame::Expand(seq));
                    return Ok(());
                }
                // `Repeat(F, N, x)`: N-fold application of F, with the step
                // index — Apalache's `RepeatRule` — as ONE ordered fold over
                // the literal sequence `<<1..N>>`, **literal N in 0..=64
                // only** (a symbolic count has no finite unfolding, and
                // Apalache errors on non-constant counts too). A sequence
                // fold, not a set fold: F need not be commutative, and the
                // order `Repeat` defines is the step order.
                if !head.is_qualified()
                    && id.name == "Repeat"
                    && args.len() == 3
                    && self.lookup("Repeat").is_none()
                    && !self.defs.contains_key("Repeat")
                {
                    let [op, count, start] = args.as_slice() else {
                        return Err(LowerError::unsupported(
                            "`Repeat`",
                            "internal: wrong argument count",
                            span,
                        ));
                    };
                    let Some(Binding::Op { params, body }) = self.as_operator(op) else {
                        return Err(LowerError::unsupported(
                            "`Repeat`",
                            "its first argument must be an operator: pass a defined \
                             operator name or a `LAMBDA`",
                            op.span,
                        ));
                    };
                    if params.len() != 2 {
                        return Err(LowerError::new(
                            LowerErrorKind::Arity {
                                name: "Repeat's operator".into(),
                                expected: 2,
                                found: params.len(),
                            },
                            op.span,
                        ));
                    }
                    let Some(n_big) = self.ground_int_expr(count) else {
                        return Err(LowerError::unsupported(
                            "`Repeat`",
                            "its count must be a literal (a symbolic count has no finite \
                             unfolding, and Apalache errors on it too)",
                            count.span,
                        ));
                    };
                    let Some(n) = self.int_of(&n_big) else {
                        return Err(LowerError::unsupported(
                            "`Repeat`",
                            "a count outside the unfolding budget",
                            count.span,
                        ));
                    };
                    if !(0..=64).contains(&n) {
                        return Err(LowerError::unsupported(
                            "`Repeat`",
                            "a count outside 0..=64 (the unfolding budget)",
                            count.span,
                        ));
                    }
                    let acc = self.fresh_name("rep_acc");
                    let elem = self.fresh_name("rep_i");
                    let items: Vec<KeraRef> =
                        (1..=n).map(|k| Kera::Int(k.to_string()).rc()).collect();
                    let mut scope = HashMap::new();
                    scope.insert(
                        params[0].0.clone(),
                        Binding::Value(Kera::Var(acc.clone()).rc()),
                    );
                    scope.insert(
                        params[1].0.clone(),
                        Binding::Value(Kera::Var(elem.clone()).rc()),
                    );
                    self.binder_names
                        .insert(e.span.start.offset, vec![acc.clone(), elem.clone()]);
                    stack.push(Frame::BuildFold {
                        over: FoldOver::SeqLeft,
                        acc,
                        elem,
                    });
                    stack.push(Frame::PopScope);
                    stack.push(Frame::Expand(body));
                    stack.push(Frame::PushScope(scope));
                    stack.push(Frame::Kera(Kera::Tuple(items).rc()));
                    stack.push(Frame::Expand(start));
                    return Ok(());
                }
                // `MkSeq(N, F)`: `[i \\in 1..N |-> F(i)]`, literal N only,
                // the operator intercepted here so `as_operator` can bind it
                // while it is still an `Expr`.
                if !head.is_qualified()
                    && id.name == "MkSeq"
                    && args.len() == 2
                    && self.lookup("MkSeq").is_none()
                    && !self.defs.contains_key("MkSeq")
                {
                    let [count, op] = args.as_slice() else {
                        return Err(LowerError::unsupported(
                            "`MkSeq`",
                            "internal: wrong argument count",
                            span,
                        ));
                    };
                    let Some(Binding::Op { params, body }) = self.as_operator(op) else {
                        return Err(LowerError::unsupported(
                            "`MkSeq`",
                            "its second argument must be an operator: pass a defined \
                             operator name or a `LAMBDA`",
                            op.span,
                        ));
                    };
                    if params.len() != 1 {
                        return Err(LowerError::new(
                            LowerErrorKind::Arity {
                                name: "MkSeq's operator".into(),
                                expected: 1,
                                found: params.len(),
                            },
                            op.span,
                        ));
                    }
                    let Some(n_big) = self.ground_int_expr(count) else {
                        return Err(LowerError::unsupported(
                            "`MkSeq`",
                            "its length must be a literal (a symbolic length has no enumerable \
                             domain)",
                            count.span,
                        ));
                    };
                    let Some(n) = self.int_of(&n_big) else {
                        return Err(LowerError::unsupported(
                            "`MkSeq`",
                            "a length outside the budget",
                            count.span,
                        ));
                    };
                    if !(0..=4096).contains(&n) {
                        return Err(LowerError::unsupported(
                            "`MkSeq`",
                            "a length outside 0..=4096 (the budget)",
                            count.span,
                        ));
                    }
                    let var = self.fresh_name("apa_i");
                    let mut scope = HashMap::new();
                    scope.insert(
                        params[0].0.clone(),
                        Binding::Value(Kera::Var(var.clone()).rc()),
                    );
                    stack.push(Frame::BuildMkSeq { var, n });
                    stack.push(Frame::PopScope);
                    stack.push(Frame::Expand(body));
                    stack.push(Frame::PushScope(scope));
                    return Ok(());
                }
                // `FunAsSeq(f, len[, capacity])` — Apalache's cast of a
                // function's `1..len` prefix to a sequence. Lowered as one
                // kernel operator the encoder builds exactly (a window over
                // the function's own array), so `len` may be symbolic. The
                // capacity is a hint Apalache's encoding needs and this one
                // does not — the window's length already makes reads past
                // `len` dead — so it is accepted and inert here, never
                // silently reinterpreted.
                if !head.is_qualified()
                    && id.name == "FunAsSeq"
                    && (args.len() == 2 || args.len() == 3)
                    && self.lookup("FunAsSeq").is_none()
                    && !self.defs.contains_key("FunAsSeq")
                {
                    let (f, len): (&'a Expr, &'a Expr) = match args.as_slice() {
                        [f, len, _cap] => (f, len),
                        [f, len] => (f, len),
                        _ => {
                            return Err(LowerError::unsupported(
                                "`FunAsSeq`",
                                "internal: wrong argument count",
                                span,
                            ));
                        }
                    };
                    stack.push(Frame::BuildFunAsSeq);
                    stack.push(Frame::Expand(len));
                    stack.push(Frame::Expand(f));
                    return Ok(());
                }
                // The community modules' folds, rewired exactly as
                // Apalache's `__rewire_*` modules rewire them:
                //
                // * `FoldSet(op, base, S)` (FiniteSetsExt) and
                //   `FoldSeq(op, base, seq)` (SequencesExt) accumulate in
                //   the operator's **right** parameter — `op(x, acc)` — so
                //   they are the kernel folds with the parameters bound the
                //   other way around.
                // * `FoldFunction(op, base, f)` / `FoldFunctionOnSet(op,
                //   base, f, I)` (Functions) fold over the *values* `f[x]`
                //   for `x \in I` (`DOMAIN f` for the former).
                //
                // A local definition of the same name still wins when the
                // application does not look like the fold — the same rule
                // `folds_here` applies to `ApaFoldSet`.
                if !head.is_qualified()
                    && matches!(
                        (id.name.as_str(), args.len()),
                        ("FoldSet", 3)
                            | ("FoldSeq", 3)
                            | ("FoldFunction", 3)
                            | ("FoldFunctionOnSet", 4)
                    )
                    && self.folds_here(&id.name, args)
                {
                    match (id.name.as_str(), args.len()) {
                        ("FoldSet", 3) => {
                            self.expand_fold_with(e, FoldOver::Set, args, true, span, stack)?;
                            return Ok(());
                        }
                        ("FoldSeq", 3) => {
                            self.expand_fold_with(e, FoldOver::SeqLeft, args, true, span, stack)?;
                            return Ok(());
                        }
                        ("FoldFunction", 3) => {
                            let [op, base, fun] = args.as_slice() else {
                                return Err(LowerError::unsupported(
                                    "`FoldFunction`",
                                    "internal: wrong argument count",
                                    span,
                                ));
                            };
                            self.expand_mapped_fold(e, op, base, fun, None, stack)?;
                            return Ok(());
                        }
                        ("FoldFunctionOnSet", 4) => {
                            let [op, base, fun, indices] = args.as_slice() else {
                                return Err(LowerError::unsupported(
                                    "`FoldFunctionOnSet`",
                                    "internal: wrong argument count",
                                    span,
                                ));
                            };
                            self.expand_mapped_fold(e, op, base, fun, Some(indices), stack)?;
                            return Ok(());
                        }
                        _ => {}
                    }
                }
                if !head.is_qualified()
                    && id.name == "BagOfAll"
                    && args.len() == 2
                    && self.lookup("BagOfAll").is_none()
                    && !self.defs.contains_key("BagOfAll")
                {
                    let [f, bag] = args.as_slice() else {
                        return Err(LowerError::unsupported(
                            "`BagOfAll`",
                            "internal: wrong argument count",
                            span,
                        ));
                    };
                    let Some(Binding::Op { params, body }) = self.as_operator(f) else {
                        return Err(LowerError::unsupported(
                            "`BagOfAll`",
                            "its first argument must be an operator: pass a defined                              operator name or a `LAMBDA`",
                            f.span,
                        ));
                    };
                    if params.len() != 1 {
                        return Err(LowerError::new(
                            LowerErrorKind::Arity {
                                name: "BagOfAll's operator".into(),
                                expected: 1,
                                found: params.len(),
                            },
                            f.span,
                        ));
                    }
                    let acc = self.fresh_name("bag_acc");
                    let elem = self.fresh_name("bag_e");
                    let out = self.fresh_name("bag_out");
                    // `F(elem)`: F's body lowered once, its parameter bound to
                    // the fold's element name.
                    let mut fscope = HashMap::new();
                    fscope.insert(
                        params[0].0.clone(),
                        Binding::Value(Kera::Var(elem.clone()).rc()),
                    );
                    stack.push(Frame::BuildBagOfAll { acc, elem, out });
                    stack.push(Frame::PopScope);
                    stack.push(Frame::Expand(body));
                    stack.push(Frame::PushScope(fscope));
                    stack.push(Frame::Expand(bag));
                    return Ok(());
                }
                // A parameter bound to a value cannot be applied: higher-order
                // parameters are inlined as values, and applying one needs the
                // operator itself, not its level.
                // Inside an instance, an application resolves against the
                // instantiated module first.
                if self.lookup(&id.name).is_none()
                    && let Some(CtxResolution::Def(def)) = self.ctx_resolve(&id.name)
                    && def.params.len() == args.len()
                {
                    stack.push(Frame::Inline {
                        name: id.name.clone(),
                        params: def.params.clone(),
                        body: def.body,
                        span,
                        cache_as: None,
                    });
                    for a in args.iter().rev() {
                        stack.push(Frame::Expand(a));
                    }
                    return Ok(());
                }
                // A parameter bound to a built-in symbol applies directly:
                // `Op(a, b)` with `Op` = `+` is the infix `+`, exactly.
                if let Some(Binding::BuiltinOp(sym)) = self.lookup(&id.name) {
                    let [x, y] = args.as_slice() else {
                        return Err(LowerError::new(
                            LowerErrorKind::Arity {
                                name: format!("the operator `{sym}`"),
                                expected: 2,
                                found: args.len(),
                            },
                            span,
                        ));
                    };
                    stack.push(Frame::BuildBuiltinOp { sym, span });
                    stack.push(Frame::Expand(y));
                    stack.push(Frame::Expand(x));
                    return Ok(());
                }
                // An operator *parameter* shadows a global definition.
                let bound_op = match self.lookup(&id.name) {
                    Some(Binding::Op { params, body }) => Some(Def {
                        params,
                        body,
                        cacheable: false,
                    }),
                    _ => None,
                };
                let resolved = bound_op.or_else(|| self.defs.get(&id.name).cloned());
                match resolved {
                    Some(def) if def.params.len() == args.len() => {
                        let mut ops: Vec<(String, Binding<'a>)> = Vec::new();
                        let mut value_args: Vec<&'a Expr> = Vec::new();
                        for ((pname, arity), arg) in def.params.iter().zip(args.iter()) {
                            if *arity == 0 {
                                value_args.push(arg);
                                continue;
                            }
                            let Some(b) = self.as_operator(arg) else {
                                return Err(LowerError::unsupported(
                                    "this higher-order argument",
                                    "a parameter declared as `F(_)` takes an operator: pass a \
                                     defined operator name or a `LAMBDA`",
                                    arg.span,
                                ));
                            };
                            ops.push((pname.clone(), b));
                        }
                        if !ops.is_empty() {
                            self.pending_ops.insert(span.start.offset, ops);
                        }
                        stack.push(Frame::Inline {
                            name: id.name.clone(),
                            params: def.params.clone(),
                            body: def.body,
                            span,
                            cache_as: None,
                        });
                        for a in value_args.into_iter().rev() {
                            stack.push(Frame::Expand(a));
                        }
                    }
                    Some(def) => {
                        return Err(LowerError::new(
                            LowerErrorKind::Arity {
                                name: id.name.clone(),
                                expected: def.params.len(),
                                found: args.len(),
                            },
                            span,
                        ));
                    }
                    None => {
                        stack.push(Frame::Build(e, args.len()));
                        for a in args.iter().rev() {
                            stack.push(Frame::Expand(a));
                        }
                    }
                }
            }
            ExprKind::Quant { kind, bounds, body } => {
                if matches!(kind, QuantKind::TemporalForall | QuantKind::TemporalExists) {
                    return Err(LowerError::unsupported(
                        "a temporal quantifier (`\\AA` / `\\EE`)",
                        "it quantifies over behaviours, which is spec structure rather than \
                         a kernel expression",
                        span,
                    ));
                }
                self.expand_binder_chain(e, bounds, body, stack);
            }
            ExprKind::UnboundedQuant { .. } => {
                return Err(LowerError::unsupported(
                    "an unbounded quantifier",
                    "give the bound variable a set to range over, as `\\A x \\in S : …`",
                    span,
                ));
            }
            ExprKind::Choose {
                pattern,
                domain,
                body,
            } => {
                let mut scope = HashMap::new();
                let Some(domain) = domain else {
                    // `CHOOSE x : P` is legal TLA+ and the standard idiom for
                    // a fresh value (`None == CHOOSE v : v \notin Values`), so
                    // the kernel carries it rather than rejecting it.
                    let name = self.bind_pattern(pattern, &mut scope);
                    self.binder_names.insert(span.start.offset, vec![name]);
                    stack.push(Frame::Build(e, 1));
                    stack.push(Frame::PopScope);
                    stack.push(Frame::Expand(body));
                    stack.push(Frame::PushScope(scope));
                    return Ok(());
                };
                let name = self.bind_pattern(pattern, &mut scope);
                self.binder_names.insert(span.start.offset, vec![name]);
                stack.push(Frame::Build(e, 2));
                stack.push(Frame::PopScope);
                stack.push(Frame::Expand(body));
                stack.push(Frame::PushScope(scope));
                stack.push(Frame::Expand(domain));
            }
            ExprKind::SetFilter {
                pattern,
                domain,
                pred,
            } => {
                let mut scope = HashMap::new();
                let name = self.bind_pattern(pattern, &mut scope);
                self.binder_names.insert(span.start.offset, vec![name]);
                stack.push(Frame::Build(e, 2));
                stack.push(Frame::PopScope);
                stack.push(Frame::Expand(pred));
                stack.push(Frame::PushScope(scope));
                stack.push(Frame::Expand(domain));
            }
            ExprKind::SetMap { expr, bounds } => {
                let total: usize = bounds.iter().map(|b| b.patterns.len()).sum();
                if total == 1 {
                    self.expand_binder_chain(e, bounds, expr, stack);
                } else {
                    // `{e : x \in S, y \in T}` collects `e` over every
                    // *combination*, giving one flat set. Nesting the binders
                    // instead produced a set of sets — `{{<<1, 2>>}}` where
                    // TLC gives `{<<1, 2>>}`. One variable ranges over the
                    // product and the components are projected out, the same
                    // shape a multi-variable function constructor uses.
                    self.expand_product_binder(e, bounds, expr, stack);
                }
            }
            ExprKind::FnConstruct { bounds, body } => {
                let total: usize = bounds.iter().map(|b| b.patterns.len()).sum();
                if total == 1 {
                    self.expand_binder_chain(e, bounds, body, stack);
                } else {
                    self.expand_product_binder(e, bounds, body, stack);
                }
            }
            ExprKind::Let { defs, body } => {
                let mut saved: Vec<(String, Option<Def<'a>>)> = Vec::new();
                let mut saved_insts: Vec<(String, Option<Instantiation<'a>>)> = Vec::new();
                for d in defs {
                    match &d.kind {
                        UnitKind::OpDef {
                            name, params, body, ..
                        } => {
                            let def = Def {
                                params: params
                                    .iter()
                                    .map(|p| (p.name.name.clone(), p.arity))
                                    .collect(),
                                body,
                                cacheable: false,
                            };
                            saved.push((
                                name.name.clone(),
                                self.defs.insert(name.name.clone(), def),
                            ));
                        }
                        UnitKind::FnDef {
                            name, bounds, body, ..
                        } => {
                            self.funs
                                .insert(name.name.clone(), (bounds.as_slice(), body));
                            saved.push((name.name.clone(), None));
                        }
                        // `LET M == INSTANCE A [WITH …] IN …`: the instance is
                        // scoped exactly like the definitions around it —
                        // visible in the `IN` body, restored afterwards, and
                        // shadowing a module-level instance of the same name
                        // for that extent. test59.tla's `Next` is the case.
                        UnitKind::ModuleDef {
                            name,
                            params,
                            instance,
                            ..
                        } => {
                            let Some(target) = self.modules.get(&instance.module.name).copied()
                            else {
                                return Err(LowerError::unsupported(
                                    &format!("`{}`!…", name.name),
                                    &format!(
                                        "the instantiated module `{}` was not found on the \
                                         search path",
                                        instance.module.name
                                    ),
                                    d.span,
                                ));
                            };
                            let inst = Instantiation {
                                module: target,
                                // The declaring scope is the module the walk
                                // is inside (or an instance member of it);
                                // recorded at use time, not here, because at
                                // this point only the frames know.
                                source: None,
                                with: instance
                                    .substitutions
                                    .iter()
                                    .map(|(n, e)| (n.name.clone(), e))
                                    .collect(),
                                params: params.iter().map(|p| p.name.name.clone()).collect(),
                            };
                            saved_insts.push((
                                name.name.clone(),
                                self.instances.insert(name.name.clone(), inst),
                            ));
                        }
                        // A bare `INSTANCE M` unit cannot appear inside a
                        // `LET` (its grammar is `name == INSTANCE …`), and the
                        // parser cannot produce it there. If that ever
                        // changes, refusing is the honest outcome — dropping
                        // it silently would surface much later as a
                        // name-resolution error pointing at the use.
                        UnitKind::Instance { .. } => {
                            return Err(LowerError::unsupported(
                                "an `INSTANCE` inside `LET`",
                                "a `LET`-scoped instance must be named, `M == INSTANCE …`",
                                d.span,
                            ));
                        }
                        UnitKind::Recursive(_) => {
                            return Err(LowerError::unsupported(
                                "`RECURSIVE` inside `LET`",
                                "a recursive operator has no finite unfolding; rewrite it as a \
                                 fold over a finite set, or a function `[x \\in S |-> …]`",
                                d.span,
                            ));
                        }
                        UnitKind::ConstantDecl(_)
                        | UnitKind::VariableDecl(_)
                        | UnitKind::Extends(_)
                        | UnitKind::Assume { .. }
                        | UnitKind::Theorem { .. }
                        | UnitKind::ProofDirective(_)
                        | UnitKind::Separator
                        | UnitKind::Submodule(_) => {}
                    }
                }
                stack.push(Frame::PopLetDefs(saved, saved_insts));
                stack.push(Frame::Expand(body));
            }
            ExprKind::Except { base, updates } => {
                // Children, in order: the base, then per update every index
                // expression followed by the replacement value. `@` is bound
                // around each value by a `BindExceptAt` frame.
                let nchildren: usize = 1 + updates.iter().map(|u| 1 + u.path.len()).sum::<usize>();
                stack.push(Frame::Build(e, nchildren));
                // Each update needs to know the shape of the ones before it,
                // both to find the function on the shared value stack and to
                // rebuild what `@` refers to. Collected forwards, then used as
                // the frames are pushed in reverse.
                let path_lens: Vec<usize> = updates.iter().map(|u| u.path.len()).collect();
                for (k, u) in updates.iter().enumerate().rev() {
                    let path_len = path_lens.get(k).copied().unwrap_or(0);
                    stack.push(Frame::PopScope);
                    stack.push(Frame::Expand(&u.value));
                    stack.push(Frame::BindExceptAt {
                        path_len,
                        before: path_lens.get(..k).unwrap_or(&[]).to_vec(),
                    });
                    for sel in u.path.iter().rev() {
                        match sel {
                            // One selector is one *index*, and `![i, j]` is a
                            // single application of a function of two
                            // arguments — which in TLA+ is a function of the
                            // pair. Flattening it into two steps reads it as
                            // `f[i][j]`, a different function and a different
                            // value; TLC gives
                            // `[f EXCEPT ![1,2] = 99][<<1,2>>] = 99`, not a
                            // nested update. `ExprKind::FnApply` already
                            // builds the tuple, so this is also what makes the
                            // two agree.
                            ExceptSel::Index(ix) if ix.len() == 1 => {
                                for i in ix {
                                    stack.push(Frame::Expand(i));
                                }
                            }
                            ExceptSel::Index(ix) => {
                                stack.push(Frame::BuildTuple(ix.len()));
                                for i in ix.iter().rev() {
                                    stack.push(Frame::Expand(i));
                                }
                            }
                            ExceptSel::Field(f) => {
                                stack.push(Frame::PushLiteral(Kera::Str(f.name.clone()).rc()));
                            }
                        }
                    }
                }
                stack.push(Frame::Expand(base));
            }
            // A higher-order *parameter* whose spelling is an operator
            // symbol — `Foo(a, _--_) == a -- 0`, applied at `a -- 0` — binds
            // the operator passed at the call site (`Foo(7, +)`, `Foo(7,
            // ++)`, a `LAMBDA`). Scope wins over a module-level definition of
            // the same spelling, which is what shadowing means and what the
            // application path already does for named parameters. test42.tla
            // is the case.
            ExprKind::Infix { op, lhs, rhs, .. }
                if matches!(
                    self.lookup(op.as_str()),
                    Some(Binding::Op { .. }) | Some(Binding::BuiltinOp(_))
                ) =>
            {
                match self.lookup(op.as_str()) {
                    Some(Binding::BuiltinOp(sym)) => {
                        stack.push(Frame::BuildBuiltinOp { sym, span });
                        stack.push(Frame::Expand(rhs));
                        stack.push(Frame::Expand(lhs));
                    }
                    Some(Binding::Op { params, body }) if params.len() == 2 => {
                        stack.push(Frame::Inline {
                            name: op.clone(),
                            params,
                            body,
                            span,
                            cache_as: None,
                        });
                        stack.push(Frame::Expand(rhs));
                        stack.push(Frame::Expand(lhs));
                    }
                    Some(Binding::Op { params, .. }) => {
                        return Err(LowerError::new(
                            LowerErrorKind::Arity {
                                name: op.clone(),
                                expected: params.len(),
                                found: 2,
                            },
                            span,
                        ));
                    }
                    // The guard admits exactly the shapes above; reaching
                    // this arm means a binding vanished mid-walk, which is
                    // an internal defect to report, never to guess around.
                    _ => {
                        return Err(LowerError::unsupported(
                            &format!("the operator `{op}`"),
                            "internal: its operator binding disappeared from scope mid-walk",
                            span,
                        ));
                    }
                }
            }
            ExprKind::Prefix { op, operand, .. } | ExprKind::Postfix { op, operand, .. }
                if matches!(self.lookup(op.as_str()), Some(Binding::Op { .. })) =>
            {
                match self.lookup(op.as_str()) {
                    Some(Binding::Op { params, body }) if params.len() == 1 => {
                        stack.push(Frame::Inline {
                            name: op.clone(),
                            params,
                            body,
                            span,
                            cache_as: None,
                        });
                        stack.push(Frame::Expand(operand));
                    }
                    Some(Binding::Op { params, .. }) => {
                        return Err(LowerError::new(
                            LowerErrorKind::Arity {
                                name: op.clone(),
                                expected: params.len(),
                                found: 1,
                            },
                            span,
                        ));
                    }
                    // A built-in operator symbol is always binary, so a
                    // prefix/postfix use of one can only be this internal
                    // defect; report it rather than guessing a meaning.
                    _ => {
                        return Err(LowerError::unsupported(
                            &format!("the operator `{op}`"),
                            "internal: its operator binding disappeared from scope mid-walk",
                            span,
                        ));
                    }
                }
            }
            // A user-defined operator symbol: `a \oplus b == …`, `-. z == …`.
            // The definition is registered under its spelling, so it must be
            // consulted before the built-in rules — otherwise every spec that
            // defines an infix operator fails to lower.
            ExprKind::Infix { op, lhs, rhs, .. } if self.defs.contains_key(op.as_str()) => {
                self.push_symbol_inline(op, &[lhs, rhs], span, stack)?;
            }
            ExprKind::Prefix { op, operand, .. } | ExprKind::Postfix { op, operand, .. }
                if self.defs.contains_key(op.as_str()) =>
            {
                self.push_symbol_inline(op, &[operand], span, stack)?;
            }
            // Everything else is "lower the children, then build".
            _ => {
                let kids = surface_children(e);
                stack.push(Frame::Build(e, kids.len()));
                for c in kids.into_iter().rev() {
                    stack.push(Frame::Expand(c));
                }
            }
        }
        Ok(())
    }
}

/// What a bare name means inside an instance.
enum CtxResolution<'a> {
    /// A declared name of the instantiated module, replaced by `WITH`.
    Value(KeraRef),
    /// A definition of the instantiated module, to be looked through as well.
    Def(Def<'a>),
}

/// The children `Frame::Build` will find on the value stack, in order, for the
/// nodes handled by the generic path.
fn surface_children(e: &Expr) -> Vec<&Expr> {
    let mut out: Vec<&Expr> = Vec::new();
    match &e.kind {
        ExprKind::Prefix { operand, .. } | ExprKind::Postfix { operand, .. } => out.push(operand),
        ExprKind::Infix { lhs, rhs, .. } => {
            out.push(lhs);
            out.push(rhs);
        }
        ExprKind::Junction { items, .. } | ExprKind::SetEnum(items) | ExprKind::Tuple(items) => {
            out.extend(items);
        }
        ExprKind::Paren(inner) | ExprKind::Label { body: inner, .. } => out.push(inner),
        ExprKind::Field { record, .. } => out.push(record),
        ExprKind::FnApply { func, args } => {
            out.push(func);
            out.extend(args);
        }
        ExprKind::FnSet { domain, codomain } => {
            out.push(domain);
            out.push(codomain);
        }
        ExprKind::RecordLit(fs) | ExprKind::RecordSet(fs) => {
            out.extend(fs.iter().map(|(_, v)| v));
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            out.push(cond);
            out.push(then_branch);
            out.push(else_branch);
        }
        ExprKind::Case { arms, other } => {
            for a in arms {
                out.push(&a.guard);
                out.push(&a.value);
            }
            out.extend(other.iter().map(AsRef::as_ref));
        }
        ExprKind::Apply { args, .. } => out.extend(args),
        _ => {}
    }
    out
}

impl<'a> Lowerer<'a> {
    /// Build one kernel node from the `n` values its children left on the stack.
    fn build(&mut self, e: &'a Expr, values: &mut Vec<KeraRef>, n: usize) -> Result<KeraRef> {
        let span = e.span;
        let at = values.len().checked_sub(n).ok_or_else(|| {
            LowerError::unsupported("this expression", "internal: value stack underflow", span)
        })?;
        let kids: Vec<KeraRef> = values.split_off(at);
        let take = |i: usize| -> Result<KeraRef> {
            kids.get(i).cloned().ok_or_else(|| {
                LowerError::unsupported("this expression", "internal: missing child", span)
            })
        };

        let built = match &e.kind {
            ExprKind::Paren(_) | ExprKind::Label { .. } => take(0)?,
            ExprKind::Junction { kind, .. } => match kind {
                nixie_tla_syntax::ast::Junct::And => Kera::And(kids).rc(),
                nixie_tla_syntax::ast::Junct::Or => Kera::Or(kids).rc(),
            },
            ExprKind::SetEnum(_) => Kera::SetEnum(kids).rc(),
            ExprKind::Tuple(_) => Kera::Tuple(kids).rc(),
            ExprKind::Field { field, .. } => {
                Kera::FunApp(take(0)?, Kera::Str(field.name.clone()).rc()).rc()
            }
            ExprKind::FnApply { .. } => {
                let f = take(0)?;
                let args: Vec<KeraRef> = kids.iter().skip(1).cloned().collect();
                match args.len() {
                    // `f[a, b]` is `f[<<a, b>>]` in TLA+.
                    0 => {
                        return Err(LowerError::unsupported(
                            "a function application with no argument",
                            "internal",
                            span,
                        ));
                    }
                    1 => Kera::FunApp(f, take(1)?).rc(),
                    _ => Kera::FunApp(f, Kera::Tuple(args).rc()).rc(),
                }
            }
            ExprKind::FnSet { .. } => Kera::FunSet {
                set: take(0)?,
                cod: take(1)?,
            }
            .rc(),
            ExprKind::RecordLit(fs) => {
                let fields = fs
                    .iter()
                    .zip(kids.iter())
                    .map(|((name, _), v)| (name.name.clone(), Rc::clone(v)))
                    .collect();
                Kera::Record(sort_fields(fields)).rc()
            }
            ExprKind::RecordSet(fs) => {
                let fields = fs
                    .iter()
                    .zip(kids.iter())
                    .map(|((name, _), v)| (name.name.clone(), Rc::clone(v)))
                    .collect();
                Kera::RecordSet(sort_fields(fields)).rc()
            }
            ExprKind::If { .. } => Kera::Ite(take(0)?, take(1)?, take(2)?).rc(),
            ExprKind::Case { arms, other } => build_case(arms, other.is_some(), &kids, span)?,
            ExprKind::Apply { head, .. } => {
                let Some(id) = head.base() else {
                    return Err(LowerError::unsupported("an empty name", "internal", span));
                };
                // The Apalache standard-library operators, in Apalache's own
                // order: `StandardLibrary` maps (module, name) to built-ins
                // *before* user definitions are consulted, but a user's own
                // definition of the same name still wins — checked by the
                // caller's `lookup`/`defs` resolution having failed to reach
                // here, and by `apalache_op` refusing shadowed names below
                // at the sites that need it.
                if let Some(k) = self.apalache_op(&id.name, &kids, e.span)? {
                    k
                }
                // The `Bags` standard-module vocabulary desugars to the
                // module's own definitions before anything else sees it.
                else if let Some(k) = self.bag_desugar(&id.name, &kids) {
                    k
                } else {
                    Kera::Opaque(Name(id.name.clone()), kids).rc()
                }
            }
            // `A \X B \X C` is a *ternary* product in TLA+ — a set of
            // 3-tuples — not `(A \X B) \X C`, which is a set of pairs whose
            // first component is a pair. The parser makes `\X` associative so
            // the chain parses; flattening it is this step's job, and not
            // doing it produced `{<<<<1, 2>>, 3>>}` where TLC gives
            // `{<<1, 2, 3>>}`.
            //
            // Only associativity-derived nesting is flattened. Explicit
            // parentheses mean the nested reading, and TLA+ distinguishes the
            // two, so a parenthesised left operand is left alone.
            ExprKind::Infix { op, lhs, .. } if op == "\\X" => {
                let a = take(0)?;
                let b = take(1)?;
                let from_assoc = matches!(&lhs.kind, ExprKind::Infix { op: l, .. } if l == "\\X");
                match (from_assoc, a.as_ref()) {
                    (true, Kera::Times(parts)) => {
                        let mut v = parts.clone();
                        v.push(b);
                        Kera::Times(v).rc()
                    }
                    _ => Kera::Times(vec![a, b]).rc(),
                }
            }
            ExprKind::Prefix { op, .. } => build_prefix(op, take(0)?, span)?,
            ExprKind::Postfix { op, .. } => match op.as_str() {
                "'" => Kera::Prime(take(0)?).rc(),
                other => Kera::Opaque(Name(other.to_string()), vec![take(0)?]).rc(),
            },
            ExprKind::Infix { op, .. } => {
                let (a, b) = (take(0)?, take(1)?);
                if let Some(k) = self.bag_desugar(op, &[Rc::clone(&a), Rc::clone(&b)]) {
                    k
                } else {
                    build_infix(op, a, b, span, &mut self.fresh)?
                }
            }
            ExprKind::Quant { kind, .. } => {
                let names = self.take_binder_names(span);
                let body = kids.last().cloned().ok_or_else(|| {
                    LowerError::unsupported("a quantifier", "internal: no body", span)
                })?;
                let mut acc = body;
                for (i, var) in names.iter().enumerate().rev() {
                    let set = take(i)?;
                    acc = match kind {
                        QuantKind::Forall => Kera::Forall {
                            var: var.clone(),
                            set,
                            body: acc,
                        },
                        _ => Kera::Exists {
                            var: var.clone(),
                            set,
                            body: acc,
                        },
                    }
                    .rc();
                }
                acc
            }
            ExprKind::SetMap { bounds, .. } => {
                let names = self.take_binder_names(span);
                let expr = kids.last().cloned().ok_or_else(|| {
                    LowerError::unsupported("a set map", "internal: no body", span)
                })?;
                let total: usize = bounds.iter().map(|b| b.patterns.len()).sum();
                if total > 1 {
                    // One binder over the product; see `expand_product_binder`.
                    let Some(var) = names.first().cloned() else {
                        return Err(LowerError::unsupported("a set map", "internal", span));
                    };
                    let doms: Vec<KeraRef> = kids.iter().take(total).cloned().collect();
                    Kera::Map {
                        var,
                        set: Kera::Times(doms).rc(),
                        expr,
                    }
                    .rc()
                } else {
                    let mut acc = expr;
                    for (i, var) in names.iter().enumerate().rev() {
                        acc = Kera::Map {
                            var: var.clone(),
                            set: take(i)?,
                            expr: acc,
                        }
                        .rc();
                    }
                    acc
                }
            }
            ExprKind::FnConstruct { .. } => {
                let names = self.take_binder_names(span);
                let Some(var) = names.first().cloned() else {
                    return Err(LowerError::unsupported("a function", "internal", span));
                };
                let body = kids.last().cloned().ok_or_else(|| {
                    LowerError::unsupported("a function", "internal: no body", span)
                })?;
                // One domain, or a product of them for a multi-variable form.
                let ndomains = kids.len().saturating_sub(1);
                let set = if ndomains <= 1 {
                    take(0)?
                } else {
                    let doms: Vec<KeraRef> = kids.iter().take(ndomains).cloned().collect();
                    Kera::Times(doms).rc()
                };
                Kera::FunDef { var, set, body }.rc()
            }
            ExprKind::Choose { domain, .. } => {
                let names = self.take_binder_names(span);
                let Some(var) = names.first().cloned() else {
                    return Err(LowerError::unsupported("a `CHOOSE`", "internal", span));
                };
                if domain.is_some() {
                    Kera::Choose {
                        var,
                        set: take(0)?,
                        body: take(1)?,
                    }
                    .rc()
                } else {
                    Kera::ChooseUnbounded {
                        var,
                        body: take(0)?,
                    }
                    .rc()
                }
            }
            ExprKind::SetFilter { .. } => {
                let names = self.take_binder_names(span);
                let Some(var) = names.first().cloned() else {
                    return Err(LowerError::unsupported("a set filter", "internal", span));
                };
                Kera::Filter {
                    var,
                    set: take(0)?,
                    pred: take(1)?,
                }
                .rc()
            }
            ExprKind::Except { updates, .. } => build_except(updates, &kids, span)?,
            other => {
                return Err(LowerError::unsupported(
                    &format!("{}", DescribeKind(other)),
                    "it has no kernel form",
                    span,
                ));
            }
        };
        Ok(built)
    }

    fn take_binder_names(&mut self, span: Span) -> Vec<Name> {
        self.binder_names
            .remove(&span.start.offset)
            .unwrap_or_default()
    }
}

/// `CASE p -> a [] q -> b [] OTHER -> c` becomes nested `IF`s.
fn build_case(arms: &[CaseArm], has_other: bool, kids: &[KeraRef], span: Span) -> Result<KeraRef> {
    // Children are guard, value, guard, value, …, then the `OTHER` value.
    let mut acc = if has_other {
        kids.last().cloned().ok_or_else(|| {
            LowerError::unsupported("a `CASE`", "internal: missing `OTHER` value", span)
        })?
    } else {
        // TLA+ leaves `CASE` with no matching arm undefined. Marking it
        // explicitly is the honest lowering: a silent default here would be a
        // fabricated value, which `AGENTS.md` forbids outright.
        Kera::Opaque(Name("$CaseNoMatch".to_string()), Vec::new()).rc()
    };
    for i in (0..arms.len()).rev() {
        let guard = kids
            .get(2 * i)
            .cloned()
            .ok_or_else(|| LowerError::unsupported("a `CASE`", "internal: missing guard", span))?;
        let value = kids.get(2 * i + 1).cloned().ok_or_else(|| {
            LowerError::unsupported("a `CASE`", "internal: missing arm value", span)
        })?;
        acc = Kera::Ite(guard, value, acc).rc();
    }
    Ok(acc)
}

/// `[f EXCEPT !p1 = v1, !p2 = v2]` becomes nested single-step updates.
fn build_except(
    updates: &[nixie_tla_syntax::ast::ExceptUpdate],
    kids: &[KeraRef],
    span: Span,
) -> Result<KeraRef> {
    let mut acc = kids
        .first()
        .cloned()
        .ok_or_else(|| LowerError::unsupported("an `EXCEPT`", "internal: no base", span))?;
    let mut at = 1usize;
    for u in updates {
        let path_len: usize = u.path.len();
        let path: Vec<KeraRef> = kids
            .get(at..at + path_len)
            .map(<[KeraRef]>::to_vec)
            .ok_or_else(|| {
                LowerError::unsupported("an `EXCEPT`", "internal: missing path", span)
            })?;
        let value = kids.get(at + path_len).cloned().ok_or_else(|| {
            LowerError::unsupported("an `EXCEPT`", "internal: missing value", span)
        })?;
        at += path_len + 1;
        acc = nest_except(acc, &path, value, span)?;
    }
    Ok(acc)
}

/// `[f EXCEPT ![i][j] = v]` is `[f EXCEPT ![i] = [f[i] EXCEPT ![j] = v]]`.
fn nest_except(fun: KeraRef, path: &[KeraRef], value: KeraRef, span: Span) -> Result<KeraRef> {
    let Some((head, rest)) = path.split_first() else {
        return Err(LowerError::unsupported(
            "an `EXCEPT` with an empty path",
            "internal",
            span,
        ));
    };
    if rest.is_empty() {
        return Ok(Kera::Except {
            fun,
            index: Rc::clone(head),
            value,
        }
        .rc());
    }
    let inner_base = Kera::FunApp(Rc::clone(&fun), Rc::clone(head)).rc();
    let inner = nest_except(inner_base, rest, value, span)?;
    Ok(Kera::Except {
        fun,
        index: Rc::clone(head),
        value: inner,
    }
    .rc())
}

fn build_prefix(op: &str, operand: KeraRef, span: Span) -> Result<KeraRef> {
    let k = match op {
        "~" => Kera::Not(operand),
        "-." => Kera::Neg(operand),
        "SUBSET" => Kera::Powerset(operand),
        "UNION" => Kera::BigUnion(operand),
        "DOMAIN" => Kera::Domain(operand),
        "UNCHANGED" => return Ok(unchanged(operand)),
        "[]" | "<>" => {
            return Err(LowerError::unsupported(
                &format!("the temporal operator `{op}`"),
                "temporal operators describe behaviours, not states; they belong to the \
                 spec's structure rather than to a kernel expression",
                span,
            ));
        }
        "ENABLED" => {
            return Err(LowerError::unsupported(
                "`ENABLED`",
                "it quantifies over successor states and needs the transition relation, \
                 which the kernel does not carry",
                span,
            ));
        }
        // A prefix operator from a standard module with no kernel node of its
        // own. Recorded by name rather than rejected: it is a *primitive* the
        // encoder must implement or decline, not something to expand here.
        // This is not a silent default -- nothing is dropped and nothing is
        // invented, the operator is carried through under its own name.
        other => Kera::Opaque(Name(other.to_string()), vec![operand]),
    };
    Ok(k.rc())
}

/// `UNCHANGED e` is `e' = e`, componentwise for a tuple.
fn unchanged(e: KeraRef) -> KeraRef {
    if let Kera::Tuple(items) = e.as_ref() {
        let conjuncts = items
            .iter()
            .map(|i| Kera::Eq(Kera::Prime(Rc::clone(i)).rc(), Rc::clone(i)).rc())
            .collect();
        return Kera::And(conjuncts).rc();
    }
    Kera::Eq(Kera::Prime(Rc::clone(&e)).rc(), e).rc()
}

fn mk_fresh(counter: &mut usize, base: &str) -> Name {
    *counter += 1;
    Name(format!("{base}#{counter}"))
}

fn build_infix(op: &str, a: KeraRef, b: KeraRef, span: Span, fresh: &mut usize) -> Result<KeraRef> {
    let k = match op {
        "=" => Kera::Eq(a, b),
        "/=" => Kera::Not(Kera::Eq(a, b).rc()),
        "\\in" => Kera::In(a, b),
        "\\notin" => Kera::Not(Kera::In(a, b).rc()),
        "/\\" => Kera::And(vec![a, b]),
        "\\/" => Kera::Or(vec![a, b]),
        "=>" => Kera::Or(vec![Kera::Not(a).rc(), b]),
        "<=>" => Kera::Eq(a, b),
        "\\cup" => Kera::SetBin(SetOp::Union, a, b),
        "\\cap" => Kera::SetBin(SetOp::Intersect, a, b),
        "\\" => Kera::SetBin(SetOp::Difference, a, b),
        "\\subseteq" => {
            // The one set relation without a kernel node: it is a quantifier
            // in every encoding, so expanding it here loses nothing.
            let v = Name("sub#0".to_string());
            Kera::Forall {
                var: v.clone(),
                set: a,
                body: Kera::In(Kera::Var(v).rc(), b).rc(),
            }
        }
        ".." => Kera::Range(a, b),
        "\\X" => Kera::Times(vec![a, b]),
        "+" => Kera::Arith(ArithOp::Add, a, b),
        "-" => Kera::Arith(ArithOp::Sub, a, b),
        "*" => Kera::Arith(ArithOp::Mul, a, b),
        "\\div" => Kera::Arith(ArithOp::Div, a, b),
        "%" => Kera::Arith(ArithOp::Mod, a, b),
        "^" => Kera::Arith(ArithOp::Exp, a, b),
        "<" => Kera::Cmp(CmpOp::Lt, a, b),
        "<=" => Kera::Cmp(CmpOp::Le, a, b),
        ">" => Kera::Cmp(CmpOp::Gt, a, b),
        ">=" => Kera::Cmp(CmpOp::Ge, a, b),
        "~>" | "-+->" | "\\cdot" => {
            return Err(LowerError::unsupported(
                &format!("the operator `{op}`"),
                "it relates behaviours or actions, which is spec structure rather than a \
                 kernel expression",
                span,
            ));
        }
        // Apalache's function constructors, exact at the kernel: `:>`/`:=`
        // build a one-entry function, `@@` merges with the right side
        // winning. Both are value-level, so the already-lowered operands are
        // exactly what the constructors want. A local definition of the same
        // name cannot exist (these are operators, not names a module can
        // rebind in scope).
        ":>" | ":=" => Kera::FunDef {
            var: mk_fresh(fresh, "apa_dom"),
            set: Kera::SetEnum(vec![a]).rc(),
            body: b,
        },
        "@@" => {
            let var = mk_fresh(fresh, "apa_e");
            let e = Kera::Var(var.clone()).rc();
            let dom = Kera::SetBin(
                SetOp::Union,
                Kera::Domain(a.clone()).rc(),
                Kera::Domain(b.clone()).rc(),
            )
            .rc();
            // LEFT wins on a shared key: Apalache's own rewire tests
            // `x \in DOMAIN f1` first (`__rewire_tlc_in_apalache.tla:38`),
            // and TLC's module agrees — the first test of this change had
            // it backwards.
            let in_f = Kera::In(Rc::clone(&e), Kera::Domain(a.clone()).rc()).rc();
            let read_f = Kera::FunApp(a, Rc::clone(&e)).rc();
            let read_g = Kera::FunApp(b, Rc::clone(&e)).rc();
            let body = Kera::Ite(in_f, read_f, read_g).rc();
            Kera::FunDef {
                var,
                set: dom,
                body,
            }
        }
        // An infix operator from a standard module -- `\o` from `Sequences`,
        // `\oplus` from a user's own module. Carried through by name for
        // the encoder to implement or decline. See the note in
        // `build_prefix`.
        other => Kera::Opaque(Name(other.to_string()), vec![a, b]),
    };
    Ok(k.rc())
}

/// Names a surface node for a diagnostic.
struct DescribeKind<'a>(&'a ExprKind);

impl core::fmt::Display for DescribeKind<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let s = match self.0 {
            ExprKind::Action { .. } => "a subscripted action (`[A]_v` / `<<A>>_v`)",
            ExprKind::Fairness { .. } => "a fairness condition (`WF_` / `SF_`)",
            ExprKind::Lambda { .. } => "a bare `LAMBDA`",
            ExprKind::AssumeProve { .. } => "an `ASSUME` … `PROVE` sequent",
            ExprKind::Qualified { .. } => "an instance-qualified expression",
            ExprKind::UnboundedQuant { .. } => "an unbounded quantifier",
            _ => "this construct",
        };
        f.write_str(s)
    }
}

/// The fold an operator name denotes, if it is one of Apalache's.
///
/// Only the two whose signatures `Apalache.tla` pins down. The community
/// modules' `FoldSet` / `FoldLeft` take their operator differently, and reading
/// one signature as another would fold the wrong argument silently, so they are
/// deliberately not guessed at here.
fn fold_kind(name: &str, argc: usize) -> Option<FoldOver> {
    match (name, argc) {
        ("ApaFoldSet", 3) => Some(FoldOver::Set),
        ("ApaFoldSeqLeft", 3) => Some(FoldOver::SeqLeft),
        _ => None,
    }
}

/// Whether `e` mentions `name` anywhere.
///
/// A definition that refers to itself is recursive, and must not be inlined
/// into itself. Walked with an explicit stack: the expression is user input.
fn mentions_name(e: &Expr, name: &str) -> bool {
    let mut stack = vec![e];
    let mut budget = 1_000_000usize;
    while let Some(t) = stack.pop() {
        match budget.checked_sub(1) {
            Some(b) => budget = b,
            // Past the budget, assume it does: keeping a recursion that is not
            // there costs a declined specification, inlining one that is costs
            // the lowering budget and a far worse diagnostic.
            None => return true,
        }
        match &t.kind {
            ExprKind::Name(q) if q.base().is_some_and(|i| i.name == name) => return true,
            ExprKind::Apply { head, .. } if head.base().is_some_and(|i| i.name == name) => {
                return true;
            }
            _ => {}
        }
        stack.extend(surface_children(t));
    }
    false
}
