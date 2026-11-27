//! Liveness-to-safety for temporal properties: the **lasso** encoding
//! (issue #29).
//!
//! A temporal property describes behaviours, and a bounded unrolling only
//! ever sees a finite prefix. Biere–Artho–Schuppan's construction makes a
//! finite prefix stand for an infinite behaviour by requiring it to be a
//! **lasso**: a prefix followed by a loop that closes back onto an earlier
//! state. Apalache realises it as a specification rewrite (`LoopEncoder`,
//! `TableauEncoder`) and checks an ordinary invariant on the rewritten
//! specification; this module does the same, on kernel terms:
//!
//! * `__InLoop` — a Boolean state variable, false initially, monotone
//!   (`__InLoop => __InLoop'`), true from the first state *after* the
//!   loop's start;
//! * `__saved_<v>` — one frozen copy per state variable (and per tableau
//!   node variable), holding the value at loop entry
//!   (`__saved_v' = IF __InLoop' = __InLoop THEN __saved_v ELSE v`);
//! * the **tableau** — per temporal node `N`, `__temporal_N` (its truth at
//!   the current unrolled state) and `__temporal_N_unroll[_prev]` (its
//!   value assuming the path goes around the loop), with the recurrence
//!   `N <=> outer(arg, N')` and `unroll <=> outer(prev, inner(InLoop',
//!   arg))`, and at the close `unroll => N` for `[]`, `N => unroll` for
//!   `<>`, with `prev = unroll`;
//! * the checked invariant: `__LoopOK => __<prop>_init`, where
//!   `__LoopOK == __InLoop /\\ \\A v : v = __saved_v` and `__<prop>_init`
//!   is the property's root node captured in `Init`.
//!
//! "No counterexample within k" therefore means *no lasso of k steps or
//! fewer carries a violation* — never "the property holds".
//!
//! Soundness rests on the invariant being an ordinary state predicate of an
//! ordinary (rewritten) specification: the solver finds a lasso exactly when
//! the finite recurrence is satisfiable, and the trace is replayed by the
//! evaluator step by step like any other, with the loop close (`__LoopOK`)
//! re-evaluated independently on the last state.

use std::rc::Rc;

use nixie_tla::kera::{Kera, KeraRef, Name, Temporal};

/// The lasso-encoded specification: drop-in replacements for `Init`/`Next`
/// plus the state invariant that a violating lasso falsifies.
#[derive(Debug, Clone)]
pub struct Lasso {
    /// The rewritten `Init`: the original, `__InLoop = FALSE`, every
    /// `__saved_v = v`, and the tableau's initial values.
    pub init: KeraRef,
    /// The rewritten `Next`: the original, the `__InLoop` update, the
    /// `__saved_` updates, and the tableau's step equations.
    pub next: KeraRef,
    /// `__LoopOK => __<prop>_init`, as a state predicate.
    pub invariant: KeraRef,
    /// The names of the auxiliary state variables (every one Boolean or a
    /// copy of a spec variable's sort), for the caller's declarations and
    /// trace decoding.
    pub aux_variables: Vec<String>,
    /// The state variables the loop closes over, by name.
    pub loop_variables: Vec<String>,
    /// `__LoopOK`, for the trace decoder (the `loop` field).
    pub loop_ok: KeraRef,
    /// The root node variable, for the trace decoder.
    pub root: Name,
}

/// The lasso prefix. Chosen to collide with nothing a TLA+ user can write
/// (`__` is not a legal identifier start in TLA+... it *is* legal, but the
/// Apalache-reserved `__` prefix is the ecosystem's convention for "mine,
/// not yours"; the names follow Apalache's so a user reading a trace
/// recognises them).
pub const IN_LOOP: &str = "__InLoop";
/// The loop-close predicate's conventional name (Apalache's); here it is a
/// term, not a definition, but traces and messages name it the same.
pub const LOOP_OK: &str = "__LoopOK";
const SAVED: &str = "__saved_";
const TEMPORAL: &str = "__temporal_";
const INIT_SUFFIX: &str = "_init";

fn v(name: &str) -> KeraRef {
    Kera::Var(Name(name.to_string())).rc()
}

fn and(xs: Vec<KeraRef>) -> KeraRef {
    Kera::And(xs).rc()
}

fn or(xs: Vec<KeraRef>) -> KeraRef {
    Kera::Or(xs).rc()
}

fn eq(a: KeraRef, b: KeraRef) -> KeraRef {
    Kera::Eq(a, b).rc()
}

fn not(a: KeraRef) -> KeraRef {
    Kera::Not(a).rc()
}

fn prime(a: KeraRef) -> KeraRef {
    Kera::Prime(a).rc()
}

fn ite(c: KeraRef, t: KeraRef, e: KeraRef) -> KeraRef {
    Kera::Ite(c, t, e).rc()
}

fn implies(a: KeraRef, b: KeraRef) -> KeraRef {
    or(vec![not(a), b])
}

fn iff(a: KeraRef, b: KeraRef) -> KeraRef {
    and(vec![implies(Rc::clone(&a), Rc::clone(&b)), implies(b, a)])
}

/// Build the lasso encoding of `init`/`next` for the property `prop` over
/// the state variables `vars`.
///
/// `vars` must list **every** state variable of the specification: a
/// variable the loop does not close over would let the lasso "return" to
/// a state that differs in it — a behaviour the specification does not
/// have, and a counterexample it cannot produce.
#[must_use]
pub fn encode(init: KeraRef, next: KeraRef, prop: &Temporal, vars: &[String]) -> Lasso {
    let in_loop = v(IN_LOOP);
    let in_loop_p = prime(Rc::clone(&in_loop));

    // ---- the tableau ----
    let mut t = Tableau::default();
    let root = t.build_root(prop);

    // Every tableau node variable is a state variable the loop closes over,
    // so each gets a frozen copy too (Apalache: `createAllVarCopiesInLoop`
    // over the extended variable list).
    let mut aux: Vec<String> = vec![IN_LOOP.to_string()];
    let mut saved: Vec<(KeraRef, KeraRef)> = vars
        .iter()
        .map(|name| {
            aux.push(format!("{SAVED}{name}"));
            (v(name), v(&format!("{SAVED}{name}")))
        })
        .collect();
    // Only the **node** variables get frozen copies (Apalache:
    // `createGenericNodeVarExs(nodeVarEx, nodeLoopVarEx)` — the `unroll`
    // and `_prev` auxiliaries get none). Their values at the close are
    // pinned by the tableau's own `prev = unroll` and `unroll => node`
    // instead. Freezing them too over-constrains: `prev@close` would be
    // `prev` at loop entry while the recurrence's `prev' = unroll` makes it
    // `unroll` one step back, and the two disagree on every lasso whose
    // loop is longer than one state — the lasso then never closes and
    // every box property "holds".
    for n in &t.decls {
        aux.push(n.clone());
    }
    for n in &t.node_vars {
        aux.push(format!("{SAVED}{n}"));
        saved.push((v(n), v(&format!("{SAVED}{n}"))));
    }

    // ---- Init ----
    let mut init_parts: Vec<KeraRef> = vec![init, eq(Rc::clone(&in_loop), Kera::Bool(false).rc())];
    init_parts.extend(saved.iter().map(|(x, s)| eq(Rc::clone(s), Rc::clone(x))));
    init_parts.extend(t.init.iter().cloned());

    // ---- Next ----
    let mut next_parts: Vec<KeraRef> = vec![
        next,
        // `__InLoop' \in BOOLEAN /\ __InLoop => __InLoop'`
        or(vec![
            eq(Rc::clone(&in_loop_p), Kera::Bool(true).rc()),
            eq(Rc::clone(&in_loop_p), Kera::Bool(false).rc()),
        ]),
        implies(Rc::clone(&in_loop), Rc::clone(&in_loop_p)),
    ];
    for (x, s) in &saved {
        // `__saved_x' = IF __InLoop' = __InLoop THEN __saved_x ELSE x`
        next_parts.push(eq(
            prime(Rc::clone(s)),
            ite(
                eq(Rc::clone(&in_loop_p), Rc::clone(&in_loop)),
                Rc::clone(s),
                Rc::clone(x),
            ),
        ));
    }
    next_parts.extend(t.next.iter().cloned());

    // ---- LoopOK ----
    let mut ok_parts: Vec<KeraRef> = vec![Rc::clone(&in_loop)];
    ok_parts.extend(saved.iter().map(|(x, s)| eq(Rc::clone(x), Rc::clone(s))));
    ok_parts.extend(t.close.iter().cloned());
    let loop_ok = and(ok_parts);

    // ---- the invariant ----
    let invariant = implies(Rc::clone(&loop_ok), Rc::clone(&root.init));

    Lasso {
        init: and(init_parts),
        next: and(next_parts),
        invariant,
        aux_variables: aux,
        loop_variables: vars.to_vec(),
        loop_ok,
        root: root.init_name,
    }
}

/// One temporal node's tableau pieces: the equations the node variables
/// contribute to `Init`, to `Next`, and to the loop close.
#[derive(Default)]
struct Tableau {
    /// Every auxiliary variable declared, in post-order (deterministic names).
    decls: Vec<String>,
    /// The subset of `decls` that are **node** variables — the ones that
    /// get a frozen copy for the loop close (the `unroll`/`_prev`
    /// auxiliaries do not; see `encode`).
    node_vars: Vec<String>,
    init: Vec<KeraRef>,
    next: Vec<KeraRef>,
    close: Vec<KeraRef>,
}

/// What [`Tableau::build_root`] returns for the property: the captured
/// `__<i>_init` (its variable name and its reading term).
struct Root {
    init: KeraRef,
    init_name: Name,
}

impl Tableau {
    fn fresh(&mut self, suffix: &str) -> String {
        let n = format!("{TEMPORAL}{}{suffix}", self.decls.len());
        self.decls.push(n.clone());
        n
    }

    /// Declare a **node variable**: a Boolean state variable whose value is
    /// defined at `Init` and at every step by `define`, read back as the
    /// variable (never as the defining term — the variable *is* the node's
    /// truth, and the loop close pins it across the seam).
    fn node_var(&mut self, define: impl Fn() -> KeraRef) -> KeraRef {
        let name = self.fresh("");
        // No frozen copy for a propositional node: its value is a function
        // of its children's **current** values, which the close pins
        // directly (each box/diamond node has its copy), so pinning it too
        // adds an `ite` equation per step and says nothing new.
        let x = v(&name);
        let d = define();
        // `Init`: node = op(args). `Next`: node' = op(args) — Apalache's
        // `createPropositionalOperNodeExs`, whose arguments are the
        // children's **current** values, which the box/diamond equations
        // then read at the next state through their own `node'`.
        self.init.push(eq(Rc::clone(&x), Rc::clone(&d)));
        self.next.push(eq(prime(Rc::clone(&x)), d));
        x
    }

    /// The tableau of one temporal-level subformula: its node variable.
    /// State predicates are read directly; every other node gets a variable
    /// (Apalache's `createPropositionalOperNodeExs`).
    fn build(&mut self, t: &Temporal) -> KeraRef {
        match t {
            Temporal::Node(k) => Rc::clone(k),
            Temporal::Always(inner) | Temporal::Eventually(inner) => {
                let is_box = matches!(t, Temporal::Always(_));
                let arg = self.build(inner);
                let in_loop_p = prime(v(IN_LOOP));
                // The node variable is defined against its own next value
                // and the unroll auxiliary against the lookback, so the
                // three names are reserved first and the equations written
                // after, in the node variable's own slots.
                let node_name = self.fresh("");
                self.node_vars.push(node_name.clone());
                let unroll_name = self.fresh("_unroll");
                let prev_name = self.fresh("_unroll_prev");
                let node = v(&node_name);
                let unroll = v(&unroll_name);
                let prev = v(&prev_name);
                let initial = Kera::Bool(is_box).rc();
                // Only the **lookback** is fixed at `Init`. Apalache's
                // `TableauEncoder` also fixes `unroll` there (`auxVarInitEx`,
                // TRUE for `[]`, FALSE for `<>`), and its step-0 equation
                // then contradicts that for every lasso whose loop starts in
                // state 0: `unroll@0 = prev@0 /\ (~InLoop@1 \/ arg@0)` is
                // FALSE there when a box argument fails in state 0 (or TRUE
                // for a diamond argument that holds), while `Init` says the
                // opposite. Such a lasso is then unrepresentable, and its
                // violation is found only one step later, rotated to start
                // in state 1 – or, within a bound that reaches the shorter
                // form only, not at all: `<>(x = 1)` on the 2-cycle
                // `(0,0) -> (1,0) -> (0,0)` was "not violated by any lasso
                // of 2 steps or fewer". Leaving `unroll@0` to its equation
                // is exact in every case – `prev@0` is the neutral element
                // the product starts from – and adds lassoes, never removes
                // one. (Found while testing fairness, issue #47.)
                self.init.push(eq(Rc::clone(&prev), initial));
                // node <=> outer(arg, node') — a `Next` equation only: it
                // reads the node's next value. (`Init` sets just the
                // unroll lookback above; Apalache's `nextExs` carry this
                // one and its `initExs` do not.)
                self.next.push(eq(
                    Rc::clone(&node),
                    if is_box {
                        and(vec![Rc::clone(&arg), prime(Rc::clone(&node))])
                    } else {
                        or(vec![Rc::clone(&arg), prime(Rc::clone(&node))])
                    },
                ));
                // unroll <=> outer(prev, inner(InLoop', arg)) — on the
                // **current** state's variables, reading only `InLoop'`:
                // `unroll@k` is `[]P`'s value at `k` assuming the path
                // goes around, accumulated from the lookback `prev@k` (which
                // is `unroll@k-1`, by `prev' = unroll`) and `P@k`, unless
                // the step out of `k` enters the loop (the prime). Priming
                // `unroll` here instead would shift the accumulation one
                // state and leave the close's `unroll => node` vacuous on
                // every box — the first version of this module did, and
                // `[](x = 9)` on a two-cycle "held".
                let unroll_def = if is_box {
                    and(vec![
                        Rc::clone(&prev),
                        or(vec![not(Rc::clone(&in_loop_p)), Rc::clone(&arg)]),
                    ])
                } else {
                    or(vec![
                        Rc::clone(&prev),
                        and(vec![Rc::clone(&in_loop_p), Rc::clone(&arg)]),
                    ])
                };
                self.next.push(eq(Rc::clone(&unroll), unroll_def));
                // prev' = unroll
                self.next
                    .push(eq(prime(Rc::clone(&prev)), Rc::clone(&unroll)));
                // close: unroll => node (box) / node => unroll (diamond);
                // prev = unroll
                self.close.push(if is_box {
                    implies(Rc::clone(&unroll), Rc::clone(&node))
                } else {
                    implies(Rc::clone(&node), Rc::clone(&unroll))
                });
                self.close.push(eq(Rc::clone(&prev), Rc::clone(&unroll)));
                node
            }
            Temporal::Not(inner) => {
                let a = self.build(inner);
                self.node_var(|| not(Rc::clone(&a)))
            }
            Temporal::And(a, b) => {
                let (x, y) = (self.build(a), self.build(b));
                self.node_var(|| and(vec![Rc::clone(&x), Rc::clone(&y)]))
            }
            Temporal::Or(a, b) => {
                let (x, y) = (self.build(a), self.build(b));
                self.node_var(|| or(vec![Rc::clone(&x), Rc::clone(&y)]))
            }
            Temporal::Implies(a, b) => {
                let (x, y) = (self.build(a), self.build(b));
                self.node_var(|| implies(Rc::clone(&x), Rc::clone(&y)))
            }
            Temporal::Equiv(a, b) => {
                let (x, y) = (self.build(a), self.build(b));
                self.node_var(|| iff(Rc::clone(&x), Rc::clone(&y)))
            }
            Temporal::Ite(c, t, e) => {
                let (c, x, y) = (self.build(c), self.build(t), self.build(e));
                self.node_var(|| ite(Rc::clone(&c), Rc::clone(&x), Rc::clone(&y)))
            }
        }
    }

    /// Build the property's tableau and capture the root's value at `Init`
    /// in `__<i>_init` (Apalache's `__<formula>_init`, `UNCHANGED` after).
    fn build_root(&mut self, prop: &Temporal) -> Root {
        let node = self.build(prop);
        let init_name = self.fresh(INIT_SUFFIX);
        self.node_vars.push(init_name.clone());
        let init = v(&init_name);
        self.init.push(eq(Rc::clone(&init), Rc::clone(&node)));
        self.next.push(unchanged(Rc::clone(&init)));
        Root {
            init,
            init_name: Name(init_name),
        }
    }
}

/// `UNCHANGED x` as a kernel equality.
fn unchanged(x: KeraRef) -> KeraRef {
    eq(prime(x.clone()), x)
}
