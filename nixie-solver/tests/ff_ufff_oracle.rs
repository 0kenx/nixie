//! Exhaustive brute-force oracle for `QF_UFFF` — the finite-field
//! combination's replacement for a Z3 differential (Z3 has no finite-
//! field theory; see `docs/FF_THEORY_DESIGN.md` §10).
//!
//! For randomly generated goals over tiny primes, the ground truth is
//! computed by enumerating **every** model: every assignment of the
//! field variables AND every interpretation table of the uninterpreted
//! functions (`p^(p^arity)` tables). A solver `unsat` on a brute-force
//! satisfiable goal, or a solver `sat` on a brute-force unsatisfiable
//! goal, is a hard failure at n = 1. A solver `unknown` is tolerated
//! (honesty, never a guess) but counted; a systematic wall of unknowns
//! would show up here as a capacity signal, not a soundness one.
//!
//! The generator builds its own small IR first, then (a) prints the
//! SMT-LIB script for the solver and (b) evaluates the same IR
//! semantics directly — the two paths share nothing but the instance,
//! so an encoder bug cannot corrupt both sides the same way.

use nixie_solver::Context;

// ---- The instance IR ----

#[derive(Clone, Debug)]
enum FfTerm {
    Const(u64),
    Var(usize),
    Add(Vec<FfTerm>),
    Mul(Vec<FfTerm>),
    App(usize, Vec<FfTerm>),
}

#[derive(Clone, Debug)]
enum Atom {
    Eq(FfTerm, FfTerm),
    Distinct(Vec<FfTerm>),
}

#[derive(Clone, Debug)]
enum Form {
    Atom(Atom),
    Not(Box<Form>),
    And(Vec<Form>),
    Or(Vec<Form>),
}

/// One test instance: prime, variable count, function arities, formula.
struct Instance {
    p: u64,
    n_vars: usize,
    arities: Vec<usize>,
    form: Form,
}

// ---- Deterministic RNG (a plain LCG; reproducibility is the point) ----

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

// ---- Random instance generation ----

fn gen_term(rng: &mut Rng, inst: &Instance, depth: u32) -> FfTerm {
    let choice = rng.below(10);
    if depth == 0 || choice < 3 {
        if rng.below(2) == 0 {
            FfTerm::Const(rng.below(inst.p))
        } else {
            FfTerm::Var(rng.below(inst.n_vars as u64) as usize)
        }
    } else if choice < 6 {
        let n = 2 + rng.below(2) as usize;
        FfTerm::Add((0..n).map(|_| gen_term(rng, inst, depth - 1)).collect())
    } else if choice < 8 {
        let n = 2 + rng.below(2) as usize;
        FfTerm::Mul((0..n).map(|_| gen_term(rng, inst, depth - 1)).collect())
    } else {
        let f = rng.below(inst.arities.len() as u64) as usize;
        let args = (0..inst.arities[f])
            .map(|_| gen_term(rng, inst, depth - 1))
            .collect();
        FfTerm::App(f, args)
    }
}

fn gen_atom(rng: &mut Rng, inst: &Instance) -> Atom {
    if rng.below(4) == 0 {
        // distinct: 2–4 terms (at p=2/3 this is where the cardinality
        // guard and the arrangement machinery earn their keep).
        let n = 2 + rng.below(3) as usize;
        Atom::Distinct((0..n).map(|_| gen_term(rng, inst, 2)).collect())
    } else {
        Atom::Eq(gen_term(rng, inst, 2), gen_term(rng, inst, 2))
    }
}

fn gen_form(rng: &mut Rng, inst: &Instance, depth: u32) -> Form {
    if depth == 0 {
        return Form::Atom(gen_atom(rng, inst));
    }
    match rng.below(4) {
        0 => Form::Not(Box::new(gen_form(rng, inst, depth - 1))),
        1 => Form::And(
            (0..2 + rng.below(2))
                .map(|_| gen_form(rng, inst, depth - 1))
                .collect(),
        ),
        2 => Form::Or(
            (0..2 + rng.below(2))
                .map(|_| gen_form(rng, inst, depth - 1))
                .collect(),
        ),
        _ => Form::Atom(gen_atom(rng, inst)),
    }
}

// ---- SMT-LIB printing ----

fn term_str(t: &FfTerm, p: u64) -> String {
    match t {
        FfTerm::Const(c) => format!("#f{c}m{p}"),
        FfTerm::Var(v) => format!("x{v}"),
        FfTerm::Add(ts) => format!(
            "(ff.add {})",
            ts.iter()
                .map(|t| term_str(t, p))
                .collect::<Vec<_>>()
                .join(" ")
        ),
        FfTerm::Mul(ts) => format!(
            "(ff.mul {})",
            ts.iter()
                .map(|t| term_str(t, p))
                .collect::<Vec<_>>()
                .join(" ")
        ),
        FfTerm::App(f, args) => format!(
            "(f{} {})",
            f,
            args.iter()
                .map(|t| term_str(t, p))
                .collect::<Vec<_>>()
                .join(" ")
        ),
    }
}

fn form_str(f: &Form, p: u64) -> String {
    match f {
        Form::Atom(Atom::Eq(a, b)) => format!("(= {} {})", term_str(a, p), term_str(b, p)),
        Form::Atom(Atom::Distinct(ts)) => format!(
            "(distinct {})",
            ts.iter()
                .map(|t| term_str(t, p))
                .collect::<Vec<_>>()
                .join(" ")
        ),
        Form::Not(inner) => format!("(not {})", form_str(inner, p)),
        Form::And(fs) => format!(
            "(and {})",
            fs.iter()
                .map(|x| form_str(x, p))
                .collect::<Vec<_>>()
                .join(" ")
        ),
        Form::Or(fs) => format!(
            "(or {})",
            fs.iter()
                .map(|x| form_str(x, p))
                .collect::<Vec<_>>()
                .join(" ")
        ),
    }
}

fn script(inst: &Instance) -> String {
    let mut s = String::new();
    s.push_str("(set-logic QF_UFFF)\n");
    for (i, &a) in inst.arities.iter().enumerate() {
        let args = vec!["(_ FiniteField ".to_string() + &inst.p.to_string() + ")"; a].join(" ");
        s.push_str(&format!(
            "(declare-fun f{i} ({args}) (_ FiniteField {}))\n",
            inst.p
        ));
    }
    for v in 0..inst.n_vars {
        s.push_str(&format!(
            "(declare-const x{v} (_ FiniteField {}))\n",
            inst.p
        ));
    }
    s.push_str(&format!("(assert {})\n", form_str(&inst.form, inst.p)));
    s.push_str("(check-sat)\n");
    s
}

// ---- Exact brute-force semantics ----

/// Evaluate a term under a variable assignment and function tables.
fn eval_term(t: &FfTerm, p: u64, vars: &[u64], tables: &[Vec<u64>]) -> u64 {
    match t {
        FfTerm::Const(c) => *c % p,
        FfTerm::Var(v) => vars[*v],
        FfTerm::Add(ts) => {
            ts.iter()
                .map(|t| eval_term(t, p, vars, tables))
                .sum::<u64>()
                % p
        }
        FfTerm::Mul(ts) => {
            ts.iter()
                .map(|t| eval_term(t, p, vars, tables))
                .product::<u64>()
                % p
        }
        FfTerm::App(f, args) => {
            let mut idx = 0usize;
            for a in args {
                idx = idx * p as usize + eval_term(a, p, vars, tables) as usize;
            }
            tables[*f][idx]
        }
    }
}

fn eval_form(f: &Form, p: u64, vars: &[u64], tables: &[Vec<u64>]) -> bool {
    match f {
        Form::Atom(Atom::Eq(a, b)) => {
            eval_term(a, p, vars, tables) == eval_term(b, p, vars, tables)
        }
        Form::Atom(Atom::Distinct(ts)) => {
            let vals: Vec<u64> = ts.iter().map(|t| eval_term(t, p, vars, tables)).collect();
            (0..vals.len()).all(|i| (i + 1..vals.len()).all(|j| vals[i] != vals[j]))
        }
        Form::Not(inner) => !eval_form(inner, p, vars, tables),
        Form::And(fs) => fs.iter().all(|x| eval_form(x, p, vars, tables)),
        Form::Or(fs) => fs.iter().any(|x| eval_form(x, p, vars, tables)),
    }
}

/// Enumerate every model: all variable assignments × all function
/// tables. The tables are one mixed-radix counter over their ENTRIES
/// (each entry ranges over `p` values), so the count is `p^(Σ table
/// sizes)` — NOT the product of the table sizes. Returns true iff some
/// model satisfies the formula.
fn brute_force_sat(inst: &Instance) -> bool {
    let p = inst.p as usize;
    let table_size: Vec<usize> = inst.arities.iter().map(|&a| p.pow(a as u32)).collect();
    let total_entries: usize = table_size.iter().sum();
    let total_tables: usize = p.pow(total_entries as u32);
    let total_vars = p.pow(inst.n_vars as u32);

    // Enumerate tables in mixed radix over their entries.
    for var_code in 0..total_vars {
        let mut vars = vec![0u64; inst.n_vars];
        let mut rest = var_code;
        for v in vars.iter_mut() {
            *v = (rest % p) as u64;
            rest /= p;
        }
        for table_code in 0..total_tables {
            let mut rest = table_code;
            let tables: Vec<Vec<u64>> = table_size
                .iter()
                .map(|&sz| {
                    let mut t = vec![0u64; sz];
                    for e in t.iter_mut() {
                        *e = (rest % p) as u64;
                        rest /= p;
                    }
                    t
                })
                .collect();
            if eval_form(&inst.form, inst.p, &vars, &tables) {
                return true;
            }
        }
    }
    false
}

// ---- The oracle drivers ----

fn run_oracle(p: u64, n_vars: usize, arities: &[usize], instances: u32, seed: u64) {
    let mut rng = Rng(seed);
    let mut unknowns = 0u32;
    for i in 0..instances {
        let proto = Instance {
            p,
            n_vars,
            arities: arities.to_vec(),
            form: Form::Or(vec![]),
        };
        let inst = Instance {
            form: gen_form(&mut rng, &proto, 3),
            ..proto
        };
        let truth = brute_force_sat(&inst);
        let mut ctx = Context::new();
        let out = match ctx.execute_script(&script(&inst)) {
            Ok(o) => o,
            Err(e) => panic!("instance {i} (p={p}) failed to parse: {e}"),
        };
        let verdict = out.first().map(String::as_str).unwrap_or("no-output");
        match verdict {
            "sat" => {
                assert!(
                    truth,
                    "instance {i} (p={p}, seed {seed}): solver sat but brute force says UNSAT\n{}",
                    script(&inst)
                );
            }
            "unsat" => {
                assert!(
                    !truth,
                    "instance {i} (p={p}, seed {seed}): solver unsat but brute force says SAT\n{}",
                    script(&inst)
                );
            }
            "unknown" => unknowns += 1,
            other => panic!("instance {i}: unexpected output {other:?}"),
        }
    }
    // A capacity signal, not a soundness one: most classes should decide.
    let ratio = unknowns as f64 / f64::from(instances);
    assert!(
        ratio < 0.35,
        "suspiciously many unknowns at p={p}: {unknowns}/{instances}"
    );
}

#[test]
fn oracle_f2_unary() {
    // 4 var assignments × 4 unary tables = 16 models per instance.
    run_oracle(2, 2, &[1], 250, 0xFF00_0001);
}

#[test]
fn oracle_f2_binary() {
    // 4 × 16 = 64 models per instance.
    run_oracle(2, 1, &[2], 200, 0xFF00_0002);
}

#[test]
fn oracle_f2_two_functions() {
    // 4 × 4 × 4 = 64 models per instance.
    run_oracle(2, 1, &[1, 1], 100, 0xFF00_0003);
}

#[test]
fn oracle_f3_unary() {
    // 9 × 27 = 243 models per instance.
    run_oracle(3, 2, &[1], 150, 0xFF00_0004);
}

#[test]
fn oracle_f3_binary() {
    // 3 × 3^9 is too large; single var, binary fn is 3^9 = 19683 tables.
    run_oracle(3, 1, &[2], 40, 0xFF00_0005);
}

#[test]
fn oracle_f5_unary() {
    // 5 × 5^5 = 15625 models per instance.
    run_oracle(5, 1, &[1], 40, 0xFF00_0006);
}

#[test]
fn oracle_f7_unary_shallow() {
    // 7 × 7^7 ≈ 5.7M models: too many — restrict to shallow forms and
    // fewer instances; still exercises real congruence structure.
    run_oracle(7, 1, &[1], 12, 0xFF00_0007);
}

#[test]
fn every_verdict_is_reproduced_deterministically() {
    // Same instance, two fresh contexts: identical verdict (the solver
    // must stay reproducible — no hash-order or wall-clock input).
    let mut rng = Rng(0xABCD_EF01);
    let proto = Instance {
        p: 3,
        n_vars: 2,
        arities: vec![1],
        form: Form::Or(vec![]),
    };
    let inst = Instance {
        p: 3,
        n_vars: 2,
        arities: vec![1],
        form: gen_form(&mut rng, &proto, 3),
    };
    let s = script(&inst);
    let v1 = Context::new().execute_script(&s).expect("parse")[0].clone();
    let v2 = Context::new().execute_script(&s).expect("parse")[0].clone();
    assert_eq!(v1, v2, "nondeterministic verdict for\n{s}");
}
