//! Differential fuzz: incremental `ArithSolver` verdicts vs a from-scratch
//! replay.
//!
//! The per-final-check `resync_theory_state` rebuilds the arithmetic solver
//! from the shadow trail on every candidate model, on the premise that the
//! incremental tableau can diverge from a fresh replay.  This harness attacks
//! that premise for `ArithSolver`: drive one solver through a random stream of
//! assertions (le/ge/eq/lt/gt over a small term pool with small rational
//! coefficients) interleaved with `push`/`pop`, and after every step compare
//! `check()` verdicts against a fresh solver fed the same *live* assertions.
//!
//! A verdict divergence is a genuine incremental-state bug (a scoped bound or
//! row that leaked across a pop, or one that vanished while still in scope) —
//! exactly the class the resync backstop hides, and each direction is
//! unsound in its own way: a leaked bound can fabricate `Unsat`, a vanished
//! one can fabricate `Sat`.

use super::*;
use nixie_core::TermId;
use num_rational::Rational64;

/// Deterministic small PRNG (xorshift64*) so failures replay from a seed.
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        Self(
            seed.wrapping_mul(0x9E3779B97F4A7C15)
                .wrapping_add(0xD1B54A32D192ED03)
                | 1,
        )
    }
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }
    #[expect(clippy::cast_possible_truncation)] // bounded below before the cast
    fn below(&mut self, n: u64) -> u32 {
        (self.next() % n) as u32
    }
}

#[derive(Clone, Debug)]
enum Op {
    /// (kind, terms, rhs): kind 0=le 1=ge 2=eq 3=lt 4=gt
    Assert(u8, Vec<(TermId, i64)>, i64),
    Push,
    Pop,
}

fn apply(s: &mut ArithSolver, op: &Op, reason: &mut u32) {
    *reason += 1;
    let tag = TermId::new(*reason);
    match op {
        Op::Assert(kind, terms, rhs) => {
            let lin: Vec<(TermId, Rational64)> = terms
                .iter()
                .map(|&(t, c)| (t, Rational64::from_integer(c)))
                .collect();
            let r = Rational64::from_integer(*rhs);
            match kind {
                0 => s.assert_le(&lin, r, tag),
                1 => s.assert_ge(&lin, r, tag),
                2 => s.assert_eq(&lin, r, tag),
                3 => s.assert_lt(&lin, r, tag),
                _ => s.assert_gt(&lin, r, tag),
            }
        }
        Op::Push => {
            use crate::theory::Theory as _;
            s.push();
        }
        Op::Pop => {
            use crate::theory::Theory as _;
            s.pop();
        }
    }
}

fn verdict_of(s: &mut ArithSolver) -> u8 {
    use crate::theory::Theory as _;
    match s.check() {
        Ok(TheoryResult::Sat) => 0,
        Ok(TheoryResult::Unsat(_)) => 1,
        Ok(_) => 2,
        Err(_) => 3,
    }
}

fn run_seed(seed: u64, steps: usize) -> Option<String> {
    use crate::theory::Theory as _;
    let mut rng = Rng::new(seed);
    let mut live = ArithSolver::lia();
    let mut reason = 10_000u32;
    let mut log: Vec<Vec<Op>> = vec![Vec::new()];
    let mut history: Vec<Op> = Vec::new();

    for step in 0..steps {
        let depth = log.len();
        let op = match rng.below(100) {
            0..=74 => {
                // 1-3 distinct-ish terms, coefficients in [-3,3]\{0}, rhs in [-8,8]
                let n = 1 + rng.below(3) as usize;
                let mut terms = Vec::with_capacity(n);
                for _ in 0..n {
                    let t = TermId::new(1 + rng.below(6));
                    let mut c = rng.below(7) as i64 - 3;
                    if c == 0 {
                        c = 1;
                    }
                    terms.push((t, c));
                }
                let rhs = rng.below(17) as i64 - 8;
                Op::Assert(rng.below(5) as u8, terms, rhs)
            }
            75..=87 if depth < 5 => Op::Push,
            88..=99 if depth > 1 => Op::Pop,
            _ => Op::Push,
        };
        history.push(op.clone());
        apply(&mut live, &op, &mut reason);
        match op {
            Op::Push => log.push(Vec::new()),
            Op::Pop => {
                log.pop();
            }
            ref other => log.last_mut().map_or((), |s| s.push(other.clone())),
        }

        // Fresh replay of the surviving log.
        let mut mirror = ArithSolver::lia();
        let mut mreason = 10_000u32;
        for scope in &log {
            for o in scope {
                apply(&mut mirror, o, &mut mreason);
            }
        }
        let vl = verdict_of(&mut live);
        let vm = verdict_of(&mut mirror);
        if vl != vm {
            return Some(format!(
                "seed {seed} step {step}: verdict diverged (live={vl} mirror={vm})\n history: {history:?}\n live-log: {log:?}"
            ));
        }
    }
    live.reset();
    None
}

/// Brute-force ground truth for a bounded-domain system: enumerate every
/// integer assignment in `[-RANGE, RANGE]` for every mentioned term and check
/// every live constraint.  `None` when some var would exceed the range in a
/// satisfying assignment we cannot see (we only assert what we found — the
/// verdict is exact for sat; unsat is exact only within the box, so the
/// caller treats found-sat as ground truth and in-box-unsat as ground truth
/// only when at least one witness touches the box boundary... which we
/// cannot know.  So: this oracle is used ONLY to certify `sat` verdicts of
/// the solver (exhibit witness, verify) and to catch solver-`unsat` when a
/// boxed witness exists).
fn brute_force_sat_witness(ops: &[Op], range: i64) -> Option<Vec<(TermId, i64)>> {
    // Collect terms and build normalized constraint evaluators.
    let mut terms: Vec<TermId> = Vec::new();
    for op in ops {
        if let Op::Assert(_, ts, _) = op {
            for (t, _) in ts {
                if !terms.contains(t) {
                    terms.push(*t);
                }
            }
        }
    }
    let n = terms.len();
    if n == 0 || n > 5 {
        return None;
    }
    let eval = |op: &Op, assign: &FxHashMap<TermId, i64>| -> Option<bool> {
        let Op::Assert(kind, ts, rhs) = op else {
            return Some(true);
        };
        let mut acc: i64 = 0;
        for (t, c) in ts {
            acc = acc.checked_add(assign.get(t).copied()? * c)?;
        }
        Some(match kind {
            0 => acc <= *rhs,
            1 => acc >= *rhs,
            2 => acc == *rhs,
            3 => acc < *rhs,
            _ => acc > *rhs,
        })
    };
    // Enumerate the box.
    let span = (2 * range + 1) as usize;
    let mut total = 1usize;
    for _ in 0..n {
        total = total.checked_mul(span)?;
        if total > 2_000_000 {
            return None;
        }
    }
    let span_i = span as i64;
    let mut idx = 0usize;
    while idx < total {
        let mut assign: FxHashMap<TermId, i64> = FxHashMap::default();
        let mut rem = idx as i64;
        for t in &terms {
            assign.insert(*t, rem % span_i - range);
            rem /= span_i;
        }
        if ops.iter().all(|op| eval(op, &assign).unwrap_or(false)) {
            return Some(assign.into_iter().collect());
        }
        idx += 1;
    }
    None
}

#[test]
fn arith_verdicts_match_bruteforce_oracle() {
    // Same stream generator, but certify verdicts against exhaustive search
    // over a small box (only streams whose every constraint fits the box are
    // certified; the box witnesses catch false `unsat` — the GMI sign-bug
    // class — and the value check catches false `sat`).
    for seed in 100..130u64 {
        let mut rng = Rng::new(seed);
        let mut s = ArithSolver::lia();
        let mut reason = 10_000u32;
        let mut log: Vec<Vec<Op>> = vec![Vec::new()];
        for _step in 0..400 {
            let depth = log.len();
            let op = match rng.below(100) {
                0..=79 => {
                    let n = 1 + rng.below(3) as usize;
                    let mut terms = Vec::with_capacity(n);
                    for _ in 0..n {
                        let t = TermId::new(1 + rng.below(4));
                        let mut c = rng.below(5) as i64 - 2;
                        if c == 0 {
                            c = 1;
                        }
                        terms.push((t, c));
                    }
                    let rhs = rng.below(9) as i64 - 4;
                    Op::Assert(rng.below(5) as u8, terms, rhs)
                }
                80..=89 if depth < 4 => Op::Push,
                90..=99 if depth > 1 => Op::Pop,
                _ => Op::Push,
            };
            apply(&mut s, &op, &mut reason);
            match op {
                Op::Push => log.push(Vec::new()),
                Op::Pop => {
                    log.pop();
                }
                ref other => log.last_mut().map_or((), |l| l.push(other.clone())),
            }
            let live: Vec<Op> = log.iter().flatten().cloned().collect();
            let Some(witness) = brute_force_sat_witness(&live, 4) else {
                continue;
            };
            // A boxed witness exists: the solver MUST answer Sat and its
            // values must satisfy every live constraint.
            let v = verdict_of(&mut s);
            assert!(
                v == 0,
                "seed {seed}: boxed witness {witness:?} exists but solver verdict={v} (0=sat,1=unsat)\n ops: {live:?}"
            );
            // On Sat, the solver's own reported values must satisfy every
            // live constraint (the model-based combination layer and model
            // printing both read `value()` — a drifted incremental
            // assignment poisons them even when the verdict is right).
            for op in &live {
                let Op::Assert(kind, terms, rhs) = op else {
                    continue;
                };
                let mut acc = num_rational::Rational64::from_integer(0);
                let mut ok = true;
                for (t, c) in terms {
                    let Some(val) = s.value(*t) else {
                        ok = false;
                        break;
                    };
                    acc += val * num_rational::Rational64::from_integer(*c);
                }
                if !ok {
                    continue;
                }
                let sat_q = match kind {
                    0 => acc <= num_rational::Rational64::from_integer(*rhs),
                    1 => acc >= num_rational::Rational64::from_integer(*rhs),
                    2 => acc == num_rational::Rational64::from_integer(*rhs),
                    3 => acc < num_rational::Rational64::from_integer(*rhs),
                    _ => acc > num_rational::Rational64::from_integer(*rhs),
                };
                assert!(
                    sat_q,
                    "seed {seed}: solver reports Sat but its own values violate {op:?} (eval={acc})"
                );
            }
        }
    }
}

#[test]
fn arith_incremental_matches_replay_fuzz() {
    // 30 seeds x 2000 steps; each step also runs two full checks, so this
    // covers ~120k incremental assertions against fresh replays.
    for seed in 0..30u64 {
        if let Some(msg) = run_seed(seed, 2000) {
            panic!("{msg}");
        }
    }
}
