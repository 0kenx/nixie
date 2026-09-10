//! Differential fuzz: incremental difference-logic solver verdicts vs a
//! from-scratch replay.
//!
//! Same premise-attack as the EUF and arithmetic harnesses: the per-final-check
//! `resync_theory_state` rebuild also resets the difference-logic solver on the
//! assumption that its incremental state can diverge from a fresh replay.
//! Drive one solver through random `register_var` / `add_leq` / `add_lt` /
//! `push` / `pop` streams and, after every step, compare `check()` against a
//! fresh solver fed the same live constraint log.

use crate::diff_logic::DiffLogicSolver;
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
    /// (strict, x, y, weight, origin): `x - y <= weight` / `x - y < weight`
    Edge(bool, u32, u32, i64, u32),
    Push,
    Pop,
}

fn apply(s: &mut DiffLogicSolver, op: &Op) {
    match op {
        Op::Edge(strict, x, y, w, o) => {
            let (a, b) = (TermId::new(1 + *x % 6), TermId::new(1 + *y % 6));
            let wr = Rational64::from_integer(*w);
            let origin = TermId::new(10_000 + *o);
            if *strict {
                let _ = s.add_lt(a, b, wr, origin);
            } else {
                let _ = s.add_leq(a, b, wr, origin);
            }
        }
        Op::Push => s.push(),
        Op::Pop => s.pop(1),
    }
}

/// Verdict of `check()`: 0 = consistent (Ok / propagation), 1 = conflict.
fn verdict_of(s: &mut DiffLogicSolver) -> u8 {
    use crate::diff_logic::DiffLogicResult;
    match s.check() {
        DiffLogicResult::Conflict(_) => 1,
        _ => 0,
    }
}

fn run_seed(seed: u64, steps: usize) -> Option<String> {
    let mut rng = Rng::new(seed);
    let mut live = DiffLogicSolver::new(true);
    let mut log: Vec<Vec<Op>> = vec![Vec::new()];

    for step in 0..steps {
        let depth = log.len();
        let op = match rng.below(100) {
            0..=79 => Op::Edge(
                rng.below(2) == 0,
                rng.below(6),
                rng.below(6),
                rng.below(17) as i64 - 8,
                step as u32,
            ),
            80..=89 if depth < 5 => Op::Push,
            90..=99 if depth > 1 => Op::Pop,
            _ => Op::Push,
        };
        apply(&mut live, &op);
        match op {
            Op::Push => log.push(Vec::new()),
            Op::Pop => {
                log.pop();
            }
            ref other => log.last_mut().map_or((), |l| l.push(other.clone())),
        }

        // Fresh replay of the surviving log.
        let mut mirror = DiffLogicSolver::new(true);
        for scope in &log {
            for o in scope {
                apply(&mut mirror, o);
            }
        }
        let vl = verdict_of(&mut live);
        let vm = verdict_of(&mut mirror);
        if vl != vm {
            return Some(format!(
                "seed {seed} step {step}: verdict diverged (live={vl} mirror={vm})\n ops: {log:?}"
            ));
        }
    }
    None
}

#[test]
fn dl_incremental_matches_replay_fuzz() {
    // 30 seeds x 2000 steps: ~60k constraints checked against fresh replays.
    for seed in 0..30u64 {
        if let Some(msg) = run_seed(seed, 2000) {
            panic!("{msg}");
        }
    }
}
