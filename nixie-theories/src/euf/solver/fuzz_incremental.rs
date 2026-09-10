//! Differential fuzz: incremental `EufSolver` state vs a from-scratch replay.
//!
//! `TheoryManager::resync_theory_state` exists (in part) because the
//! incremental e-graph "can lose a congruence or disequality" across
//! CDCL push/pop.  This harness attacks that claim directly: drive one
//! solver through a random op stream (intern / intern_app / merge /
//! assert_diseq / push / pop) and, after every step, rebuild a second
//! solver by replaying the *live* op log from scratch (the same
//! discipline `resync_theory_state` uses for the EUF side), then compare
//! the induced equivalence partitions and the conflict verdicts.
//!
//! Any disagreement is a genuine incremental-state divergence of exactly
//! the class the per-final-check resync backstop was installed to hide —
//! and a soundness bug in its own right (a missed congruence is a missed
//! conflict, i.e. a potential false `sat`).

use super::*;
use nixie_core::TermId;

/// One fuzz operation.  Indices into the node-id vector are taken modulo
/// its current length when applied, so the stream never goes out of range.
#[derive(Clone, Debug)]
enum Op {
    InternLeaf(u32),
    InternApp {
        func: u32,
        a: u32,
        b: u32,
        unary: bool,
    },
    Merge(u32, u32),
    Diseq(u32, u32),
    Push,
    Pop,
}

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
    #[expect(clippy::cast_possible_truncation)] // modulo a small bound first
    fn below(&mut self, n: u64) -> u32 {
        (self.next() % n) as u32
    }
}

/// Apply `op` to `s`, appending any new node id to `nodes`.
fn apply(s: &mut EufSolver, nodes: &mut Vec<u32>, op: &Op) {
    let pick = |nodes: &[u32], i: u32| nodes[(i as usize) % nodes.len()];
    match op {
        Op::InternLeaf(i) => {
            nodes.push(s.intern(TermId::new(*i)));
        }
        Op::InternApp { func, a, b, unary } => {
            let args: SmallVec<[u32; 4]> = if *unary {
                vec![pick(nodes, *a)]
            } else {
                vec![pick(nodes, *a), pick(nodes, *b)]
            }
            .into_iter()
            .collect();
            // Distinct term id per application so every replay interns it
            // afresh (the term counter matches the node order exactly).
            let term = TermId::new(1000 + nodes.len() as u32);
            nodes.push(s.intern_app(term, *func, args));
        }
        Op::Merge(i, j) => {
            let (a, b) = (pick(nodes, *i), pick(nodes, *j));
            let _ = s.merge(a, b, TermId::new(0));
        }
        Op::Diseq(i, j) => {
            let (a, b) = (pick(nodes, *i), pick(nodes, *j));
            s.assert_diseq(a, b, TermId::new(0));
        }
        Op::Push => s.push(),
        Op::Pop => s.pop(),
    }
}

/// The partition of live node ids induced by `find`, canonicalized to dense
/// first-appearance ids so solvers with different root choices still compare.
fn partition_of(solver: &mut EufSolver, nodes: &[u32]) -> Vec<u32> {
    let mut canon: FxHashMap<u32, u32> = FxHashMap::default();
    let mut out = Vec::with_capacity(nodes.len());
    for &n in nodes {
        let root = solver.find(n);
        let next = canon.len() as u32;
        let id = *canon.entry(root).or_insert(next);
        out.push(id);
    }
    out
}

/// How many intern ops the surviving log contains (node ids are assigned in
/// intern order, so this is the expected live node count).
fn intern_count(log: &[Vec<Op>]) -> usize {
    log.iter()
        .flatten()
        .filter(|op| matches!(op, Op::InternLeaf(_) | Op::InternApp { .. }))
        .count()
}

fn run_seed(seed: u64, steps: usize) -> Option<String> {
    let mut rng = Rng::new(seed);
    let mut live: EufSolver = EufSolver::new();
    let mut live_nodes: Vec<u32> = Vec::new();
    // Op log per open scope; Pop discards its scope's log (and its nodes).
    let mut log: Vec<Vec<Op>> = vec![Vec::new()];

    for step in 0..steps {
        let depth = log.len();
        // Until at least one node exists, the only applicable op is an intern
        // (every other op indexes into the node vector).
        let op = if live_nodes.is_empty() {
            Op::InternLeaf(1 + rng.below(8))
        } else {
            match rng.below(100) {
                0..=14 => Op::InternLeaf(1 + rng.below(8)),
                15..=29 => Op::InternApp {
                    func: rng.below(3),
                    a: rng.below(64),
                    b: rng.below(64),
                    unary: rng.below(2) == 0,
                },
                30..=69 => Op::Merge(rng.below(64), rng.below(64)),
                70..=84 => Op::Diseq(rng.below(64), rng.below(64)),
                85..=92 if depth < 6 => Op::Push,
                93..=99 if depth > 1 => Op::Pop,
                _ => Op::Merge(rng.below(64), rng.below(64)),
            }
        };
        apply(&mut live, &mut live_nodes, &op);
        match op {
            Op::Push => log.push(Vec::new()),
            Op::Pop => {
                log.pop();
                // Nodes interned in the popped scope are gone; the replay's
                // node vector is authoritative for the expected count.
                let expected = intern_count(&log);
                live_nodes.truncate(expected);
            }
            ref other => log.last_mut().map_or((), |s| s.push(other.clone())),
        }

        // Fresh replay of the surviving log.
        let mut mirror = EufSolver::new();
        let mut mirror_nodes = Vec::new();
        for scope in &log {
            for o in scope {
                apply(&mut mirror, &mut mirror_nodes, o);
            }
        }
        if live_nodes.len() != mirror_nodes.len() {
            return Some(format!(
                "seed {seed} step {step}: node count diverged: live={} mirror={}",
                live_nodes.len(),
                mirror_nodes.len()
            ));
        }
        let pl = partition_of(&mut live, &live_nodes);
        let pm = partition_of(&mut mirror, &mirror_nodes);
        if pl != pm {
            return Some(format!(
                "seed {seed} step {step}: partition diverged\n live={pl:?}\n mirror={pm:?}\n ops: {log:?}"
            ));
        }
        let cl = live.check_conflicts().is_some();
        let cm = mirror.check_conflicts().is_some();
        if cl != cm {
            return Some(format!(
                "seed {seed} step {step}: conflict verdict diverged (live={cl} mirror={cm})\n ops: {log:?}"
            ));
        }
    }
    None
}

#[test]
fn euf_incremental_matches_replay_fuzz() {
    // 40 seeds x 3000 steps ≈ 120k ops per CI run; enough to catch any
    // systematic pop/undo divergence while staying fast.
    for seed in 0..40u64 {
        if let Some(msg) = run_seed(seed, 3000) {
            panic!("{msg}");
        }
    }
}
