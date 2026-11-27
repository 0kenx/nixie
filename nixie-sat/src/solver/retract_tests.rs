//! Equivalence tests for the batched clause retraction
//! ([`Solver::retract_clauses`], behind [`Solver::pop`] and
//! [`Solver::forget_learned_since`]).
//!
//! The per-clause removal it replaced is the oracle.  Two solvers are built
//! to the same state; on the first, every binary clause of the retracted
//! batch has its implication-graph edges purged ONE CLAUSE AT A TIME by the
//! unbounded [`Solver::purge_binary_edges`] before the retraction runs – so
//! the batched pass meets lists that hold nothing left to drop and can only
//! agree with the oracle by doing nothing; on the second, the retraction
//! runs alone.  The two must then agree on every implication list, edge for
//! edge and in order, on the learned-clause registry, on the clause counts,
//! on the DRAT proof, and on the whole search that follows.

use super::*;

/// xorshift64* – a fixed stream, so a failure replays.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    fn lit(&mut self, vars: &[Var]) -> Lit {
        let v = vars[self.below(vars.len())];
        if self.next() & 1 == 0 {
            Lit::pos(v)
        } else {
            Lit::neg(v)
        }
    }
}

/// Add a binary clause and return its id (ids are allocation identities,
/// so the newest clause has the highest one).
fn add_binary(s: &mut Solver, a: Lit, b: Lit) -> ClauseId {
    let before = s.clauses.num_slots();
    s.add_clause([a, b]);
    assert_eq!(
        s.clauses.num_slots(),
        before + 1,
        "a binary clause is stored as is"
    );
    let id = ClauseId::new(before as u32);
    let mut stored = s
        .clauses
        .get(id)
        .map(|c| c.lits.to_vec())
        .unwrap_or_default();
    stored.sort_by_key(|l| l.code());
    let mut wanted = vec![a, b];
    wanted.sort_by_key(|l| l.code());
    assert_eq!(stored, wanted, "a binary clause is stored as is");
    id
}

/// Every implication list of the graph, in literal-code order.
fn graph_snapshot(s: &Solver) -> Vec<Vec<(Lit, ClauseId)>> {
    (0..2 * s.num_vars as u32)
        .map(|code| {
            s.binary_graph
                .get(Lit::from_code(code))
                .iter()
                .copied()
                .collect()
        })
        .collect()
}

/// Everything a retraction touches, for the comparison.
#[derive(Debug, PartialEq, Eq)]
struct State {
    graph: Vec<Vec<(Lit, ClauseId)>>,
    learned: Vec<ClauseId>,
    clauses: usize,
    learned_count: usize,
    /// Which ids still name a live clause.
    live: Vec<bool>,
}

fn state_snapshot(s: &Solver) -> State {
    State {
        graph: graph_snapshot(s),
        learned: s.learned_clause_ids.clone(),
        clauses: s.num_clauses(),
        learned_count: s.num_learned_clauses(),
        live: (0..s.clauses.num_slots())
            .map(|i| {
                s.clauses
                    .get(ClauseId::new(i as u32))
                    .is_some_and(|c| !c.deleted)
            })
            .collect(),
    }
}

/// The shared build-up: a base formula whose implication lists come in
/// every shape the retraction distinguishes, then a scope.
///
/// * six long lists (40 base edges under one trigger) – after the rebuild
///   they sit in the graph's PRIMARY spans, and the scope puts 30 clauses on
///   each: the batched pass, over a span and an overflow list at once;
/// * twelve medium lists (12 edges) – long too, and the scope puts ONE
///   clause on each: the "stands alone" case of the batched pass;
/// * eight short lists (5 edges) that the scope SHARES between three of its
///   clauses: the per-edge path with several batch edges;
/// * random binaries and longer clauses around them.
struct Layout {
    long: Vec<Lit>,
    medium: Vec<Lit>,
    short: Vec<Lit>,
    fresh: Vec<Var>,
}

fn build_base(s: &mut Solver, rng: &mut Rng) -> Layout {
    let vars: Vec<Var> = (0..900).map(|_| s.new_var()).collect();
    // A star: `leaves` binary clauses (center v leaf) under one trigger.
    let mut star = |s: &mut Solver, leaves: usize| -> Lit {
        let center = rng.lit(&vars[..200]);
        for _ in 0..leaves {
            let leaf = Lit::pos(s.new_var());
            add_binary(s, center, leaf);
        }
        center.negate()
    };
    let long: Vec<Lit> = (0..6).map(|_| star(s, 40)).collect();
    let medium: Vec<Lit> = (0..12).map(|_| star(s, 12)).collect();
    let short: Vec<Lit> = (0..8).map(|_| star(s, 5)).collect();
    for _ in 0..300 {
        let (a, b) = (rng.lit(&vars), rng.lit(&vars));
        if a.var() != b.var() {
            add_binary(s, a, b);
        }
    }
    for _ in 0..200 {
        s.add_clause(random_long_clause(rng, &vars));
    }
    // Base binaries into the primary spans (the incremental attach puts
    // them in the overflow lists; a rebuild is what a search's inprocessing
    // or a bulk load leaves behind).
    s.rebuild_watches_and_binary_graph();
    Layout {
        long,
        medium,
        short,
        fresh: (0..400).map(|_| s.new_var()).collect(),
    }
}

fn random_long_clause(rng: &mut Rng, vars: &[Var]) -> Vec<Lit> {
    let mut lits: Vec<Lit> = (0..3 + rng.below(5)).map(|_| rng.lit(vars)).collect();
    lits.sort_by_key(|l| l.var().index());
    lits.dedup_by_key(|l| l.var());
    lits
}

fn build_scope(s: &mut Solver, layout: &Layout, rng: &mut Rng) {
    let mut fresh = layout.fresh.iter();
    let mut next = || Lit::pos(*fresh.next().unwrap_or(&layout.fresh[0]));
    // (c v x): its triggers are ¬c (the star's list) and ¬x (one edge).
    for trigger in &layout.long {
        for _ in 0..30 {
            add_binary(s, trigger.negate(), next());
        }
    }
    for trigger in &layout.medium {
        add_binary(s, trigger.negate(), next());
    }
    for trigger in &layout.short {
        for _ in 0..3 {
            add_binary(s, trigger.negate(), next());
        }
    }
    let rest = fresh.as_slice();
    for _ in 0..120 {
        let (a, b) = (rng.lit(rest), rng.lit(rest));
        if a.var() != b.var() {
            add_binary(s, a, b);
        }
    }
    for _ in 0..60 {
        s.add_clause(random_long_clause(rng, rest));
    }
}

/// Pigeonhole `pigeons` into `holes` (`pigeons > holes`): UNSAT, and past
/// the conflict cap below, so a bounded search over it always comes back
/// with the cap's worth of learned clauses – binaries among them, since the
/// "no two pigeons share a hole" clauses are binary and share triggers.
fn add_pigeonhole(s: &mut Solver, pigeons: usize, holes: usize) -> Vec<Vec<Lit>> {
    let mut vars = Vec::new();
    for _ in 0..pigeons {
        let mut row = Vec::new();
        for _ in 0..holes {
            row.push(Lit::pos(s.new_var()));
        }
        vars.push(row);
    }
    for row in &vars {
        s.add_clause(row.iter().copied());
    }
    for (i, row) in vars.iter().enumerate() {
        for other in vars.iter().skip(i + 1) {
            for (a, b) in row.iter().zip(other) {
                add_binary(s, Lit::neg(a.var()), Lit::neg(b.var()));
            }
        }
    }
    vars
}

/// Twenty base edges under the trigger of each of the first literals: the
/// learned clauses over them land on LONG lists, which is where a retracted
/// batch needs the batched pass.
fn add_fans(s: &mut Solver, lits: &[Lit], leaves: usize) {
    for &l in lits {
        for _ in 0..leaves {
            let leaf = Lit::pos(s.new_var());
            add_binary(s, l, leaf);
        }
    }
}

/// After a retraction the learned-clause registry names no retracted id,
/// and only live clauses.
fn assert_registry_clean(s: &Solver, retracted: &[ClauseId], what: &str) {
    for &id in &s.learned_clause_ids {
        assert!(
            !retracted.contains(&id),
            "{what}: retracted id {id:?} still registered"
        );
        assert!(
            s.clauses.get(id).is_some_and(|c| !c.deleted),
            "{what}: registered id {id:?} is not a live clause"
        );
    }
}

/// A bounded search over the base: learns clauses (binaries among them)
/// into the current scope, up to the cap.
fn search_a_little(s: &mut Solver) {
    s.set_max_conflicts(Some(400));
    let _ = s.solve();
    s.set_max_conflicts(None);
    assert!(
        s.stats().conflicts >= 400,
        "the search must hit its cap ({} conflicts)",
        s.stats().conflicts
    );
}

fn assert_same_state(oracle: &Solver, batched: &Solver, what: &str) {
    crate::invariants::check_binary_graph_backing(batched)
        .unwrap_or_else(|e| panic!("{what}: binary graph backing: {e}"));
    assert_eq!(state_snapshot(oracle), state_snapshot(batched), "{what}");
}

/// How many implication lists hold at least `at_least` edges of `ids` and
/// more than `longer_than` edges in all.
fn count_lists_holding(s: &Solver, ids: &[ClauseId], at_least: usize, longer_than: usize) -> usize {
    let mut n = 0;
    for code in 0..2 * s.num_vars as u32 {
        let list = s.binary_graph.get(Lit::from_code(code));
        let mine = list.iter().filter(|(_, cid)| ids.contains(cid)).count();
        if mine >= at_least && list.len() > longer_than {
            n += 1;
        }
    }
    n
}

fn assert_same_search(oracle: &mut Solver, batched: &mut Solver, what: &str) {
    assert_eq!(
        format!("{:?}", oracle.solve()),
        format!("{:?}", batched.solve()),
        "{what}: verdict"
    );
    let (so, sb) = (oracle.stats(), batched.stats());
    assert_eq!(
        (so.conflicts, so.decisions, so.propagations),
        (sb.conflicts, sb.decisions, sb.propagations),
        "{what}: search counters"
    );
}

#[test]
fn pop_leaves_what_the_per_clause_removals_leave() {
    for round in 0u64..12 {
        let path = std::env::temp_dir().join(format!("nixie_sat_retract_pop_{round}.drat"));
        let other = path.with_extension("batched.drat");
        let mut oracle = Solver::new();
        let mut batched = Solver::new();
        for s in [&mut oracle, &mut batched] {
            let mut rng = Rng(0x5EED_1234_ABCD_0001 + round);
            let layout = build_base(s, &mut rng);
            let php = add_pigeonhole(s, 9, 8);
            add_fans(s, &php[0], 20);
            s.push();
            build_scope(s, &layout, &mut rng);
        }
        oracle.enable_drat_proof(&path).unwrap();
        batched.enable_drat_proof(&other).unwrap();
        search_a_little(&mut oracle);
        search_a_little(&mut batched);
        // Re-index the graph with the scope open (the mid-search CSR fold
        // and a bulk load's flush do): the scope's edges move from the
        // overflow lists into the primary spans, so the batched pass has a
        // span to compact as well.
        for s in [&mut oracle, &mut batched] {
            s.rebuild_watches_and_binary_graph();
        }
        assert!(
            count_lists_holding(
                &batched,
                &batched.assertion_levels.last().unwrap().clause_ids,
                2,
                8
            ) >= 6,
            "the scope's binaries must share long lists"
        );
        // A learned clause of the scope retired before the pop, edges
        // first (as the search's clause-database reduction does): its id
        // stays in the scope and names no live clause at the pop.
        let retired = oracle.learned_clause_ids.first().copied();
        for s in [&mut oracle, &mut batched] {
            if let Some(id) = retired {
                s.purge_binary_edges(id);
                s.clauses.remove(id);
            }
        }
        assert_same_state(&oracle, &batched, "before the pop");
        let scope: Vec<ClauseId> = oracle.assertion_levels.last().unwrap().clause_ids.clone();
        assert_eq!(scope, batched.assertion_levels.last().unwrap().clause_ids);
        let live_binaries = scope
            .iter()
            .filter(|&&id| {
                oracle
                    .clauses
                    .get(id)
                    .is_some_and(|c| c.lits.len() == 2 && !c.deleted)
            })
            .count();
        assert!(
            live_binaries >= 6 * 30 + 12 + 8 * 3,
            "the scope's binaries (got {live_binaries})"
        );
        // The oracle: the per-clause purge, as `pop` used to run it.
        for &id in &scope {
            oracle.purge_binary_edges(id);
        }
        oracle.pop();
        batched.pop();
        oracle.disable_drat_proof();
        batched.disable_drat_proof();
        assert_same_state(&oracle, &batched, "after the pop");
        assert_registry_clean(&oracle, &scope, "oracle after the pop");
        assert_registry_clean(&batched, &scope, "batched after the pop");
        let a = std::fs::read(&path).unwrap_or_default();
        let b = std::fs::read(&other).unwrap_or_default();
        let _ = std::fs::remove_file(&path);
        let _ = std::fs::remove_file(&other);
        assert!(!a.is_empty(), "the proof must have been written");
        assert_eq!(
            a, b,
            "the DRAT records of the scope's retraction must be identical"
        );
        assert_same_search(&mut oracle, &mut batched, "after the pop");
    }
}

#[test]
fn forget_leaves_what_the_per_clause_removals_leave() {
    for round in 0u64..8 {
        let mut oracle = Solver::new();
        let mut batched = Solver::new();
        let mut layout = None;
        for s in [&mut oracle, &mut batched] {
            let mut rng = Rng(0xA11C_E000_0000_0002 + round);
            let php = add_pigeonhole(s, 9, 8);
            add_fans(s, &php[0], 20);
            let l = build_base(s, &mut rng);
            if layout.is_none() {
                layout = Some(l);
            }
        }
        let layout = layout.unwrap();
        search_a_little(&mut oracle);
        search_a_little(&mut batched);
        // Learned BINARIES on long lists, by the learning path itself (an
        // empty trail, so none of them asserts anything): 20 on each of the
        // six 40-edge lists.  The search's own learned clauses are mostly
        // long, and the batched pass is for binaries.
        for s in [&mut oracle, &mut batched] {
            s.backtrack_to_root();
            for trigger in &layout.long {
                for _ in 0..20 {
                    let y = Lit::pos(s.new_var());
                    s.learn_clause(smallvec::smallvec![trigger.negate(), y]);
                }
            }
            // A rebuild puts every edge – the forgotten ones included –
            // into the primary spans.
            s.rebuild_watches_and_binary_graph();
        }
        assert_same_state(&oracle, &batched, "before the forget");
        let tail: Vec<ClauseId> = oracle.learned_clause_ids.clone();
        assert_eq!(tail, batched.learned_clause_ids);
        assert!(
            tail.len() >= 200,
            "the search must have learned clauses (got {})",
            tail.len()
        );
        // The batched pass must be in play: long lists hold several of the
        // forgotten binaries.
        let shared_long_lists = count_lists_holding(&batched, &tail, 2, 8);
        assert!(
            shared_long_lists >= 6,
            "long lists holding two of the forgotten binaries: {shared_long_lists}"
        );
        for &id in &tail {
            oracle.purge_binary_edges(id);
        }
        oracle.forget_learned_since(0);
        batched.forget_learned_since(0);
        assert_same_state(&oracle, &batched, "after the forget");
        assert_registry_clean(&oracle, &tail, "oracle after the forget");
        assert!(batched.learned_clause_ids.is_empty());
        assert_same_search(&mut oracle, &mut batched, "after the forget");
    }
}

#[test]
fn a_scope_of_short_lists_alone_is_retracted_by_the_per_edge_path() {
    // Nothing in this scope lands on a long list: every edge goes down the
    // per-edge removal, and no id is marked (there is no registry to filter).
    let mut s = Solver::new();
    let vars: Vec<Var> = (0..200).map(|_| s.new_var()).collect();
    s.push();
    let mut ids = Vec::new();
    for i in 0..100 {
        ids.push(add_binary(
            &mut s,
            Lit::pos(vars[i]),
            Lit::pos(vars[100 + i]),
        ));
    }
    assert_eq!(s.binary_graph.get(Lit::neg(vars[0])).len(), 1);
    s.pop();
    assert!(s.learned_clause_ids.is_empty());
    for v in &vars {
        assert!(s.binary_graph.get(Lit::pos(*v)).is_empty());
        assert!(s.binary_graph.get(Lit::neg(*v)).is_empty());
    }
    for id in ids {
        assert!(s.clauses.get(id).is_none_or(|c| c.deleted));
    }
    assert!(s.retract_scratch.dead.iter().all(|&m| !m));
    assert!(s.retract_scratch.trigger_pending.iter().all(|&p| !p));
    crate::invariants::check_binary_graph_backing(&s).unwrap();
    assert_eq!(SolverResult::Sat, s.solve());
}

#[test]
fn a_scope_of_one_edge_lists_under_one_trigger_is_retracted_in_a_pass() {
    // 200 clauses under one trigger: one collected list, compacted once.
    let mut s = Solver::new();
    let t = Lit::pos(s.new_var());
    let xs: Vec<Lit> = (0..200).map(|_| Lit::pos(s.new_var())).collect();
    s.push();
    for &x in &xs {
        add_binary(&mut s, t, x);
    }
    assert_eq!(s.binary_graph.get(t.negate()).len(), 200);
    s.pop();
    assert_eq!(s.binary_graph.get(t.negate()).len(), 0);
    for &x in &xs {
        assert!(s.binary_graph.get(x.negate()).is_empty());
    }
    assert!(s.retract_scratch.dead.iter().all(|&m| !m));
    assert!(s.retract_scratch.trigger_pending.iter().all(|&p| !p));
    crate::invariants::check_binary_graph_backing(&s).unwrap();
    assert_eq!(SolverResult::Sat, s.solve());
}

#[test]
fn retracting_an_empty_or_null_batch_is_a_no_op() {
    let mut rng = Rng(7);
    let mut s = Solver::new();
    build_base(&mut s, &mut rng);
    let before = state_snapshot(&s);
    s.retract_clauses(&[], true);
    s.retract_clauses(&[ClauseId::NULL, ClauseId::NULL], true);
    assert_eq!(before, state_snapshot(&s));
}
