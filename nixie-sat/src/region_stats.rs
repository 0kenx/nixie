//! Read-only traffic census for a fixed snapshot of certified gate clauses.
//! Components are candidates, not executable blocks. Every event revalidates
//! its gate certificate; variable/component labels still describe the snapshot.

use crate::{ClauseDatabase, ClauseId, Lit, Solver, xor::XorDetector};
use rustc_hash::FxHashMap;
use std::{
    io::{self, Write},
    num::NonZeroU64,
};

const LIMIT: usize = 2_000_000;
const OUTSIDE: usize = usize::MAX;
type Key = [u32; 3];

// Channel: binary, long. Class: region gate, small gate, invalidated gate,
// original local/boundary/outside, learned local/boundary/outside, dead.
// Metric: visits, immediate satisfaction, payload accesses, tail inspections,
// propagations, conflicts. These are event counts, never physical-cost ticks.
pub(crate) const HIT: usize = 1;
pub(crate) const PAYLOAD: usize = 2;
pub(crate) const SCAN: usize = 3;
pub(crate) const UNIT: usize = 4;
pub(crate) const CONFLICT: usize = 5;

fn key(lits: &[Lit]) -> Option<Key> {
    if !(2..=3).contains(&lits.len()) {
        return None;
    }
    let mut k = [u32::MAX; 3];
    for (dst, lit) in k.iter_mut().zip(lits) {
        *dst = lit.code();
    }
    k.sort_unstable();
    if k[..lits.len()].windows(2).any(|w| w[0] / 2 == w[1] / 2) {
        return None;
    }
    Some(k)
}

fn root(parent: &mut [usize], mut v: usize) -> usize {
    while parent[v] != v {
        parent[v] = parent[parent[v]];
        v = parent[v];
    }
    v
}

#[derive(Debug)]
struct Gate {
    sources: Vec<(ClauseId, Key)>,
    vars: [usize; 3],
    region: bool,
}

impl Gate {
    fn valid(&self, db: &ClauseDatabase) -> bool {
        self.sources.iter().all(|&(id, expected)| {
            db.get(id)
                .is_some_and(|c| !c.deleted && !c.learned && key(c.lits) == Some(expected))
        })
    }
}

#[derive(Clone, Copy)]
pub(crate) struct Event {
    channel: usize,
    class: usize,
}

#[derive(Debug)]
pub(crate) struct Collector {
    stride: NonZeroU64,
    triggers: u64,
    samples: u64,
    gates: Vec<Gate>,
    membership: FxHashMap<ClauseId, Vec<usize>>,
    regions: Vec<usize>,
    short_clauses: usize,
    ands: usize,
    xors: usize,
    components: usize,
    region_gates: usize,
    region_vars: usize,
    counts: [[[u64; 6]; 10]; 2],
    by_conflicts: [[[u64; 10]; 2]; 3],
}

impl Collector {
    fn empty(stride: NonZeroU64) -> Self {
        Self {
            stride,
            triggers: 0,
            samples: 0,
            gates: Vec::new(),
            membership: FxHashMap::default(),
            regions: Vec::new(),
            short_clauses: 0,
            ands: 0,
            xors: 0,
            components: 0,
            region_gates: 0,
            region_vars: 0,
            counts: [[[0; 6]; 10]; 2],
            by_conflicts: [[[0; 10]; 2]; 3],
        }
    }

    fn build(
        db: &ClauseDatabase,
        nvars: usize,
        stride: NonZeroU64,
        limit: usize,
    ) -> io::Result<Self> {
        let exhausted = || io::Error::other("region snapshot exceeds its deterministic capacity");
        if nvars > limit {
            return Err(exhausted());
        }
        let mut c = Self::empty(stride);
        let mut index = FxHashMap::<Key, ClauseId>::default();
        for id in db.iter_ids() {
            let Some(clause) = db.get(id).filter(|c| !c.deleted && !c.learned) else {
                continue;
            };
            let Some(k) = key(clause.lits) else {
                continue;
            };
            // Append-only IDs: retain the first copy, independently of hash iteration.
            index.entry(k).or_insert(id);
            if index.len() > limit {
                return Err(exhausted());
            }
        }
        c.short_clauses = index.len();
        let mut ternary: Vec<_> = index
            .iter()
            .filter(|(k, _)| k[2] != u32::MAX)
            .map(|(&k, &id)| (k, id))
            .collect();
        ternary.sort_unstable_by_key(|&(k, _)| k);
        for &(k, id) in &ternary {
            for i in 0..3 {
                let o = Lit::from_code(k[i]);
                let a = Lit::from_code(k[(i + 1) % 3]).negate();
                let b = Lit::from_code(k[(i + 2) % 3]).negate();
                let (Some(ka), Some(kb)) = (key(&[o.negate(), a]), key(&[o.negate(), b])) else {
                    continue;
                };
                if let (Some(&ia), Some(&ib)) = (index.get(&ka), index.get(&kb)) {
                    c.gates.push(Gate {
                        sources: vec![(id, k), (ia, ka), (ib, kb)],
                        vars: k.map(|l| (l / 2) as usize),
                        region: false,
                    });
                    c.ands += 1;
                    break;
                }
            }
            if c.gates.len() > limit {
                return Err(exhausted());
            }
        }
        let clauses: Vec<_> = ternary
            .iter()
            .map(|&(k, id)| (k.into_iter().map(Lit::from_code).collect(), id))
            .collect();
        let mut xors = XorDetector::new(3, 3).detect_xor(&clauses);
        xors.sort_by_key(|x| x.vars.iter().map(|v| v.index()).collect::<Vec<_>>());
        for x in xors {
            let [a, b, d] = x.vars.as_slice() else {
                return Err(io::Error::other("invalid three-variable XOR certificate"));
            };
            let mut sources = Vec::new();
            for id in x.source_clauses {
                let Some(k) = db.get(id).and_then(|clause| key(clause.lits)) else {
                    return Err(io::Error::other(
                        "XOR certificate references an absent short clause",
                    ));
                };
                sources.push((id, k));
            }
            if sources.len() != 4 {
                return Err(io::Error::other("incomplete XOR certificate"));
            }
            sources.sort_unstable_by_key(|&(id, _)| id.0);
            c.gates.push(Gate {
                sources,
                vars: [a.index(), b.index(), d.index()],
                region: false,
            });
            c.xors += 1;
            if c.gates.len() > limit {
                return Err(exhausted());
            }
        }
        let mut parent: Vec<_> = (0..nvars).collect();
        for g in &c.gates {
            if g.vars.iter().any(|&v| v >= nvars) {
                return Err(io::Error::other("gate variable outside snapshot"));
            }
            for &v in &g.vars[1..] {
                let a = root(&mut parent, g.vars[0]);
                let b = root(&mut parent, v);
                parent[a.max(b)] = a.min(b);
            }
        }
        let mut sizes = vec![0usize; nvars];
        for g in &c.gates {
            sizes[root(&mut parent, g.vars[0])] += 1;
        }
        c.components = sizes.iter().filter(|&&n| n >= 4).count();
        c.regions = (0..nvars)
            .map(|v| {
                let r = root(&mut parent, v);
                if sizes[r] >= 4 { r } else { OUTSIDE }
            })
            .collect();
        c.region_vars = c.regions.iter().filter(|&&r| r != OUTSIDE).count();
        for (i, g) in c.gates.iter_mut().enumerate() {
            g.region = c.regions[g.vars[0]] != OUTSIDE;
            c.region_gates += usize::from(g.region);
            for &(id, _) in &g.sources {
                c.membership.entry(id).or_default().push(i);
            }
        }
        Ok(c)
    }

    pub(crate) fn begin(&mut self, nonempty: bool) -> bool {
        if !nonempty {
            return false;
        }
        let selected = self.triggers.is_multiple_of(self.stride.get());
        self.triggers += 1;
        self.samples += u64::from(selected);
        selected
    }

    fn class(&self, db: &ClauseDatabase, id: ClauseId) -> usize {
        let Some(clause) = db.get(id).filter(|c| !c.deleted) else {
            return 9;
        };
        if let Some(gates) = self.membership.get(&id) {
            let mut small = false;
            for &i in gates {
                let g = &self.gates[i];
                if g.valid(db) {
                    if g.region {
                        return 0;
                    }
                    small = true;
                }
            }
            return if small { 1 } else { 2 };
        }
        let mut first = None;
        let mut outside = false;
        let mut crossing = false;
        for lit in clause.lits {
            let r = self
                .regions
                .get(lit.var().index())
                .copied()
                .unwrap_or(OUTSIDE);
            if r == OUTSIDE {
                outside = true;
            } else if let Some(prev) = first {
                crossing |= prev != r;
            } else {
                first = Some(r);
            }
        }
        let incidence = if first.is_none() {
            2
        } else if outside || crossing {
            1
        } else {
            0
        };
        if clause.learned {
            6 + incidence
        } else {
            3 + incidence
        }
    }

    fn write_report(&self, mut out: impl Write) -> io::Result<()> {
        writeln!(
            out,
            "{{\"schema\":\"nixie-region-traffic/1\",\"stride\":{},\"snapshot_limit\":{LIMIT},\"triggers\":{},\"samples\":{},\"short_clauses\":{},\"and_gates\":{},\"xor_gates\":{},\"candidate_components\":{},\"region_gates\":{},\"region_vars\":{},\"counts\":{:?},\"by_conflicts\":{:?}}}",
            self.stride,
            self.triggers,
            self.samples,
            self.short_clauses,
            self.ands,
            self.xors,
            self.components,
            self.region_gates,
            self.region_vars,
            self.counts,
            self.by_conflicts
        )
    }
}

pub(crate) fn visit(
    stats: &mut Option<Box<Collector>>,
    sampled: bool,
    db: &ClauseDatabase,
    id: ClauseId,
    channel: usize,
    conflicts: u64,
) -> Option<Event> {
    if !sampled {
        return None;
    }
    let c = stats.as_mut()?;
    let class = c.class(db, id);
    let bin = match conflicts {
        0 => 0,
        1..=16383 => 1,
        _ => 2,
    };
    c.counts[channel][class][0] += 1;
    c.by_conflicts[bin][channel][class] += 1;
    Some(Event { channel, class })
}

pub(crate) fn record(stats: &mut Option<Box<Collector>>, event: Option<Event>, metric: usize) {
    if let (Some(c), Some(e)) = (stats, event) {
        c.counts[e.channel][e.class][metric] += 1;
    }
}

/// Explicit parity-only activation: an empty reference snapshot exercises all
/// observation hooks through Context's private SAT solver. Certificate logic
/// is covered by direct tests and the three nonempty-snapshot measurement cells.
pub(crate) fn parity_collector() -> Option<Box<Collector>> {
    (std::env::var("NIXIE_REGION_PARITY").as_deref() == Ok("1"))
        .then(|| Box::new(Collector::empty(NonZeroU64::MIN)))
}

impl Solver {
    /// Reset a read-only, sampled BCP census against the current original-clause
    /// snapshot. Components remain snapshot labels across later scope changes;
    /// every counted gate certificate is revalidated against live clauses.
    /// [`Self::reset`] discards the snapshot because database IDs restart.
    /// Capacity failure leaves prior observations unchanged and returns an error.
    pub fn enable_region_stats(&mut self, stride: NonZeroU64) -> io::Result<()> {
        let c = Collector::build(&self.clauses, self.num_vars(), stride, LIMIT)?;
        self.region_stats = Some(Box::new(c));
        Ok(())
    }

    /// Write sampled traffic as JSON. Instrumented timings are not throughput
    /// results; the study documents array dimensions and opportunity limits.
    pub fn write_region_report(&self, out: impl Write) -> io::Result<()> {
        match &self.region_stats {
            Some(c) => c.write_report(out),
            None => Err(io::Error::other("region observations are disabled")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ConfigPreset, SolverResult, Var, watched::WatchLists};

    fn lit(n: usize) -> Lit {
        Lit::pos(Var::new(n as u32))
    }

    fn and(db: &mut ClauseDatabase, output: Lit, a: Lit, b: Lit) -> [ClauseId; 3] {
        [
            db.add_original([output, a.negate(), b.negate()]),
            db.add_original([output.negate(), a]),
            db.add_original([output.negate(), b]),
        ]
    }

    fn collect(db: &ClauseDatabase, nvars: usize) -> Collector {
        match Collector::build(db, nvars, NonZeroU64::MIN, LIMIT) {
            Ok(c) => c,
            Err(e) => panic!("snapshot failed: {e}"),
        }
    }

    #[test]
    fn certificates_match_truth_tables_for_every_signed_and_and_xor() {
        for signs in 0..8 {
            let ls: Vec<_> = (0..3)
                .map(|i| {
                    if signs >> i & 1 == 1 {
                        lit(i).negate()
                    } else {
                        lit(i)
                    }
                })
                .collect();
            for xor in [false, true] {
                let mut db = ClauseDatabase::new();
                if xor {
                    for pattern in [0u32, 3, 5, 6] {
                        db.add_original(
                            ls.iter()
                                .enumerate()
                                .rev()
                                .map(|(i, &l)| if pattern >> i & 1 == 1 { l.negate() } else { l }),
                        );
                    }
                } else {
                    and(&mut db, ls[0], ls[1], ls[2]);
                }
                let c = collect(&db, 3);
                assert_eq!((c.ands, c.xors), if xor { (0, 1) } else { (1, 0) });
                assert!(c.gates[0].valid(&db));
                for assignment in 0..8 {
                    let value = |l: Lit| ((assignment >> l.var().index() & 1) == 1) == l.is_pos();
                    let cnf = c.gates[0].sources.iter().all(|&(id, _)| {
                        db.get(id)
                            .is_some_and(|clause| clause.lits.iter().copied().any(value))
                    });
                    let expected = if xor {
                        value(ls[0]) ^ value(ls[1]) ^ value(ls[2])
                    } else {
                        value(ls[0]) == (value(ls[1]) && value(ls[2]))
                    };
                    assert_eq!(
                        cnf, expected,
                        "signs={signs} xor={xor} assignment={assignment}"
                    );
                }
            }
        }
    }

    #[test]
    fn incomplete_and_duplicate_encodings_do_not_fabricate_gates() {
        for missing in 0..3 {
            let mut db = ClauseDatabase::new();
            let ids = and(&mut db, lit(0), lit(1), lit(2));
            db.remove(ids[missing]);
            assert!(collect(&db, 3).gates.is_empty());
        }
        let mut db = ClauseDatabase::new();
        and(&mut db, lit(0), lit(1), lit(2));
        and(&mut db, lit(0), lit(1), lit(2));
        assert_eq!(collect(&db, 3).ands, 1);
        let mut db = ClauseDatabase::new();
        for _ in 0..4 {
            db.add_original([lit(0), lit(1), lit(2)]);
        }
        assert!(collect(&db, 3).gates.is_empty());
        assert!(key(&[lit(0), lit(0)]).is_none());
        assert!(key(&[lit(0), lit(0).negate(), lit(1)]).is_none());
    }

    #[test]
    fn changed_deleted_and_relocated_support_is_checked_exactly() {
        let mut db = ClauseDatabase::new();
        let ids = and(&mut db, lit(0), lit(1), lit(2));
        let c = collect(&db, 4);
        assert_eq!(c.class(&db, ids[0]), 1);
        db.swap_lits(ids[0], 0, 2);
        db.compact_arena_forced(&mut WatchLists::new(4));
        assert_eq!(c.class(&db, ids[0]), 1);
        assert!(db.shrink(ids[1], &[lit(0).negate(), lit(3)]));
        assert_eq!(c.class(&db, ids[0]), 2);
        assert!(db.shrink(ids[1], &[lit(0).negate(), lit(1)]));
        assert_eq!(c.class(&db, ids[0]), 1);
        db.remove(ids[2]);
        assert_eq!(c.class(&db, ids[0]), 2);
        assert_eq!(c.class(&db, ids[2]), 9);
        let fresh = db.add_original([lit(0).negate(), lit(2)]);
        assert_ne!(fresh, ids[2]);
        assert_eq!(c.class(&db, ids[0]), 2);
    }

    #[test]
    fn candidate_components_and_boundary_traffic_have_distinct_classes() {
        let mut db = ClauseDatabase::new();
        let mut region_ids = Vec::new();
        for base in [0, 10] {
            for i in 0..4 {
                region_ids.extend(and(&mut db, lit(base + i), lit(base + 4), lit(base + 5)));
            }
        }
        let mut c = collect(&db, 22);
        assert_eq!((c.components, c.region_gates, c.region_vars), (2, 8, 12));
        for id in region_ids {
            assert_eq!(c.class(&db, id), 0);
        }
        for learned in [false, true] {
            for (lits, incidence) in [
                (vec![lit(0), lit(1)], 0),
                (vec![lit(0), lit(10)], 1),
                (vec![lit(0), lit(21)], 1),
                (vec![lit(20), lit(21)], 2),
                (vec![lit(22)], 2),
            ] {
                let id = if learned {
                    db.add_learned(lits)
                } else {
                    db.add_original(lits)
                };
                assert_eq!(
                    c.class(&db, id),
                    if learned {
                        6 + incidence
                    } else {
                        3 + incidence
                    }
                );
            }
        }
        assert!(!c.begin(false));
        assert!(c.begin(true));
        c.stride = match NonZeroU64::new(2) {
            Some(n) => n,
            None => panic!("positive stride"),
        };
        assert!(!c.begin(true));
        assert!(c.begin(true));
        assert_eq!((c.triggers, c.samples), (3, 2));
    }

    #[test]
    fn capacity_errors_do_not_return_partial_snapshots() {
        let mut db = ClauseDatabase::new();
        and(&mut db, lit(0), lit(1), lit(2));
        assert!(Collector::build(&db, 3, NonZeroU64::MIN, 2).is_err());
        // Exhaust short-clause capacity with fewer variables than the limit.
        db.add_original([lit(0), lit(1)]);
        assert!(Collector::build(&db, 3, NonZeroU64::MIN, 3).is_err());
    }

    #[test]
    fn popped_support_invalidates_fixed_snapshot_and_activation_resets_it() {
        let mut s = Solver::new();
        for _ in 0..3 {
            s.new_var();
        }
        s.add_clause([lit(0), lit(1).negate(), lit(2).negate()]);
        let Some(id) = s.clauses.iter_ids().next() else {
            panic!("original clause missing");
        };
        s.push();
        s.add_clause([lit(0).negate(), lit(1)]);
        s.add_clause([lit(0).negate(), lit(2)]);
        assert!(s.enable_region_stats(NonZeroU64::MIN).is_ok());
        assert_eq!(
            s.region_stats.as_ref().map(|c| c.class(&s.clauses, id)),
            Some(1)
        );
        s.pop();
        assert_eq!(
            s.region_stats.as_ref().map(|c| c.class(&s.clauses, id)),
            Some(2)
        );
        assert!(s.enable_region_stats(NonZeroU64::MIN).is_ok());
        assert_eq!(s.region_stats.as_ref().map(|c| c.gates.len()), Some(0));
    }

    #[test]
    fn reset_discards_certificates_before_database_ids_are_reused() {
        let mut s = Solver::new();
        for _ in 0..3 {
            s.new_var();
        }
        s.add_clause([lit(0), lit(1).negate(), lit(2).negate()]);
        s.add_clause([lit(0).negate(), lit(1)]);
        s.add_clause([lit(0).negate(), lit(2)]);
        assert!(s.enable_region_stats(NonZeroU64::MIN).is_ok());
        assert_eq!(s.region_stats.as_ref().map(|c| c.gates.len()), Some(1));
        s.reset();
        assert!(
            s.region_stats
                .as_ref()
                .is_none_or(|c| c.gates.is_empty() && c.regions.is_empty())
        );
        for _ in 0..3 {
            s.new_var();
        }
        s.add_clause([lit(0), lit(1), lit(2)]);
        assert!(s.enable_region_stats(NonZeroU64::MIN).is_ok());
        assert_eq!(
            s.region_stats.as_ref().map(|c| (c.gates.len(), c.triggers)),
            Some((0, 0))
        );
    }

    #[test]
    fn sat_unsat_scope_state_and_lrat_transcripts_match() {
        for holes in [3, 4] {
            let mut outputs = Vec::new();
            for enabled in [false, true] {
                let mut s = Solver::with_config(ConfigPreset::CaDiCaL.config());
                s.region_stats = None;
                let handle = s.enable_lrat_transcript();
                let vars: Vec<_> = (0..4 * holes).map(|_| s.new_var()).collect();
                for p in 0..4 {
                    s.add_clause((0..holes).map(|h| Lit::pos(vars[p * holes + h])));
                }
                for h in 0..holes {
                    for a in 0..4 {
                        for b in a + 1..4 {
                            s.add_clause([
                                Lit::neg(vars[a * holes + h]),
                                Lit::neg(vars[b * holes + h]),
                            ]);
                        }
                    }
                }
                // Real candidate region, with independently constrained inputs.
                let gvars: Vec<_> = (0..6).map(|_| s.new_var()).collect();
                for &o in &gvars[..4] {
                    s.add_clause([Lit::pos(o), Lit::neg(gvars[4]), Lit::neg(gvars[5])]);
                    s.add_clause([Lit::neg(o), Lit::pos(gvars[4])]);
                    s.add_clause([Lit::neg(o), Lit::pos(gvars[5])]);
                }
                if enabled {
                    assert!(s.enable_region_stats(NonZeroU64::MIN).is_ok());
                }
                s.add_clause([Lit::pos(gvars[4])]);
                s.add_clause([Lit::pos(gvars[5])]);
                assert_eq!(
                    s.solve(),
                    if holes == 3 {
                        SolverResult::Unsat
                    } else {
                        SolverResult::Sat
                    }
                );
                if enabled {
                    assert!(
                        s.region_stats
                            .as_ref()
                            .is_some_and(|c| c.counts.iter().any(|ch| ch[0][0] > 0))
                    );
                    let mut report = Vec::new();
                    assert!(s.write_region_report(&mut report).is_ok());
                    assert!(serde_json::from_slice::<serde_json::Value>(&report).is_ok());
                }
                let Ok(transcript) = handle.snapshot() else {
                    panic!("missing LRAT transcript");
                };
                outputs.push((
                    format!("{:?}", s.stats()),
                    format!("{:?}", s.trail),
                    s.model().to_vec(),
                    format!("{transcript:?}"),
                ));
                s.push();
                s.pop();
                let repeated = s.solve();
                outputs.push((
                    format!("{:?}", s.stats()),
                    format!("{:?}", s.trail),
                    s.model().to_vec(),
                    format!("{repeated:?}"),
                ));
            }
            assert_eq!(outputs[0], outputs[2]);
            assert_eq!(outputs[1], outputs[3]);
        }
    }
}
