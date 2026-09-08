//! Sample clause identities, then count all their BCP and first-UIP events.
//! Diagnostics only: no counter or storage from here influences the solver.

use crate::{ClauseDatabase, ClauseId, Solver};
use rustc_hash::FxHashMap;
use std::{
    io::{self, Write},
    num::NonZeroU64,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
};

const EPOCH: u64 = 4096;
const MAX_ROWS: usize = 250_000;
pub(crate) const HIT: usize = 1;
pub(crate) const PAYLOAD: usize = 2;
pub(crate) const SCAN: usize = 3;
pub(crate) const UNIT: usize = 4;
pub(crate) const CONFLICT: usize = 5;
pub(crate) const ANALYZE: usize = 6;
type Counts = [[u64; 7]; 2];

#[derive(Clone, Copy)]
enum Target {
    Learned(usize),
    Original,
    Deleted,
    Omitted,
}

#[derive(Clone, Copy)]
pub(crate) struct Event {
    target: Target,
    channel: usize,
}

#[derive(Debug)]
struct Row {
    id: ClauseId,
    epoch: u64,
    length: usize,
    glue: u32,
    tier: u8,
    counts: Counts,
}

#[derive(Debug)]
pub(crate) struct Collector {
    stride: NonZeroU64,
    start_conflict: u64,
    active: Arc<AtomicBool>,
    rows: Vec<Row>,
    last: FxHashMap<ClauseId, usize>,
    original: Counts,
    deleted: Counts,
    omitted: Counts,
    overflow: bool,
    limit: usize,
}

/// Owns only a shared diagnostic flag, so nested public solve entry points
/// do not reset the outer call's preprocessing observations. No solver borrow
/// is held and every early return releases the flag.
pub(crate) struct Session(Arc<AtomicBool>);

impl Drop for Session {
    fn drop(&mut self) {
        self.0.store(false, Ordering::Relaxed);
    }
}

fn selected(id: ClauseId, stride: NonZeroU64) -> bool {
    // Fixed SplitMix64 finalizer, independent of the solver RNG. Hashing the
    // identity rather than visit ordinal avoids traffic-dependent sampling.
    let mut x = u64::from(id.0).wrapping_add(0x9e37_79b9_7f4a_7c15);
    x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    (x ^ (x >> 31)).is_multiple_of(stride.get())
}

impl Collector {
    fn new(stride: NonZeroU64, start_conflict: u64) -> Self {
        Self {
            stride,
            start_conflict,
            active: Arc::new(AtomicBool::new(false)),
            rows: Vec::new(),
            last: FxHashMap::default(),
            original: [[0; 7]; 2],
            deleted: [[0; 7]; 2],
            omitted: [[0; 7]; 2],
            overflow: false,
            limit: MAX_ROWS,
        }
    }

    pub(crate) fn clear(&mut self, conflicts: u64) {
        self.start_conflict = conflicts;
        self.rows.clear();
        self.last.clear();
        self.original = [[0; 7]; 2];
        self.deleted = [[0; 7]; 2];
        self.omitted = [[0; 7]; 2];
        self.overflow = false;
    }

    fn event(
        &mut self,
        db: &ClauseDatabase,
        id: ClauseId,
        channel: usize,
        conflicts: u64,
    ) -> Event {
        let target = match db.get(id) {
            Some(c) if !c.deleted && c.learned => {
                let epoch = match conflicts.checked_sub(self.start_conflict) {
                    Some(n) => n / EPOCH,
                    None => {
                        self.overflow = true;
                        return Event {
                            target: Target::Omitted,
                            channel,
                        };
                    }
                };
                if let Some(&at) = self.last.get(&id)
                    && self.rows[at].epoch == epoch
                {
                    Target::Learned(at)
                } else if self.rows.len() == self.limit {
                    Target::Omitted
                } else {
                    let at = self.rows.len();
                    self.rows.push(Row {
                        id,
                        epoch,
                        length: c.lits.len(),
                        glue: c.lbd,
                        tier: c.tier as u8,
                        counts: [[0; 7]; 2],
                    });
                    self.last.insert(id, at);
                    Target::Learned(at)
                }
            }
            Some(c) if !c.deleted => Target::Original,
            Some(_) | None => Target::Deleted,
        };
        Event { target, channel }
    }

    fn count(&mut self, event: Event, metric: usize) {
        let counts = match event.target {
            Target::Learned(at) => &mut self.rows[at].counts,
            Target::Original => &mut self.original,
            Target::Deleted => &mut self.deleted,
            Target::Omitted => &mut self.omitted,
        };
        let value = &mut counts[event.channel][metric];
        match value.checked_add(1) {
            Some(next) => *value = next,
            None => self.overflow = true,
        }
    }

    fn write(&self, db: &ClauseDatabase, conflicts: u64, mut out: impl Write) -> io::Result<()> {
        let elapsed = conflicts
            .checked_sub(self.start_conflict)
            .ok_or_else(|| io::Error::other("clause traffic conflict counter moved backwards"))?;
        write!(
            out,
            "{{\"schema\":\"nixie-clause-traffic/1\",\"stride\":{},\"epoch_conflicts\":{EPOCH},\"elapsed_conflicts\":{elapsed},\"overflow\":{},\"original\":{:?},\"deleted\":{:?},\"omitted\":{:?},\"rows\":[",
            self.stride, self.overflow, self.original, self.deleted, self.omitted
        )?;
        for (i, row) in self.rows.iter().enumerate() {
            if i != 0 {
                write!(out, ",")?;
            }
            // Final status is not a lifetime or a missing-future-use claim.
            let status = match db.get(row.id) {
                Some(c) if !c.deleted && c.learned => "learned",
                Some(c) if !c.deleted => "original",
                Some(_) | None => "deleted",
            };
            write!(
                out,
                "{{\"id\":{},\"epoch\":{},\"length\":{},\"glue\":{},\"tier\":{},\"final_status\":\"{status}\",\"counts\":{:?}}}",
                row.id.0, row.epoch, row.length, row.glue, row.tier, row.counts
            )?;
        }
        writeln!(out, "]}}")
    }
}

/// Explicit activation for the instrumented library parity run. Absent from
/// ordinary builds and never a search-policy input.
pub(crate) fn parity_collector() -> Option<Box<Collector>> {
    std::env::var("NIXIE_CLAUSE_TRAFFIC_PARITY")
        .is_ok_and(|value| value == "1")
        .then(|| Box::new(Collector::new(NonZeroU64::MIN, 0)))
}

pub(crate) fn visit(
    stats: &mut Option<Box<Collector>>,
    db: &ClauseDatabase,
    id: ClauseId,
    channel: usize,
    conflicts: u64,
) -> Option<Event> {
    let stats = stats.as_mut()?;
    if !selected(id, stats.stride) {
        return None;
    }
    let event = stats.event(db, id, channel, conflicts);
    stats.count(event, 0);
    Some(event)
}

pub(crate) fn record(stats: &mut Option<Box<Collector>>, event: Option<Event>, metric: usize) {
    if let (Some(stats), Some(event)) = (stats, event) {
        stats.count(event, metric);
    }
}

pub(crate) fn analyze(
    stats: &mut Option<Box<Collector>>,
    db: &ClauseDatabase,
    id: ClauseId,
    conflicts: u64,
) {
    let Some(stats) = stats else {
        return;
    };
    if !selected(id, stats.stride) {
        return;
    }
    let channel = usize::from(db.get(id).is_some_and(|c| c.lits.len() > 2));
    let event = stats.event(db, id, channel, conflicts);
    stats.count(event, ANALYZE);
}

impl Solver {
    /// Enable a bounded, read-only per-clause cost/use census. The fixed hash
    /// selects roughly one in `stride` clause IDs, independently of their work.
    /// Requires the `clause-traffic` feature. Each outer solve starts a new
    /// session; push/pop/reset also clear it. Ordinary builds have no observer.
    pub fn enable_clause_traffic(&mut self, stride: NonZeroU64) {
        self.clause_traffic = Some(Box::new(Collector::new(stride, self.stats.conflicts)));
    }

    /// Write the current session's JSON census, including omissions/overflow.
    /// Rows count BCP events and main first-UIP expansions, not all possible
    /// semantic uses of a clause. Instrumented timings are not throughput data.
    ///
    /// # Errors
    /// Returns an error if disabled, the conflict clock moved backwards, or
    /// the output writer fails. Counter overflow is explicit in the report.
    pub fn write_clause_traffic(&self, writer: impl Write) -> io::Result<()> {
        let Some(stats) = &self.clause_traffic else {
            return Err(io::Error::other("clause traffic census is disabled"));
        };
        stats.write(&self.clauses, self.stats.conflicts, writer)
    }

    pub(crate) fn begin_clause_traffic_session(&mut self) -> Option<Session> {
        let stats = self.clause_traffic.as_mut()?;
        if stats.active.load(Ordering::Relaxed) {
            return None;
        }
        stats.clear(self.stats.conflicts);
        stats.active.store(true, Ordering::Relaxed);
        Some(Session(Arc::clone(&stats.active)))
    }

    pub(crate) fn clear_clause_traffic(&mut self) {
        if let Some(stats) = &mut self.clause_traffic {
            stats.clear(self.stats.conflicts);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ConfigPreset, Lit, SolverResult, Var};

    fn lit(v: u32) -> Lit {
        Lit::pos(Var(v))
    }

    fn learned(db: &mut ClauseDatabase) -> ClauseId {
        db.add_learned([lit(0), lit(1), lit(2)])
    }

    fn collector() -> Option<Box<Collector>> {
        Some(Box::new(Collector::new(NonZeroU64::MIN, 0)))
    }

    #[test]
    fn complete_selected_clause_events_and_epochs_are_distinct() {
        let mut db = ClauseDatabase::new();
        let id = learned(&mut db);
        db.set_lbd(id, 7);
        let mut c = collector();
        let event = visit(&mut c, &db, id, 1, 4095);
        for metric in [PAYLOAD, SCAN, SCAN, UNIT] {
            record(&mut c, event, metric);
        }
        analyze(&mut c, &db, id, 4095);
        let event = visit(&mut c, &db, id, 0, 4096);
        record(&mut c, event, HIT);
        let Some(c) = c else {
            panic!("missing collector");
        };
        assert_eq!(c.rows.len(), 2);
        assert_eq!(c.rows[0].counts[1], [1, 0, 1, 2, 1, 0, 1]);
        assert_eq!(c.rows[1].counts[0], [1, 1, 0, 0, 0, 0, 0]);
        assert_eq!((c.rows[0].epoch, c.rows[1].epoch), (0, 1));
        assert_eq!((c.rows[0].length, c.rows[0].glue), (3, 7));
    }

    #[test]
    fn sampling_is_identity_based_and_ignores_visit_frequency() {
        let mut db = ClauseDatabase::new();
        let ids: Vec<_> = (0..1000).map(|_| learned(&mut db)).collect();
        let Some(stride) = NonZeroU64::new(16) else {
            panic!("positive stride");
        };
        let mut c = Some(Box::new(Collector::new(stride, 0)));
        for (i, &id) in ids.iter().enumerate() {
            for _ in 0..i % 17 + 1 {
                assert_eq!(visit(&mut c, &db, id, 1, 0).is_some(), selected(id, stride));
            }
        }
        let Some(c) = c else {
            panic!("missing collector");
        };
        assert_eq!(
            c.rows.len(),
            ids.iter().filter(|&&id| selected(id, stride)).count()
        );
        assert!(c.rows.len() > 30 && c.rows.len() < 100);
        for row in c.rows {
            assert_eq!(
                row.counts[1][0],
                ids.iter()
                    .position(|&id| id == row.id)
                    .map(|i| (i % 17 + 1) as u64)
                    .unwrap_or(0)
            );
        }
    }

    #[test]
    fn deleted_and_original_events_do_not_become_learned_rows() {
        let mut db = ClauseDatabase::new();
        let id = learned(&mut db);
        let original = db.add_original([lit(0), lit(1)]);
        let mut c = collector();
        let event = visit(&mut c, &db, id, 1, 0);
        record(&mut c, event, PAYLOAD);
        db.remove(id);
        let event = visit(&mut c, &db, id, 1, 1);
        record(&mut c, event, HIT);
        analyze(&mut c, &db, original, 1);
        let Some(c) = c else {
            panic!("missing collector");
        };
        assert_eq!(c.rows.len(), 1);
        assert_eq!(c.deleted[1], [1, 1, 0, 0, 0, 0, 0]);
        assert_eq!(c.original[0][ANALYZE], 1);
        let mut bytes = Vec::new();
        assert!(c.write(&db, 1, &mut bytes).is_ok());
        let Ok(report) = serde_json::from_slice::<serde_json::Value>(&bytes) else {
            panic!("invalid JSON");
        };
        assert_eq!(report["rows"][0]["final_status"], "deleted");
    }

    #[test]
    fn capacity_overflow_and_clock_errors_are_explicit() {
        let mut db = ClauseDatabase::new();
        let id = learned(&mut db);
        let mut c = collector();
        let Some(stats) = &mut c else {
            panic!("missing collector");
        };
        stats.limit = 1;
        let first = visit(&mut c, &db, id, 1, 0);
        let omitted = visit(&mut c, &db, id, 1, EPOCH);
        record(&mut c, omitted, SCAN);
        let Some(stats) = &mut c else {
            panic!("missing collector");
        };
        assert_eq!(stats.omitted[1][0], 1);
        assert_eq!(stats.omitted[1][SCAN], 1);
        stats.rows[0].counts[1][HIT] = u64::MAX;
        record(&mut c, first, HIT);
        let Some(stats) = &mut c else {
            panic!("missing collector");
        };
        assert!(stats.overflow);
        stats.clear(100);
        let _ = visit(&mut c, &db, id, 1, 99);
        let Some(stats) = &c else {
            panic!("missing collector");
        };
        assert!(stats.overflow);
        assert!(stats.write(&db, 99, Vec::new()).is_err());
    }

    #[test]
    fn nested_sessions_scope_changes_and_reset_preserve_lifecycle() {
        fn send_sync<T: Send + Sync>() {}
        send_sync::<Solver>();
        let mut s = Solver::new();
        s.enable_clause_traffic(NonZeroU64::MIN);
        let outer = s.begin_clause_traffic_session();
        let id = learned(&mut s.clauses);
        let _ = visit(&mut s.clause_traffic, &s.clauses, id, 1, 0);
        assert!(s.begin_clause_traffic_session().is_none());
        assert_eq!(s.clause_traffic.as_ref().map(|c| c.rows.len()), Some(1));
        drop(outer);
        let next = s.begin_clause_traffic_session();
        assert_eq!(s.clause_traffic.as_ref().map(|c| c.rows.len()), Some(0));
        drop(next);
        for reset in 0..3 {
            let _ = visit(&mut s.clause_traffic, &s.clauses, id, 1, 0);
            match reset {
                0 => s.push(),
                1 => s.pop(),
                2 => s.reset(),
                _ => unreachable!(),
            }
            assert_eq!(s.clause_traffic.as_ref().map(|c| c.rows.len()), Some(0));
        }
        let reused = learned(&mut s.clauses);
        assert_eq!(id, reused);
        let _ = visit(&mut s.clause_traffic, &s.clauses, reused, 1, 0);
        assert_eq!(s.clause_traffic.as_ref().map(|c| c.rows.len()), Some(1));
    }

    #[test]
    fn sat_unsat_search_models_and_lrat_transcripts_are_identical() {
        for holes in [3, 4] {
            let mut outputs = Vec::new();
            for enabled in [false, true] {
                let mut config = ConfigPreset::CaDiCaL.config();
                config.enable_inprocessing = false;
                config.enable_bve = false;
                let mut s = Solver::with_config(config);
                let proof = s.enable_lrat_transcript();
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
                if enabled {
                    s.enable_clause_traffic(NonZeroU64::MIN);
                }
                assert_eq!(
                    s.solve(),
                    if holes == 3 {
                        SolverResult::Unsat
                    } else {
                        SolverResult::Sat
                    }
                );
                if enabled {
                    let Some(c) = &s.clause_traffic else {
                        panic!("missing collector");
                    };
                    assert!(c.original.iter().flatten().any(|&v| v > 0));
                    if holes == 3 {
                        assert!(
                            c.rows
                                .iter()
                                .any(|r| r.counts.iter().any(|ch| ch[ANALYZE] > 0))
                        );
                    }
                    assert!(!c.active.load(Ordering::Relaxed));
                    let mut bytes = Vec::new();
                    assert!(s.write_clause_traffic(&mut bytes).is_ok());
                    assert!(serde_json::from_slice::<serde_json::Value>(&bytes).is_ok());
                }
                let Ok(transcript) = proof.snapshot() else {
                    panic!("missing LRAT transcript");
                };
                outputs.push((
                    format!("{:?}", s.stats()),
                    format!("{:?}", s.trail),
                    s.model().to_vec(),
                    format!("{transcript:?}"),
                ));
            }
            assert_eq!(outputs[0], outputs[1]);
        }
    }

    #[test]
    fn disabled_and_failed_writers_return_errors() {
        struct Failed;
        impl Write for Failed {
            fn write(&mut self, _: &[u8]) -> io::Result<usize> {
                Err(io::Error::other("test writer failure"))
            }
            fn flush(&mut self) -> io::Result<()> {
                Ok(())
            }
        }
        let mut s = Solver::new();
        assert!(s.write_clause_traffic(Vec::new()).is_err());
        s.enable_clause_traffic(NonZeroU64::MIN);
        assert!(s.write_clause_traffic(Failed).is_err());
    }
}
