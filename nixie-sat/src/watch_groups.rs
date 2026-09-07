//! Sampled, read-only opportunity measurement for shared blocking literals.
//! This module is absent unless `bcp-groups` is enabled. No observation is a
//! propagation certificate or a solver policy input.

use crate::{Solver, literal::Lit, trail::Trail, watched::Watcher};
use rustc_hash::FxHashMap;
use std::io::{self, Write};
use std::num::NonZeroU64;

const MAX_SNAPSHOT_ENTRIES: usize = 262_144;
const MAX_HISTORY_ENTRIES: usize = 1_000_000;
const MAX_HISTORY_LISTS: usize = 65_536;

#[derive(Debug)]
struct Entry {
    clause: u32,
    blocker: u32,
    true_at_entry: bool,
}

#[derive(Debug)]
pub(crate) struct Sample {
    trigger: u32,
    ordinal: u64,
    conflict_bin: usize,
    entries: Vec<Entry>,
    hits: Vec<bool>,
}

impl Sample {
    pub(crate) fn observe(&mut self, watcher: Watcher, hit: bool) {
        let entry = &self.entries[self.hits.len()];
        assert_eq!(
            (entry.clause, entry.blocker),
            (watcher.clause.0, watcher.blocker.code())
        );
        assert!(
            !entry.true_at_entry || hit,
            "true blocker changed during forward propagation"
        );
        self.hits.push(hit);
    }
}

#[derive(Debug)]
struct Previous {
    ordinal: u64,
    members: Vec<(u32, u32)>,
}

#[derive(Debug, Default)]
struct Counts {
    lists_seen: u64,
    offered_entries: u64,
    samples: u64,
    skipped_lists: u64,
    skipped_entries: u64,
    visited: u64,
    hits: u64,
    entry_true: u64,
    entry_true_groups: u64,
    actual_true_groups: u64,
    large_group_entries: u64,
    adjacent_hits: u64,
    removed: u64,
    blocker_updates: u64,
    conflict_samples: u64,
    history_pairs: u64,
    history_old_entries: u64,
    history_new_entries: u64,
    history_unchanged: u64,
    history_gap_sum: u64,
    history_gap_max: u64,
    history_skipped: u64,
    history_resets: u64,
    // Group-size bins: 1, 2, 3, 4..7, 8..15, 16..31, 32+.
    group_counts: [u64; 7],
    group_entries: [u64; 7],
    // Conflict bins: 0, 1..1023, 1024..16383, 16384+.
    // Columns: visited, entry-true hits, duplicate checks, large-group entries.
    by_conflicts: [[u64; 4]; 4],
}

#[derive(Debug)]
pub(crate) struct Collector {
    stride: NonZeroU64,
    counts: Counts,
    history: FxHashMap<u32, Previous>,
    history_entries: usize,
    history_limit: usize,
}

impl Collector {
    fn new(stride: NonZeroU64) -> Self {
        Self {
            stride,
            counts: Counts::default(),
            history: FxHashMap::default(),
            history_entries: 0,
            history_limit: MAX_HISTORY_ENTRIES,
        }
    }

    pub(crate) fn clear_history(&mut self) {
        self.history.clear();
        self.history_entries = 0;
        self.counts.history_resets += 1;
    }

    pub(crate) fn begin(
        &mut self,
        trigger: Lit,
        watches: &[Watcher],
        trail: &Trail,
        conflicts: u64,
    ) -> Option<Sample> {
        if watches.is_empty() {
            return None;
        }
        let ordinal = self.counts.lists_seen;
        self.counts.lists_seen += 1;
        self.counts.offered_entries += watches.len() as u64;
        if !ordinal.is_multiple_of(self.stride.get()) {
            return None;
        }
        if watches.len() > MAX_SNAPSHOT_ENTRIES {
            self.counts.skipped_lists += 1;
            self.counts.skipped_entries += watches.len() as u64;
            return None;
        }
        let conflict_bin = match conflicts {
            0 => 0,
            1..=1023 => 1,
            1024..=16383 => 2,
            _ => 3,
        };
        Some(Sample {
            trigger: trigger.code(),
            ordinal,
            conflict_bin,
            entries: watches
                .iter()
                .map(|w| Entry {
                    clause: w.clause.0,
                    blocker: w.blocker.code(),
                    true_at_entry: trail.lit_val_hot(w.blocker) > 0,
                })
                .collect(),
            hits: Vec::with_capacity(watches.len()),
        })
    }

    pub(crate) fn finish(&mut self, sample: Sample, after: &[Watcher], conflict: bool) {
        assert!(conflict || sample.hits.len() == sample.entries.len());
        let mut at_entry = FxHashMap::<u32, u64>::default();
        let mut actual = FxHashMap::<u32, u64>::default();
        let mut previous_hit = None;
        let c = &mut self.counts;
        c.samples += 1;
        c.conflict_samples += u64::from(conflict);
        c.visited += sample.hits.len() as u64;
        let mut entry_hits = 0;
        for (entry, &hit) in sample.entries.iter().zip(&sample.hits) {
            if entry.true_at_entry {
                *at_entry.entry(entry.blocker).or_default() += 1;
                entry_hits += 1;
            }
            if hit {
                c.hits += 1;
                *actual.entry(entry.blocker).or_default() += 1;
                c.adjacent_hits += u64::from(previous_hit == Some(entry.blocker));
                previous_hit = Some(entry.blocker);
            } else {
                previous_hit = None;
            }
        }
        c.entry_true += entry_hits;
        c.entry_true_groups += at_entry.len() as u64;
        c.actual_true_groups += actual.len() as u64;
        let mut large_entries = 0;
        for &size in at_entry.values() {
            let bin = match size {
                0 => unreachable!(),
                1 => 0,
                2 => 1,
                3 => 2,
                4..=7 => 3,
                8..=15 => 4,
                16..=31 => 5,
                _ => 6,
            };
            c.group_counts[bin] += 1;
            c.group_entries[bin] += size;
            if size >= 4 {
                large_entries += size;
            }
        }
        c.large_group_entries += large_entries;
        let row = &mut c.by_conflicts[sample.conflict_bin];
        for (field, delta) in row.iter_mut().zip([
            sample.hits.len() as u64,
            entry_hits,
            entry_hits - at_entry.len() as u64,
            large_entries,
        ]) {
            *field += delta;
        }

        // Compaction preserves clause order. Include the untouched conflict
        // tail for membership comparisons, but never count it as visited.
        let mut survivors = after.iter().peekable();
        for entry in &sample.entries {
            if let Some(w) = survivors.peek()
                && w.clause.0 == entry.clause
            {
                c.blocker_updates += u64::from(w.blocker.code() != entry.blocker);
                survivors.next();
            } else {
                c.removed += 1;
            }
        }
        assert!(
            survivors.next().is_none(),
            "watch order changed outside compaction"
        );

        let mut before: Vec<_> = sample
            .entries
            .iter()
            .map(|e| (e.clause, e.blocker))
            .collect();
        before.sort_unstable();
        if let Some(previous) = self.history.remove(&sample.trigger) {
            self.history_entries -= previous.members.len();
            let gap = sample.ordinal - previous.ordinal;
            c.history_pairs += 1;
            c.history_gap_sum += gap;
            c.history_gap_max = c.history_gap_max.max(gap);
            c.history_old_entries += previous.members.len() as u64;
            c.history_new_entries += before.len() as u64;
            c.history_unchanged += intersection_count(&previous.members, &before);
        }
        if self.history_entries + after.len() <= self.history_limit
            && self.history.len() < MAX_HISTORY_LISTS
        {
            let mut members: Vec<_> = after
                .iter()
                .map(|w| (w.clause.0, w.blocker.code()))
                .collect();
            members.sort_unstable();
            self.history_entries += members.len();
            self.history.insert(
                sample.trigger,
                Previous {
                    ordinal: sample.ordinal,
                    members,
                },
            );
        } else {
            c.history_skipped += 1;
        }
    }

    fn write_report(&self, mut out: impl Write) -> io::Result<()> {
        let c = &self.counts;
        write!(
            out,
            "{{\"schema\":\"nixie-watch-groups/1\",\"stride\":{}",
            self.stride
        )?;
        write!(
            out,
            ",\"snapshot_entry_limit\":{MAX_SNAPSHOT_ENTRIES},\"history_entry_limit\":{},\"history_list_limit\":{MAX_HISTORY_LISTS}",
            self.history_limit
        )?;
        macro_rules! fields {
            ($($field:ident),* $(,)?) => { $(write!(out, ",\"{}\":{}", stringify!($field), c.$field)?;)* };
        }
        fields!(
            lists_seen,
            offered_entries,
            samples,
            skipped_lists,
            skipped_entries,
            visited,
            hits,
            entry_true,
            entry_true_groups,
            actual_true_groups,
            large_group_entries,
            adjacent_hits,
            removed,
            blocker_updates,
            conflict_samples,
            history_pairs,
            history_old_entries,
            history_new_entries,
            history_unchanged,
            history_gap_sum,
            history_gap_max,
            history_skipped,
            history_resets
        );
        write!(
            out,
            ",\"duplicate_entry_true\":{},\"duplicate_actual_true\":{}",
            c.entry_true - c.entry_true_groups,
            c.hits - c.actual_true_groups
        )?;
        // Debug formatting of fixed arrays of integers is also valid JSON.
        writeln!(
            out,
            ",\"group_counts\":{:?},\"group_entries\":{:?},\"by_conflicts\":{:?}}}",
            c.group_counts, c.group_entries, c.by_conflicts
        )
    }
}

fn intersection_count(a: &[(u32, u32)], b: &[(u32, u32)]) -> u64 {
    let (mut i, mut j, mut count) = (0, 0, 0);
    while i < a.len() && j < b.len() {
        match a[i].cmp(&b[j]) {
            core::cmp::Ordering::Less => i += 1,
            core::cmp::Ordering::Greater => j += 1,
            core::cmp::Ordering::Equal => {
                count += 1;
                i += 1;
                j += 1;
            }
        }
    }
    count
}

impl Solver {
    /// Enable sampled shared-blocker observations for this solver, resetting
    /// earlier observations. Available only with the `bcp-groups` feature.
    /// Observed timings include instrumentation overhead and are not solver
    /// throughput measurements. Sampling uses nonempty watch-list ordinals.
    pub fn enable_watch_group_stats(&mut self, stride: NonZeroU64) {
        self.watch_group_stats = Some(Box::new(Collector::new(stride)));
    }

    /// Write one JSON report. Counters describe sampled visits, and persistence
    /// compares successive sampled visits of a trigger. Oversize samples and
    /// history capacity omissions are explicitly counted. Collection must
    /// first be enabled with [`Self::enable_watch_group_stats`].
    pub fn write_watch_group_report(&self, out: impl Write) -> io::Result<()> {
        match &self.watch_group_stats {
            Some(stats) => stats.write_report(out),
            None => Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "watch group observations are disabled",
            )),
        }
    }

    pub(crate) fn clear_watch_group_history(&mut self) {
        if let Some(stats) = &mut self.watch_group_stats {
            stats.clear_history();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ClauseId, ConfigPreset, SolverResult, memory::ClauseRef};

    fn watches(blockers: &[u32]) -> Vec<Watcher> {
        blockers
            .iter()
            .enumerate()
            .map(|(i, &b)| {
                Watcher::new(ClauseId::new(i as u32), ClauseRef::NULL, Lit::from_code(b))
            })
            .collect()
    }

    fn begin(c: &mut Collector, w: &[Watcher], t: &Trail) -> Sample {
        let Some(s) = c.begin(Lit::from_code(0), w, t, 10) else {
            panic!("test visit must be sampled");
        };
        s
    }

    #[test]
    fn counts_shared_true_groups_and_adjacent_runs() {
        let mut c = Collector::new(NonZeroU64::MIN);
        let w = watches(&[2, 2, 2, 2, 4, 4, 6]);
        let mut t = Trail::new(4);
        t.assign_decision(Lit::from_code(2));
        t.assign_decision(Lit::from_code(4));
        let mut s = begin(&mut c, &w, &t);
        for (i, &w) in w.iter().enumerate() {
            s.observe(w, i < 6);
        }
        c.finish(s, &w, false);
        assert_eq!(c.counts.visited, 7);
        assert_eq!(c.counts.entry_true, 6);
        assert_eq!(c.counts.entry_true_groups, 2);
        assert_eq!(c.counts.large_group_entries, 4);
        assert_eq!(c.counts.adjacent_hits, 4);
        assert_eq!(c.counts.group_counts, [0, 1, 0, 1, 0, 0, 0]);
        assert_eq!(c.counts.by_conflicts[1], [7, 6, 4, 4]);
        let mut out = Vec::new();
        assert!(c.write_report(&mut out).is_ok());
        let Ok(report) = serde_json::from_slice::<serde_json::Value>(&out) else {
            panic!("invalid JSON report");
        };
        assert_eq!(report["duplicate_entry_true"], 4);
    }

    #[test]
    fn conflict_tail_is_not_counted_as_a_visit_or_group_member() {
        let mut c = Collector::new(NonZeroU64::MIN);
        let w = watches(&[2, 2, 4, 2, 2, 2]);
        let mut t = Trail::new(3);
        t.assign_decision(Lit::from_code(2));
        let mut s = begin(&mut c, &w, &t);
        for (&w, hit) in w.iter().zip([true, true, false]) {
            s.observe(w, hit);
        }
        c.finish(s, &w, true);
        assert_eq!(c.counts.visited, 3);
        assert_eq!(c.counts.entry_true, 2);
        assert_eq!(c.counts.entry_true_groups, 1);
        assert_eq!(c.counts.large_group_entries, 0);
        assert_eq!(c.counts.removed, 0);
        assert_eq!(c.counts.conflict_samples, 1);
    }

    #[test]
    fn becoming_true_during_a_visit_is_reported_separately() {
        let mut c = Collector::new(NonZeroU64::MIN);
        let w = watches(&[2, 2, 2, 2]);
        let mut t = Trail::new(2);
        let mut s = begin(&mut c, &w, &t);
        s.observe(w[0], false);
        t.assign_decision(Lit::from_code(2));
        for &w in &w[1..] {
            s.observe(w, t.lit_val_hot(w.blocker) > 0);
        }
        c.finish(s, &w, false);
        assert_eq!(c.counts.entry_true, 0);
        assert_eq!(c.counts.hits, 3);
        assert_eq!(c.counts.actual_true_groups, 1);
        assert_eq!(c.counts.adjacent_hits, 2);
    }

    #[test]
    fn tracks_churn_and_exact_sampled_membership() {
        let mut c = Collector::new(NonZeroU64::MIN);
        let w = watches(&[2, 4, 2]);
        let t = Trail::new(5);
        let mut s = begin(&mut c, &w, &t);
        for &w in &w {
            s.observe(w, false);
        }
        let mut after = vec![w[0], w[2]];
        after[0].blocker = Lit::from_code(6);
        c.finish(s, &after, false);
        assert_eq!(c.counts.removed, 1);
        assert_eq!(c.counts.blocker_updates, 1);
        after[1].blocker = Lit::from_code(4);
        after.push(Watcher::new(
            ClauseId::new(3),
            ClauseRef::NULL,
            Lit::from_code(8),
        ));
        let mut s = begin(&mut c, &after, &t);
        for &w in &after {
            s.observe(w, false);
        }
        c.finish(s, &after, false);
        assert_eq!(c.counts.history_pairs, 1);
        assert_eq!(c.counts.history_old_entries, 2);
        assert_eq!(c.counts.history_new_entries, 3);
        assert_eq!(c.counts.history_unchanged, 1);
        assert_eq!(c.counts.history_gap_sum, 1);
        assert_eq!(
            intersection_count(&[(1, 2), (1, 2), (3, 4)], &[(1, 2), (3, 5)]),
            1
        );
    }

    #[test]
    fn sampling_and_memory_omissions_are_explicit() {
        let Some(stride) = NonZeroU64::new(2) else {
            panic!("positive stride");
        };
        let mut c = Collector::new(stride);
        let t = Trail::new(2);
        assert!(c.begin(Lit::from_code(0), &[], &t, 0).is_none());
        let w = watches(&[2, 2]);
        c.history_limit = 1;
        let mut s = begin(&mut c, &w, &t);
        for &w in &w {
            s.observe(w, false);
        }
        c.finish(s, &w, false);
        assert_eq!(c.counts.history_skipped, 1);
        assert!(c.begin(Lit::from_code(0), &w, &t, 0).is_none());
        let oversized = vec![w[0]; MAX_SNAPSHOT_ENTRIES + 1];
        assert!(c.begin(Lit::from_code(0), &oversized, &t, 0).is_none());
        assert_eq!(c.counts.lists_seen, 3);
        assert_eq!(c.counts.skipped_lists, 1);
        assert_eq!(c.counts.skipped_entries, oversized.len() as u64);
        assert_eq!(c.counts.samples, 1);
    }

    fn seed_history(solver: &mut Solver) {
        let Some(c) = solver.watch_group_stats.as_mut() else {
            panic!("collector disabled");
        };
        let w = watches(&[2]);
        let mut s = begin(c, &w, &Trail::new(2));
        s.observe(w[0], false);
        c.finish(s, &w, false);
        assert_eq!(c.history.len(), 1);
    }

    #[test]
    fn scope_and_solve_boundaries_invalidate_history() {
        let mut solver = Solver::new();
        solver.enable_watch_group_stats(NonZeroU64::MIN);
        seed_history(&mut solver);
        solver.push();
        assert_eq!(
            solver.watch_group_stats.as_ref().map(|c| c.history.len()),
            Some(0)
        );
        seed_history(&mut solver);
        solver.pop();
        assert_eq!(
            solver.watch_group_stats.as_ref().map(|c| c.history.len()),
            Some(0)
        );
        seed_history(&mut solver);
        assert_eq!(solver.solve(), SolverResult::Sat);
        assert_eq!(
            solver.watch_group_stats.as_ref().map(|c| c.history.len()),
            Some(0)
        );
        solver.enable_watch_group_stats(NonZeroU64::MIN);
        assert_eq!(
            solver.watch_group_stats.as_ref().map(|c| c.counts.samples),
            Some(0)
        );
    }

    #[test]
    fn observation_preserves_search_on_sat_and_unsat_pigeonholes() {
        for holes in [3, 4] {
            let mut plain = Solver::with_config(ConfigPreset::CaDiCaL.config());
            let mut observed = Solver::with_config(ConfigPreset::CaDiCaL.config());
            observed.enable_watch_group_stats(NonZeroU64::MIN);
            for solver in [&mut plain, &mut observed] {
                let vars: Vec<_> = (0..4 * holes).map(|_| solver.new_var()).collect();
                for pigeon in 0..4 {
                    solver.add_clause((0..holes).map(|h| Lit::pos(vars[pigeon * holes + h])));
                }
                for h in 0..holes {
                    for a in 0..4 {
                        for b in a + 1..4 {
                            solver.add_clause([
                                Lit::neg(vars[a * holes + h]),
                                Lit::neg(vars[b * holes + h]),
                            ]);
                        }
                    }
                }
            }
            let expected = if holes == 3 {
                SolverResult::Unsat
            } else {
                SolverResult::Sat
            };
            assert_eq!(plain.solve(), expected);
            assert_eq!(observed.solve(), expected);
            assert_eq!(plain.model(), observed.model());
            assert_eq!(
                format!("{:?}", plain.stats()),
                format!("{:?}", observed.stats())
            );
            assert!(
                observed
                    .watch_group_stats
                    .as_ref()
                    .is_some_and(|c| c.counts.visited > 0)
            );
        }
    }
}
