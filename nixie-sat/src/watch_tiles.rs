//! Experimental shared-blocker certificates over consecutive watch-list tiles.
//! Masks refer to the current flat list. Only a true blocker permits a skip;
//! compaction and blocker changes repair membership before another pass.

use crate::{Solver, literal::Lit, trail::Trail, watched::Watcher};

const WIDTH: usize = 64;
const MIN_TILE: usize = 16;
const MIN_GROUP: u32 = 4;
const REBUILD_EDITS: u64 = 64;

macro_rules! count {
    ($work:expr, $field:ident, $n:expr) => {
        #[cfg(feature = "bcp-tiles-stats")]
        {
            $work.$field += ($n) as u64;
        }
    };
}
pub(crate) use count;

macro_rules! work_fields {
    ($($field:ident),+ $(,)?) => {
        #[derive(Debug, Default)]
        pub(crate) struct Work {
            $(#[cfg(feature = "bcp-tiles-stats")] pub $field: u64,)+
        }
        #[cfg(feature = "bcp-tiles-stats")]
        impl Work {
            pub(crate) fn merge(&mut self, other: Self) { $(self.$field += other.$field;)+ }
            fn write(&self, mut out: impl std::io::Write) -> std::io::Result<()> {
                write!(out, "{{\"schema\":\"nixie-watch-tiles/1\"")?;
                $(write!(out, ",\"{}\":{}", stringify!($field), self.$field)?;)+
                writeln!(out, "}}")
            }
        }
    };
}
work_fields!(
    lists,
    scalar_visits,
    skipped,
    skip_spans,
    skipped_copies,
    tiles_entered,
    group_checks,
    tile_builds,
    build_entries,
    build_comparisons,
    groups_built,
    changed_entries,
    removed_entries,
    mask_deletions,
    suffix_rebuilds,
);

#[derive(Debug, Clone)]
struct Group {
    blocker: Lit,
    mask: u64,
}

#[derive(Debug, Clone)]
struct Tile {
    len: usize,
    groups: Vec<Group>,
    changed: u64,
    removed: u64,
    edits: u64,
}

impl Tile {
    fn build(watches: &[Watcher], _work: &mut Work) -> Self {
        assert!(!watches.is_empty() && watches.len() <= WIDTH);
        count!(_work, tile_builds, 1);
        count!(_work, build_entries, watches.len());
        let mut sorted = [(0u32, 0usize); WIDTH];
        for (i, w) in watches.iter().enumerate() {
            sorted[i] = (w.blocker.code(), i);
        }
        sorted[..watches.len()].sort_unstable_by(|a, b| {
            count!(_work, build_comparisons, 1);
            a.0.cmp(&b.0)
        });
        let mut groups = Vec::new();
        let mut start = 0;
        while start < watches.len() {
            let blocker = sorted[start].0;
            let mut end = start;
            let mut mask = 0;
            while end < watches.len() && sorted[end].0 == blocker {
                mask |= 1u64 << sorted[end].1;
                end += 1;
            }
            if mask.count_ones() >= MIN_GROUP {
                groups.push(Group {
                    blocker: Lit::from_code(blocker),
                    mask,
                });
            }
            start = end;
        }
        count!(_work, groups_built, groups.len());
        Self {
            len: watches.len(),
            groups,
            changed: 0,
            removed: 0,
            edits: 0,
        }
    }
}

/// Cached metadata only: the ordinary watcher vector remains authoritative.
#[derive(Debug, Clone, Default)]
pub(crate) struct Cache {
    tiles: Vec<Tile>,
    covered: usize,
}

impl Cache {
    pub(crate) fn prepare(&mut self, watches: &[Watcher], work: &mut Work) {
        assert!(
            self.covered <= watches.len(),
            "watch cache missed an invalidation"
        );
        while watches.len() - self.covered >= MIN_TILE {
            let end = (self.covered + WIDTH).min(watches.len());
            self.tiles
                .push(Tile::build(&watches[self.covered..end], work));
            self.covered = end;
        }
        debug_assert!(self.consistent(watches));
    }

    /// Patch one visited position. The cursor still uses the pre-pass masks;
    /// those only certify blockers already true when the tile was entered.
    pub(crate) fn changed(&mut self, cursor: &Cursor, read: usize, removed: bool) {
        if let Some(tile) = self.tiles.get_mut(cursor.tile) {
            assert!(read >= cursor.start && read < cursor.start + tile.len);
            let bit = 1u64 << (read - cursor.start);
            tile.changed |= bit;
            if removed {
                tile.removed |= bit;
            }
        }
    }

    pub(crate) fn finish(&mut self, watches: &[Watcher], work: &mut Work) {
        #[cfg(feature = "bcp-tiles-stats")]
        for tile in &self.tiles {
            count!(work, changed_entries, tile.changed.count_ones());
            count!(work, removed_entries, tile.removed.count_ones());
        }
        let mut start = 0;
        let mut rebuild_suffix = None;
        for (i, tile) in self.tiles.iter_mut().enumerate() {
            let removed = tile.removed.count_ones() as usize;
            let changed = tile.changed.count_ones() as u64;
            tile.edits += changed;
            tile.len -= removed;
            if tile.len < MIN_TILE {
                rebuild_suffix = Some(i);
                count!(work, suffix_rebuilds, 1);
                break;
            }
            assert!(start + tile.len <= watches.len());
            if tile.edits >= REBUILD_EDITS {
                *tile = Tile::build(&watches[start..start + tile.len], work);
            } else if tile.changed != 0 {
                for group in &mut tile.groups {
                    group.mask &= !tile.changed;
                    count!(work, mask_deletions, removed);
                    group.mask = delete_positions(group.mask, tile.removed);
                }
                tile.groups.retain(|g| g.mask.count_ones() >= MIN_GROUP);
                tile.changed = 0;
                tile.removed = 0;
            }
            start += tile.len;
        }
        if let Some(i) = rebuild_suffix {
            self.tiles.truncate(i);
        }
        self.covered = start;
        // Dropping a depleted tile exposes its suffix as the scalar tail.
        // Rebuild in logical order, charging every scanned watcher.
        self.prepare(watches, work);
    }

    fn consistent(&self, watches: &[Watcher]) -> bool {
        let mut start = 0;
        for tile in &self.tiles {
            if tile.len == 0 || tile.len > WIDTH || start + tile.len > watches.len() {
                return false;
            }
            let mut seen = 0;
            for group in &tile.groups {
                if group.mask & !low_bits(tile.len) != 0 || group.mask & seen != 0 {
                    return false;
                }
                seen |= group.mask;
                let mut bits = group.mask;
                while bits != 0 {
                    let i = bits.trailing_zeros() as usize;
                    if watches[start + i].blocker != group.blocker {
                        return false;
                    }
                    bits &= bits - 1;
                }
            }
            start += tile.len;
        }
        start == self.covered
    }
}

fn low_bits(n: usize) -> u64 {
    if n == WIDTH {
        u64::MAX
    } else {
        (1u64 << n) - 1
    }
}

/// Stable bit compaction. Descending deletion leaves every lower original
/// position unchanged until its turn; the top-bit case avoids a shift by 64.
fn delete_positions(mut mask: u64, mut removed: u64) -> u64 {
    while removed != 0 {
        let bit = (63 - removed.leading_zeros()) as usize;
        let high = if bit == 63 { 0 } else { mask >> (bit + 1) };
        mask = (mask & low_bits(bit)) | (high << bit);
        removed &= !(1u64 << bit);
    }
    mask
}

#[derive(Default)]
pub(crate) struct Cursor {
    tile: usize,
    start: usize,
    end: usize,
    pending: u64,
    ready: bool,
}

impl Cursor {
    /// Return the end of a certified satisfied span, or `read` for a scalar
    /// visit. A span never crosses a tile boundary. Truth is checked afresh
    /// on entry to each tile and is never carried to another propagation pass.
    #[inline]
    pub(crate) fn skip(
        &mut self,
        cache: &Cache,
        trail: &Trail,
        read: usize,
        _work: &mut Work,
    ) -> usize {
        if self.ready && read >= self.end {
            self.tile += 1;
            self.start = self.end;
            self.ready = false;
        }
        let Some(tile) = cache.tiles.get(self.tile) else {
            return read;
        };
        if !self.ready {
            self.end = self.start + tile.len;
            self.pending = low_bits(tile.len);
            count!(_work, tiles_entered, 1);
            for group in &tile.groups {
                count!(_work, group_checks, 1);
                if trail.lit_val_hot(group.blocker) > 0 {
                    self.pending &= !group.mask;
                }
            }
            self.ready = true;
        }
        assert!(read >= self.start && read < self.end);
        let remaining = self.pending & (u64::MAX << (read - self.start));
        if remaining == 0 {
            self.end
        } else {
            self.start + remaining.trailing_zeros() as usize
        }
    }
}

impl Solver {
    /// Enable/disable the experimental tile kernel in a `bcp-tiles` build.
    /// The feature opts in by default; ordinary builds exclude the kernel.
    pub fn enable_watch_tiles(&mut self, enabled: bool) {
        self.use_watch_tiles = enabled;
        self.watches.clear_tile_caches();
    }

    /// Write explanatory maintenance counters. Instrumented timings include
    /// counter overhead; use the `bcp-tiles`-only build for throughput.
    #[cfg(feature = "bcp-tiles-stats")]
    pub fn write_watch_tile_report(&self, out: impl std::io::Write) -> std::io::Result<()> {
        self.watch_tile_work.write(out)
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

    #[test]
    fn compaction_matches_stable_filter_exhaustively() {
        for removed in 0u64..256 {
            for mask in 0u64..256 {
                let mut expected = 0;
                let mut write = 0;
                for bit in 0..8 {
                    if removed & (1 << bit) == 0 {
                        expected |= ((mask >> bit) & 1) << write;
                        write += 1;
                    }
                }
                assert_eq!(delete_positions(mask, removed), expected);
                assert_eq!(delete_positions(mask << 56, removed << 56), expected << 56);
            }
        }
        assert_eq!(delete_positions(u64::MAX, u64::MAX), 0);
    }

    #[test]
    fn skip_preserves_order_and_rechecks_truth_each_pass() {
        let mut cache = Cache::default();
        let mut work = Work::default();
        let w = watches(&[vec![2; 16], vec![4; 16], vec![6; 32], vec![4; 16]].concat());
        cache.prepare(&w, &mut work);
        let mut trail = Trail::new(4);
        trail.assign_decision(Lit::from_code(2));
        let mut cursor = Cursor::default();
        assert_eq!(cursor.skip(&cache, &trail, 0, &mut work), 16);
        assert_eq!(cursor.skip(&cache, &trail, 16, &mut work), 16);
        trail.assign_decision(Lit::from_code(4));
        // The old negative group test cannot suppress newly satisfied entries.
        assert_eq!(cursor.skip(&cache, &trail, 17, &mut work), 17);
        // The next tile sees current truth, so its group can be skipped.
        assert_eq!(cursor.skip(&cache, &trail, 64, &mut work), 80);
        let fresh = Trail::new(4);
        assert_eq!(Cursor::default().skip(&cache, &fresh, 0, &mut work), 0);
    }

    #[test]
    fn repairs_changes_removals_and_appended_delta() {
        let mut cache = Cache::default();
        let mut work = Work::default();
        let mut w = watches(&[2; 80]);
        cache.prepare(&w, &mut work);
        let trail = Trail::new(3);
        let mut cursor = Cursor::default();
        assert_eq!(cursor.skip(&cache, &trail, 0, &mut work), 0);
        cache.changed(&cursor, 0, true);
        cache.changed(&cursor, 10, false);
        w[10].blocker = Lit::from_code(4);
        w.remove(0);
        cache.finish(&w, &mut work);
        assert!(cache.consistent(&w));
        assert_eq!(cache.tiles[0].len, 63);
        w.extend(watches(&[4; 17]));
        cache.prepare(&w, &mut work);
        assert!(cache.consistent(&w));
        assert_eq!(cache.covered, w.len());
    }

    #[test]
    fn conflict_tail_and_depleted_suffix_survive() {
        let mut cache = Cache::default();
        let mut work = Work::default();
        let mut w = watches(&[vec![2; 64], vec![4; 64]].concat());
        cache.prepare(&w, &mut work);
        let mut cursor = Cursor::default();
        let trail = Trail::new(3);
        cursor.skip(&cache, &trail, 0, &mut work);
        for read in 0..50 {
            cache.changed(&cursor, read, true);
        }
        // Conflict at position 50: no following position has been changed.
        w.drain(..50);
        cache.finish(&w, &mut work);
        assert!(cache.consistent(&w));
        assert_eq!(w[0].clause, ClauseId::new(50));
        assert_eq!(w[77].clause, ClauseId::new(127));
    }

    #[test]
    fn sat_unsat_and_scope_trajectories_match_scalar() {
        for holes in [4, 5] {
            let mut scalar = Solver::with_config(ConfigPreset::CaDiCaL.config());
            scalar.enable_watch_tiles(false);
            let mut tiled = Solver::with_config(ConfigPreset::CaDiCaL.config());
            for solver in [&mut scalar, &mut tiled] {
                let vars: Vec<_> = (0..5 * holes).map(|_| solver.new_var()).collect();
                for p in 0..5 {
                    solver.add_clause((0..holes).map(|h| Lit::pos(vars[p * holes + h])));
                }
                for h in 0..holes {
                    for a in 0..5 {
                        for b in a + 1..5 {
                            solver.add_clause([
                                Lit::neg(vars[a * holes + h]),
                                Lit::neg(vars[b * holes + h]),
                            ]);
                        }
                    }
                }
            }
            let expected = if holes == 4 {
                SolverResult::Unsat
            } else {
                SolverResult::Sat
            };
            assert_eq!(scalar.solve(), expected);
            assert_eq!(tiled.solve(), expected);
            assert_eq!(scalar.model(), tiled.model());
            assert_eq!(
                format!("{:?}", scalar.stats()),
                format!("{:?}", tiled.stats())
            );
            for solver in [&mut scalar, &mut tiled] {
                solver.push();
                solver.pop();
            }
            assert_eq!(scalar.solve(), tiled.solve());
            assert_eq!(
                format!("{:?}", scalar.stats()),
                format!("{:?}", tiled.stats())
            );
        }
    }

    #[test]
    fn actual_skips_preserve_compaction_conflict_and_tail() {
        let mut outputs = Vec::new();
        for enabled in [false, true] {
            let mut solver = Solver::new();
            solver.enable_watch_tiles(enabled);
            let t = solver.new_var();
            let m = solver.new_var();
            let b = solver.new_var();
            let a = solver.new_var();
            let c = solver.new_var();
            let e = solver.new_var();
            solver.add_clause([Lit::neg(t), Lit::pos(m), Lit::pos(e)]);
            for _ in 0..64 {
                let v = solver.new_var();
                solver.add_clause([Lit::neg(t), Lit::pos(b), Lit::pos(v)]);
            }
            solver.add_clause([Lit::neg(t), Lit::pos(a), Lit::pos(c)]);
            for _ in 0..16 {
                let v = solver.new_var();
                solver.add_clause([Lit::neg(t), Lit::pos(b), Lit::pos(v)]);
            }
            assert!(!solver.assign_and_propagate_level0(&[
                Lit::pos(b),
                Lit::pos(t),
                Lit::neg(a),
                Lit::neg(c),
            ]));
            #[cfg(feature = "bcp-tiles-stats")]
            if enabled {
                assert!(solver.watch_tile_work.skipped > 0);
                assert!(solver.watch_tile_work.skipped_copies > 0);
            }
            outputs.push((
                format!("{:?}", solver.watches.packed_snapshot()),
                format!("{:?}", solver.trail),
                format!("{:?}", solver.stats()),
            ));
        }
        assert_eq!(outputs[0], outputs[1]);
    }

    #[test]
    fn lrat_transcript_is_identical_after_actual_group_skips() {
        let mut transcripts = Vec::new();
        for enabled in [false, true] {
            let mut solver = Solver::new();
            solver.enable_watch_tiles(enabled);
            let handle = solver.enable_lrat_transcript();
            let t = solver.new_var();
            let b = solver.new_var();
            for _ in 0..80 {
                let v = solver.new_var();
                solver.add_clause([Lit::neg(t), Lit::pos(b), Lit::pos(v)]);
            }
            solver.add_clause([Lit::pos(b)]);
            solver.add_clause([Lit::pos(t)]);
            let p = solver.new_var();
            let q = solver.new_var();
            for x in [Lit::pos(p), Lit::neg(p)] {
                for y in [Lit::pos(q), Lit::neg(q)] {
                    solver.add_clause([x, y]);
                }
            }
            assert_eq!(solver.solve(), SolverResult::Unsat);
            #[cfg(feature = "bcp-tiles-stats")]
            if enabled {
                assert!(solver.watch_tile_work.skipped > 0);
            }
            let Ok(transcript) = handle.snapshot() else {
                panic!("LRAT transcript failed");
            };
            transcripts.push(format!("{transcript:?}"));
        }
        assert_eq!(transcripts[0], transcripts[1]);
    }

    #[test]
    fn external_mutation_and_snapshot_restore_invalidate_certificates() {
        use crate::watched::WatchLists;
        let key = Lit::from_code(0);
        let mut lists = WatchLists::new(3);
        for w in watches(&[2; 32]) {
            lists.add(key, w);
        }
        let original = lists.packed_snapshot();
        let mut cache = lists.take_tile_cache(key);
        cache.prepare(lists.get(key), &mut Work::default());
        lists.put_tile_cache(key, cache);
        for w in lists.get_mut(key) {
            w.blocker = Lit::from_code(4);
        }
        let mut cache = lists.take_tile_cache(key);
        cache.prepare(lists.get(key), &mut Work::default());
        let mut trail = Trail::new(3);
        trail.assign_decision(Lit::from_code(2));
        assert_eq!(
            Cursor::default().skip(&cache, &trail, 0, &mut Work::default()),
            0
        );
        lists.put_tile_cache(key, cache);
        lists.restore(original);
        let mut cache = lists.take_tile_cache(key);
        cache.prepare(lists.get(key), &mut Work::default());
        assert_eq!(
            Cursor::default().skip(&cache, &trail, 0, &mut Work::default()),
            32
        );
    }
}
