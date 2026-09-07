//! Kitten — the embedded small CDCL solver (faithful port of kissat
//! `kitten.c`, the sub-solver behind SAT sweeping).
//!
//! Kitten is deliberately **not** the main solver: no arena, no
//! inprocessing, no proofs, no phase saving beyond a plain phase array.
//! It exists to answer bounded, assumption-driven satisfiability queries
//! over a *copy* of a fragment of the main formula (the sweep
//! environment), under a **tick budget** — a deterministic work counter,
//! never wall clock. Its API surface mirrors `kitten.h`:
//!
//! * lifecycle: [`Kitten::new`] / [`Kitten::clear`] (reset trail and
//!   clauses, keep capacities) — release is Rust `Drop`;
//! * problem: [`Kitten::unit`], [`Kitten::binary`], [`Kitten::clause`],
//!   [`Kitten::clause_with_id_and_exception`] (the id+exception form is
//!   how a caller maps kitten antecedents back to main-solver clauses),
//!   [`Kitten::assume`];
//! * budget: [`Kitten::set_ticks_limit_delta`] /
//!   [`Kitten::no_ticks_limit`] — [`Kitten::solve`] returns
//!   [`KittenResult::Unknown`] when the budget runs out (C returns 0);
//! * answers: [`Kitten::solve`] / [`Kitten::status`] /
//!   [`Kitten::value`] / [`Kitten::fixed`] / [`Kitten::failed`];
//! * phase / order control: [`Kitten::flip_phases`],
//!   [`Kitten::randomize_phases`], [`Kitten::shuffle_clauses`];
//! * core extraction (requires [`Kitten::track_antecedents`]):
//!   [`Kitten::compute_clausal_core`] + [`Kitten::traverse_core_clauses`].
//!
//! Internal encoding mirrors the C exactly: literals are `2*idx + sign`
//! (`u32`), clauses ("klauses") live in one flat `u32` arena with layout
//! `[aux, size, flags, lits.., (antecedent refs..)]` and are referenced
//! by word offset ("ref"). Watches carry a blocking literal and a binary
//! bit. The decision queue is the kissat stamped VMTF ring (`links` with
//! `prev/next/stamp`, `queue.search`), which also *is* the branching
//! heuristic: analyzed variables move to the back, decisions are taken
//! from the back, `search` skips assigned prefixes.
//!
//! Soundness notes that matter for the port:
//!
//! * Learned clauses are resolvents of database clauses only — assumption
//!   literals are decisions and never appear as reasons — so every learned
//!   clause is entailed by the clause set alone, which is what makes the
//!   extracted core (see [`Kitten::compute_clausal_core`]) sound to reuse.
//! * All walks (analysis, failed-assumption analysis, core computation)
//!   are iterative; no unbounded native recursion over user-controlled
//!   structure (see AGENTS.md).
//! * `INVALID` (`u32::MAX`) is never dereferenced: every path that can
//!   observe it is structured as an explicit check, and structurally
//!   impossible states surface as `debug_assert!` plus a conservative
//!   fallback (abort the solve as `Unknown`), never a fabricated answer.

/// Literal encoding: `2*idx + sign`, `u32::MAX` = invalid.
pub(crate) const INVALID: u32 = u32::MAX;

/// kissat's `MAX_VARS` bound: importing a variable at or beyond this
/// index would overflow the internal literal encoding. Callers feeding
/// larger codes (a sentinel, garbage) get a defensive rejection instead
/// of a multi-gigabyte import-table resize.
const MAX_VARS: u32 = (1u32 << 31) - 1;

/// A sane external-literal sanity bound for the sweeper's use: external
/// codes are main-solver literal codes, so anything at or beyond twice
/// this cannot name a real variable. Used to fail fast on sentinel
/// codes instead of resizing tables by 2^31 entries.
#[inline]
fn external_literal_sane(elit: u32) -> bool {
    (elit >> 1) < MAX_VARS
}

/// Flag bit: klause is part of the computed core.
const CORE_FLAG: u32 = 1;
/// Flag bit: klause was learned (not original input).
const LEARNED_FLAG: u32 = 2;

/// Result of [`Kitten::solve`] (kissat status codes 10/20/0).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum KittenResult {
    /// Formula (under current assumptions) satisfied — C status 10.
    Satisfied,
    /// Formula (under current assumptions) inconsistent — C status 20.
    Inconsistent,
    /// Tick budget exhausted — C status 0.
    Unknown,
}

/// Internal solver status (kissat codes).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Status {
    /// No result yet — 0.
    Unsolved,
    /// Last solve returned SAT — 10.
    Satisfied,
    /// Last solve returned UNSAT — 20.
    Inconsistent,
    /// UNSAT and the clausal core was computed — 21.
    InconsistentCore,
}

/// Per-variable assignment record: decision level and reason ref.
#[derive(Debug, Clone, Copy, Default)]
struct Kar {
    level: u32,
    reason: u32,
}

/// Decision-queue link: intrusive doubly-linked ring entry with a stamp
/// (insertion time) used by `search` to resume mid-queue.
#[derive(Debug, Clone, Copy)]
struct Kink {
    next: u32,
    prev: u32,
    stamp: u64,
}

/// One watch entry: blocking literal + klause ref (+ binary shortcut).
#[derive(Debug, Clone, Copy)]
struct Katch {
    blit: u32,
    reference: u32,
    binary: bool,
}

/// kitten statistics (mirrors the C counters; `ticks` is the budget
/// currency summed into the main solver's `kitten_ticks`).
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct KittenStats {
    pub ticks: u64,
    pub solved: u64,
    pub sat: u64,
    pub unsat: u64,
    pub unknown: u64,
    pub conflicts: u64,
    pub decisions: u64,
    pub propagations: u64,
    pub flips: u64,
    pub flipped: u64,
}

/// The embedded solver. See the module documentation for the contract.
#[derive(Debug, Clone)]
pub(crate) struct Kitten {
    status: Status,
    /// Antecedent tracking armed (before any learning).
    antecedents: bool,
    /// A learned klause exists (blocks arming antecedents late).
    learned: bool,

    level: u32,
    propagated: usize,
    unassigned: u32,
    inconsistent: Option<u32>,
    failing: Option<u32>,
    generator: u64,

    /// Number of active internal literals (`2 *` internal vars).
    lits: usize,
    /// Number of imported external variables.
    evars: usize,
    /// Arena end of the original (non-learned) klauses.
    end_original_ref: usize,

    queue: Queue,

    /// Allocated literal capacity (`2 *` var capacity).
    size: usize,
    /// Allocated external-variable capacity.
    esize: usize,

    vars: Vec<Kar>,
    links: Vec<Kink>,
    marks: Vec<u8>,
    values: Vec<i8>,
    failed: Vec<bool>,
    phases: Vec<u8>,
    /// `import[eidx] = iidx + 1` (0 = not imported).
    import: Vec<u32>,
    watches: Vec<Vec<Katch>>,

    analyzed: Vec<u32>,
    assumptions: Vec<u32>,
    core: Vec<u32>,
    export: Vec<u32>,
    klause: Vec<u32>,
    klauses: Vec<u32>,
    resolved: Vec<u32>,
    trail: Vec<u32>,
    /// Unit klause refs (their literal is `klause_lits(ref)[0]`).
    units: Vec<u32>,

    ticks_limit: u64,
    initialized: u64,

    pub(crate) stats: KittenStats,
}

/// Decision queue head/tail with the `search` resume point.
#[derive(Debug, Clone, Copy, Default)]
struct Queue {
    first: Option<u32>,
    last: Option<u32>,
    stamp: u64,
    search: Option<u32>,
}

/// kissat `kissat_next_random64`: LCG used for phase randomization and
/// shuffling. Ported exactly so phase policies match the reference.
#[inline]
fn next_random64(generator: &mut u64) -> u64 {
    *generator = generator
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *generator
}

/// kissat `kissat_pick_random`: uniform pick in `[l, r)`. Used by
/// [`Kitten::shuffle_clauses`] (itself part of the ported API surface;
/// exercised by the kitten unit tests).
#[allow(dead_code)]
#[inline]
fn pick_random(generator: &mut u64, l: u32, r: u32) -> u32 {
    debug_assert!(l <= r);
    if l == r {
        return l;
    }
    let delta = r - l;
    let tmp = (next_random64(generator) >> 32) as u32;
    let fraction = f64::from(tmp) / 4294967296.0;
    // `delta * fraction < delta` always, but clamp defensively so a
    // floating-point edge can never produce an out-of-range index.
    let scaled = ((delta as f64) * fraction) as u32;
    let scaled = if scaled >= delta { delta - 1 } else { scaled };
    l + scaled
}

impl Kitten {
    // The `#[allow(dead_code)]` markers below cover the parts of the
    // `kitten.h` API contract this port carries for parity that the
    // sweeper does not exercise (they are exercised by the unit tests:
    // `flip_phases`, `shuffle_clauses`, `unit`, `binary`, `failed`,
    // `no_ticks_limit`). Dropping them would silently shrink the port's
    // contract below the reference API.

    /// Fresh solver (`kitten_init`).
    pub(crate) fn new() -> Self {
        let mut kitten = Self {
            status: Status::Unsolved,
            antecedents: false,
            learned: false,
            level: 0,
            propagated: 0,
            unassigned: 0,
            inconsistent: None,
            failing: None,
            generator: 0,
            lits: 0,
            evars: 0,
            end_original_ref: 0,
            queue: Queue::default(),
            size: 0,
            esize: 0,
            vars: Vec::new(),
            links: Vec::new(),
            marks: Vec::new(),
            values: Vec::new(),
            failed: Vec::new(),
            phases: Vec::new(),
            import: Vec::new(),
            watches: Vec::new(),
            analyzed: Vec::new(),
            assumptions: Vec::new(),
            core: Vec::new(),
            export: Vec::new(),
            klause: Vec::new(),
            klauses: Vec::new(),
            resolved: Vec::new(),
            trail: Vec::new(),
            units: Vec::new(),
            ticks_limit: u64::MAX,
            initialized: 0,
            stats: KittenStats::default(),
        };
        kitten.initialize();
        kitten
    }

    fn initialize(&mut self) {
        self.queue = Queue::default();
        self.inconsistent = None;
        self.failing = None;
        self.ticks_limit = u64::MAX;
        self.generator = self.initialized;
        self.initialized += 1;
    }

    /// Reset trail, assignments and every klause, keeping capacities and
    /// the tick/stat counters (`kitten_clear`). The import/export map is
    /// reset; the decision queue is emptied. Antecedent tracking is
    /// disarmed and must be re-armed explicitly — same contract as the C.
    pub(crate) fn clear(&mut self) {
        self.assumptions.clear();
        self.core.clear();
        self.klause.clear();
        self.klauses.clear();
        self.trail.clear();
        self.units.clear();
        self.analyzed.clear();
        self.resolved.clear();
        for watch in self.watches.iter_mut() {
            watch.clear();
        }
        for &eidx in &self.export {
            self.import[eidx as usize] = 0;
        }
        self.export.clear();
        let vars = self.size / 2;
        for m in self.marks.iter_mut().take(vars) {
            *m = 0;
        }
        for p in self.phases.iter_mut().take(vars) {
            *p = 0;
        }
        for v in self.vars.iter_mut().take(vars) {
            *v = Kar::default();
        }
        for val in self.values.iter_mut().take(self.size) {
            *val = 0;
        }
        for f in self.failed.iter_mut().take(self.size) {
            *f = false;
        }
        // `clear_kitten` in the C zeroes everything from `status` up to
        // (excluding) `size`, then re-initializes.
        self.status = Status::Unsolved;
        self.antecedents = false;
        self.learned = false;
        self.level = 0;
        self.propagated = 0;
        self.unassigned = 0;
        self.inconsistent = None;
        self.failing = None;
        self.lits = 0;
        self.evars = 0;
        self.end_original_ref = 0;
        self.queue = Queue::default();
        self.initialize();
    }

    // ======== queue (stamped VMTF ring) ========

    fn update_search(&mut self, idx: u32) {
        if self.queue.search != Some(idx) {
            self.queue.search = Some(idx);
        }
    }

    fn enqueue(&mut self, idx: u32) {
        let last = self.queue.last;
        match last {
            None => self.queue.first = Some(idx),
            Some(l) => self.links[l as usize].next = idx,
        }
        self.links[idx as usize].prev = last.unwrap_or(INVALID);
        self.links[idx as usize].next = INVALID;
        self.queue.last = Some(idx);
        let stamp = self.queue.stamp;
        self.links[idx as usize].stamp = stamp;
        self.queue.stamp = stamp.wrapping_add(1);
    }

    fn dequeue(&mut self, idx: u32) {
        let l = self.links[idx as usize];
        let prev = l.prev;
        let next = l.next;
        if prev == INVALID {
            self.queue.first = if next == INVALID { None } else { Some(next) };
        } else {
            self.links[prev as usize].next = next;
        }
        if next == INVALID {
            self.queue.last = if prev == INVALID { None } else { Some(prev) };
        } else {
            self.links[next as usize].prev = prev;
        }
    }

    fn init_queue(&mut self, old_vars: usize, new_vars: usize) {
        for idx in old_vars..new_vars {
            self.unassigned = self.unassigned.saturating_add(1);
            self.enqueue(idx as u32);
        }
        if let Some(&last) = self.queue.last.as_ref() {
            self.update_search(last);
        }
    }

    // ======== sizing / import-export ========

    fn enlarge_internal(&mut self, new_lits: usize) {
        let old_lits = self.lits;
        debug_assert!(old_lits < new_lits);
        let old_size = self.size;
        let old_vars = old_lits / 2;
        let new_vars = new_lits / 2;
        if old_size < new_lits {
            let mut new_size = if old_size == 0 { 2 } else { old_size * 2 };
            while new_size <= new_lits {
                new_size *= 2;
            }
            self.marks.resize(new_size / 2, 0);
            self.phases.resize(new_size / 2, 0);
            self.vars.resize(new_size / 2, Kar::default());
            self.links.resize(
                new_size / 2,
                Kink {
                    next: INVALID,
                    prev: INVALID,
                    stamp: 0,
                },
            );
            self.values.resize(new_size, 0);
            self.failed.resize(new_size, false);
            self.watches.resize(new_size, Vec::new());
            self.size = new_size;
        }
        self.lits = new_lits;
        self.init_queue(old_vars, new_vars);
    }

    fn enlarge_external(&mut self, eidx: usize) {
        let old_size = self.esize;
        let new_evars = eidx + 1;
        if old_size <= eidx {
            let mut new_size = if old_size == 0 { 1 } else { old_size * 2 };
            while new_size <= eidx {
                new_size *= 2;
            }
            self.import.resize(new_size, 0);
            self.esize = new_size;
        }
        self.evars = new_evars;
    }

    fn import_literal(&mut self, elit: u32) -> u32 {
        let eidx = (elit >> 1) as usize;
        if eidx >= self.evars {
            self.enlarge_external(eidx);
        }
        let mut iidx = self.import[eidx];
        if iidx == 0 {
            iidx = self.export.len() as u32;
            self.export.push(eidx as u32);
            self.import[eidx] = iidx + 1;
        } else {
            iidx -= 1;
        }
        let ilit = 2 * iidx + (elit & 1);
        let new_lits = ((ilit | 1) + 1) as usize;
        if new_lits > self.lits {
            self.enlarge_internal(new_lits);
        }
        ilit
    }

    fn export_literal(&self, ilit: u32) -> u32 {
        let iidx = (ilit >> 1) as usize;
        match self.export.get(iidx) {
            Some(&eidx) => 2 * eidx + (ilit & 1),
            // Unreachable through the public surface: every internal
            // literal was produced by `import_literal`, which registers
            // the export entry. Fall back to the literal itself rather
            // than fabricate a mapping.
            None => ilit,
        }
    }

    // ======== klauses ========

    #[inline]
    fn klause_aux(&self, reference: u32) -> u32 {
        self.klauses[reference as usize]
    }

    #[inline]
    fn klause_size(&self, reference: u32) -> usize {
        self.klauses[(reference + 1) as usize] as usize
    }

    #[inline]
    fn klause_flags(&self, reference: u32) -> u32 {
        self.klauses[(reference + 2) as usize]
    }

    #[inline]
    fn klause_lits(&self, reference: u32) -> &[u32] {
        let start = (reference + 3) as usize;
        let size = self.klause_size(reference);
        &self.klauses[start..start + size]
    }

    #[inline]
    fn is_learned_klause(&self, reference: u32) -> bool {
        self.klause_flags(reference) & LEARNED_FLAG != 0
    }

    #[inline]
    fn is_core_klause(&self, reference: u32) -> bool {
        self.klause_flags(reference) & CORE_FLAG != 0
    }

    #[inline]
    fn set_core_klause(&mut self, reference: u32) {
        self.klauses[(reference + 2) as usize] |= CORE_FLAG;
    }

    #[inline]
    fn unset_core_klause(&mut self, reference: u32) {
        self.klauses[(reference + 2) as usize] &= !CORE_FLAG;
    }

    /// Antecedent refs of a learned klause (stored after its literals).
    fn klause_antecedents(&self, reference: u32) -> &[u32] {
        debug_assert!(self.is_learned_klause(reference));
        let start = (reference + 3) as usize;
        let size = self.klause_size(reference);
        let aux = self.klause_aux(reference) as usize;
        &self.klauses[start + size..start + size + aux]
    }

    fn new_reference(&mut self) -> u32 {
        self.stats.ticks += 1;
        self.klauses.len() as u32
    }

    fn connect_new_klause(&mut self, reference: u32) {
        let size = self.klause_size(reference);
        if size == 0 {
            if self.inconsistent.is_none() {
                self.inconsistent = Some(reference);
            }
        } else if size == 1 {
            self.units.push(reference);
        } else {
            let l0 = self.klause_lits(reference)[0];
            let l1 = self.klause_lits(reference)[1];
            let binary = size == 2;
            let blit = l0 ^ l1 ^ l0; // = l1
            let _ = blit;
            self.watch_klause(l0, reference, binary);
            self.watch_klause(l1, reference, binary);
        }
    }

    fn watch_klause(&mut self, lit: u32, reference: u32, binary: bool) {
        let lits = self.klause_lits(reference);
        let blit = lits[0] ^ lits[1] ^ lit;
        let katch = Katch {
            blit,
            reference,
            binary,
        };
        self.watches[lit as usize].push(katch);
    }

    fn new_original_klause(&mut self, id: u32) {
        let reference = self.new_reference();
        let size = self.klause.len() as u32;
        self.klauses.push(id);
        self.klauses.push(size);
        self.klauses.push(0);
        let klause = core::mem::take(&mut self.klause);
        self.klauses.extend_from_slice(&klause);
        self.klause = klause;
        self.connect_new_klause(reference);
        self.end_original_ref = self.klauses.len();
    }

    fn new_learned_klause(&mut self) -> u32 {
        let reference = self.new_reference();
        let size = self.klause.len() as u32;
        let aux = if self.antecedents {
            self.resolved.len() as u32
        } else {
            0
        };
        self.klauses.push(aux);
        self.klauses.push(size);
        self.klauses.push(LEARNED_FLAG);
        let klause = core::mem::take(&mut self.klause);
        self.klauses.extend_from_slice(&klause);
        self.klause = klause;
        if aux > 0 {
            let resolved = core::mem::take(&mut self.resolved);
            self.klauses.extend_from_slice(&resolved);
            self.resolved = resolved;
        }
        self.connect_new_klause(reference);
        self.learned = true;
        reference
    }

    // ======== phases / shuffling / limits ========

    /// Randomize every phase from the generator (`kitten_randomize_phases`).
    pub(crate) fn randomize_phases(&mut self) {
        let vars = self.size / 2;
        let mut random = next_random64(&mut self.generator);
        for i in 0..vars {
            if i % 64 == 0 && i > 0 {
                random = next_random64(&mut self.generator);
            }
            self.phases[i] = ((random >> (i % 64)) & 1) as u8;
        }
    }

    /// Flip every phase (`kitten_flip_phases`).
    #[allow(dead_code)]
    pub(crate) fn flip_phases(&mut self) {
        for p in self.phases.iter_mut().take(self.size / 2) {
            *p ^= 1;
        }
    }

    /// Remove the tick limit (`kitten_no_ticks_limit`).
    #[allow(dead_code)]
    pub(crate) fn no_ticks_limit(&mut self) {
        self.ticks_limit = u64::MAX;
    }

    /// Set the tick limit as a delta over the live counter
    /// (`kitten_set_ticks_limit`).
    pub(crate) fn set_ticks_limit_delta(&mut self, delta: u64) {
        self.ticks_limit = self.stats.ticks.saturating_add(delta);
    }

    /// Shuffle decision order, watch lists and units
    /// (`kitten_shuffle_clauses`). Only valid while unsolved.
    #[allow(dead_code)]
    pub(crate) fn shuffle_clauses(&mut self) {
        debug_assert!(self.status == Status::Unsolved);
        let vars = (self.lits / 2) as u32;
        for _ in 0..vars {
            let idx = pick_random(&mut self.generator, 0, vars);
            self.dequeue(idx);
            self.enqueue(idx);
        }
        if let Some(&last) = self.queue.last.as_ref() {
            self.update_search(last);
        }
        for lit in 0..self.lits {
            let n = self.watches[lit].len();
            for i in 0..n {
                let j = pick_random(&mut self.generator, 0, (i + 1) as u32) as usize;
                if j != i {
                    self.watches[lit].swap(i, j);
                }
            }
        }
        let n = self.units.len();
        for i in 0..n {
            let j = pick_random(&mut self.generator, 0, (i + 1) as u32) as usize;
            if j != i {
                self.units.swap(i, j);
            }
        }
    }

    // ======== problem construction ========

    /// Register an assumption literal (external encoding).
    pub(crate) fn assume(&mut self, elit: u32) {
        debug_assert!(external_literal_sane(elit));
        if !external_literal_sane(elit) {
            return;
        }
        if self.status != Status::Unsolved {
            self.reset_incremental();
        }
        let ilit = self.import_literal(elit);
        self.assumptions.push(ilit);
    }

    /// Add an original klause, skipping `except` and tagging `id`
    /// (`kitten_clause_with_id_and_exception`). `INVALID` id/except mean
    /// "none".
    pub(crate) fn clause_with_id_and_exception(&mut self, id: u32, elits: &[u32], except: u32) {
        if self.status != Status::Unsolved {
            self.reset_incremental();
        }
        debug_assert!(self.klause.is_empty());
        for &elit in elits {
            if elit == except {
                continue;
            }
            debug_assert!(external_literal_sane(elit));
            if !external_literal_sane(elit) {
                // A sentinel/garbage code would resize the import table
                // by billions of entries; skip the literal (weakening the
                // clause, never strengthening it — sound).
                continue;
            }
            let ilit = self.import_literal(elit);
            let iidx = (ilit >> 1) as usize;
            if self.marks[iidx] != 0 {
                // Duplicate variable in one clause: the C aborts. The
                // sweeper never produces duplicates (its clause copies
                // come from watched clauses, which are duplicate-free);
                // keep the first occurrence — a duplicate never changes a
                // clause's meaning.
                continue;
            }
            self.marks[iidx] = 1;
            self.klause.push(ilit);
        }
        for &ilit in &self.klause {
            self.marks[(ilit >> 1) as usize] = 0;
        }
        self.new_original_klause(id);
        self.klause.clear();
    }

    /// Add an original klause (`kitten_clause`).
    pub(crate) fn clause(&mut self, elits: &[u32]) {
        self.clause_with_id_and_exception(INVALID, elits, INVALID);
    }

    /// Add a unit (`kitten_unit`).
    #[allow(dead_code)]
    pub(crate) fn unit(&mut self, lit: u32) {
        self.clause(&[lit]);
    }

    /// Add a binary (`kitten_binary`).
    #[allow(dead_code)]
    pub(crate) fn binary(&mut self, a: u32, b: u32) {
        self.clause(&[a, b]);
    }

    // ======== assignment / propagation ========

    fn move_to_front(&mut self, idx: u32) {
        if Some(idx) == self.queue.last {
            return;
        }
        self.dequeue(idx);
        self.enqueue(idx);
    }

    fn assign(&mut self, lit: u32, reason: u32) {
        debug_assert!(self.values[lit as usize] == 0);
        self.values[lit as usize] = 1;
        self.values[(lit ^ 1) as usize] = -1;
        let idx = (lit >> 1) as usize;
        self.phases[idx] = (lit & 1) as u8;
        self.trail.push(lit);
        let mut reason = reason;
        if self.level == 0 {
            debug_assert!(reason != INVALID);
            let size = self.klause_size(reason);
            if size > 1 {
                // Wrap the level-0 propagation into a learned unit klause
                // carrying the antecedents, so core extraction can walk
                // through it (kitten.c `assign`).
                if self.antecedents {
                    self.resolved.push(reason);
                    let lits: Vec<u32> = self.klause_lits(reason).to_vec();
                    for other in lits {
                        if other != lit {
                            let other_idx = (other >> 1) as usize;
                            let other_ref = self.vars[other_idx].reason;
                            debug_assert!(other_ref != INVALID);
                            self.resolved.push(other_ref);
                        }
                    }
                }
                self.klause.push(lit);
                let learned_ref = self.new_learned_klause();
                self.resolved.clear();
                self.klause.clear();
                reason = learned_ref;
            }
        }
        self.vars[idx] = Kar {
            level: self.level,
            reason,
        };
        debug_assert!(self.unassigned > 0);
        self.unassigned -= 1;
    }

    /// Watch-list surgery for one propagated literal; returns the
    /// conflicting klause ref if any (`propagate_literal`).
    fn propagate_literal(&mut self, lit: u32) -> Option<u32> {
        debug_assert!(self.values[lit as usize] > 0);
        let not_lit = lit ^ 1;
        let mut ticks = (self.watches[not_lit as usize].len() / 16) as u64 + 1;
        let mut conflict = None;
        let mut i = 0usize;
        while i < self.watches[not_lit as usize].len() {
            let katch = self.watches[not_lit as usize][i];
            i += 1;
            let reference = katch.reference;
            let blit_value = self.values[katch.blit as usize];
            if blit_value > 0 {
                continue;
            }
            if katch.binary {
                if blit_value < 0 {
                    self.stats.conflicts += 1;
                    conflict = Some(reference);
                    break;
                }
                self.assign(katch.blit, reference);
                continue;
            }
            // Large klause: try to move the watch off `not_lit`.
            let start = (reference + 3) as usize;
            let size = self.klause_size(reference);
            let lits0 = self.klauses[start];
            let lits1 = self.klauses[start + 1];
            let other = lits0 ^ lits1 ^ not_lit;
            let other_value = self.values[other as usize];
            ticks += 1;
            if other_value > 0 {
                // Keep watching, refresh the blocking literal.
                self.watches[not_lit as usize][i - 1].blit = other;
                continue;
            }
            let mut replacement = INVALID;
            let mut replacement_value = -1;
            let mut r_pos = start + size; // one past the scan range
            for r in (start + 2)..(start + size) {
                replacement = self.klauses[r];
                replacement_value = self.values[replacement as usize];
                r_pos = r;
                if replacement_value >= 0 {
                    break;
                }
            }
            if replacement_value >= 0 {
                debug_assert!(replacement != INVALID);
                // Swap `not_lit` out of the watch slots; move the watch
                // to `replacement` (the C mutates the klause body
                // in place and re-watches).
                self.klauses[start] = other;
                self.klauses[start + 1] = replacement;
                self.klauses[r_pos] = not_lit;
                self.watch_klause(replacement, reference, false);
                // Drop the just-copied watch from this list (the C's
                // `q--`).
                self.watches[not_lit as usize].remove(i - 1);
                i -= 1;
            } else if other_value < 0 {
                self.stats.conflicts += 1;
                conflict = Some(reference);
                break;
            } else {
                self.assign(other, reference);
            }
        }
        self.stats.ticks += ticks;
        conflict
    }

    /// Propagate the trail; returns a conflicting klause ref (`propagate`).
    fn propagate(&mut self) -> Option<u32> {
        debug_assert!(self.inconsistent.is_none());
        let mut conflict = None;
        while conflict.is_none() && self.propagated < self.trail.len() {
            let lit = self.trail[self.propagated];
            conflict = self.propagate_literal(lit);
            self.propagated += 1;
            self.stats.propagations = self.stats.propagations.saturating_add(1);
        }
        conflict
    }

    // ======== backtracking ========

    fn unassign(&mut self, lit: u32) {
        let not_lit = lit ^ 1;
        self.values[lit as usize] = 0;
        self.values[not_lit as usize] = 0;
        let idx = lit >> 1;
        self.unassigned += 1;
        if let Some(search) = self.queue.search
            && self.links[idx as usize].stamp > self.links[search as usize].stamp
        {
            self.update_search(idx);
        }
    }

    fn backtrack(&mut self, jump: u32) {
        debug_assert!(jump < self.level);
        while let Some(&lit) = self.trail.last() {
            let level = self.vars[(lit >> 1) as usize].level;
            if level == jump {
                break;
            }
            self.trail.pop();
            self.unassign(lit);
        }
        self.propagated = self.trail.len();
        self.level = jump;
    }

    fn completely_backtrack_to_root_level(&mut self) {
        let lits: Vec<u32> = self.trail.drain(..).collect();
        for lit in lits {
            self.unassign(lit);
        }
        self.propagated = 0;
        self.level = 0;
    }

    fn reset_incremental(&mut self) {
        self.completely_backtrack_to_root_level();
        if !self.assumptions.is_empty() {
            self.reset_assumptions();
        }
        if self.status == Status::InconsistentCore {
            self.reset_core();
        }
        self.status = Status::Unsolved;
    }

    fn reset_core(&mut self) {
        let mut reference = 0usize;
        while reference < self.klauses.len() {
            let r = reference as u32;
            if self.is_core_klause(r) {
                self.unset_core_klause(r);
            }
            let size = self.klause_size(r);
            let aux = if self.antecedents && self.is_learned_klause(r) {
                self.klause_aux(r) as usize
            } else {
                0
            };
            reference += 3 + size + aux;
        }
        self.core.clear();
    }

    fn reset_assumptions(&mut self) {
        while let Some(assumption) = self.assumptions.pop() {
            self.failed[assumption as usize] = false;
        }
        self.failing = None;
    }

    // ======== analysis ========

    fn bump(&mut self) {
        let analyzed = core::mem::take(&mut self.analyzed);
        for idx in analyzed.iter().copied() {
            self.marks[idx as usize] = 0;
            self.move_to_front(idx);
        }
        self.analyzed = analyzed;
        self.analyzed.clear();
    }

    /// First-UIP analysis + learning (`analyze`). Iterative by
    /// construction (trail walk like the C).
    fn analyze(&mut self, conflict: u32) {
        debug_assert!(self.level > 0);
        debug_assert!(self.inconsistent.is_none());
        self.klause.push(INVALID); // placeholder for the negated UIP
        let mut reason = conflict;
        let level = self.level;
        let mut open: u32 = 0;
        let mut jump: u32 = 0;
        let mut size: u32 = 1;
        let mut p = self.trail.len();
        // The loop expression breaks with the final UIP, so the binding
        // needs no (never-read) initializer.
        let uip = loop {
            debug_assert!(reason != INVALID);
            self.resolved.push(reason);
            let lits: Vec<u32> = self.klause_lits(reason).to_vec();
            for lit in lits {
                let idx = lit >> 1;
                if self.marks[idx as usize] != 0 {
                    continue;
                }
                debug_assert!(self.values[lit as usize] < 0);
                self.marks[idx as usize] = 1;
                self.analyzed.push(idx);
                let v_level = self.vars[idx as usize].level;
                if v_level < level {
                    let mut lit = lit;
                    if v_level > jump {
                        jump = v_level;
                        if size > 1 {
                            // Keep the highest-level literal at position 1
                            // (the watch slot after backtracking); the
                            // displaced literal goes to the end.
                            core::mem::swap(&mut self.klause[1], &mut lit);
                        }
                    }
                    self.klause.push(lit);
                    size += 1;
                } else {
                    open += 1;
                }
            }
            let uip = loop {
                debug_assert!(p > 0);
                p -= 1;
                let candidate = self.trail[p];
                if self.marks[(candidate >> 1) as usize] != 0 {
                    break candidate;
                }
            };
            debug_assert!(open > 0);
            open -= 1;
            if open == 0 {
                break uip;
            }
            reason = self.vars[(uip >> 1) as usize].reason;
        };
        let not_uip = uip ^ 1;
        self.klause[0] = not_uip;
        self.bump();
        let learned_ref = self.new_learned_klause();
        self.resolved.clear();
        self.klause.clear();
        self.backtrack(jump);
        self.assign(not_uip, learned_ref);
    }

    /// Failed-assumption analysis producing the final core clause
    /// (`failing`). Iterative walk exactly like the C.
    fn failing(&mut self) {
        debug_assert!(self.inconsistent.is_none());
        debug_assert!(!self.assumptions.is_empty());
        let mut failed_clashing = INVALID;
        let mut first_failed = INVALID;
        let mut failed_unit = INVALID;
        for &lit in &self.assumptions {
            if self.values[lit as usize] >= 0 {
                continue;
            }
            if first_failed == INVALID {
                first_failed = lit;
            }
            let failed_idx = (lit >> 1) as usize;
            let failed_var = self.vars[failed_idx];
            if failed_var.level == 0 {
                failed_unit = lit;
                break;
            }
            if failed_clashing == INVALID && failed_var.reason == INVALID {
                failed_clashing = lit;
            }
        }
        let failed = if failed_unit != INVALID {
            failed_unit
        } else if failed_clashing != INVALID {
            failed_clashing
        } else {
            first_failed
        };
        debug_assert!(failed != INVALID);
        let failed_idx = (failed >> 1) as usize;
        let failed_reason = self.vars[failed_idx].reason;
        self.failed[failed as usize] = true;

        if failed_unit != INVALID {
            debug_assert!(self.klause_size(failed_reason) == 1);
            self.failing = Some(failed_reason);
            return;
        }

        let not_failed = failed ^ 1;
        if failed_clashing != INVALID {
            self.failed[not_failed as usize] = true;
            debug_assert!(self.failing.is_none());
            return;
        }

        self.marks[failed_idx] = 1;
        self.analyzed.push(failed_idx as u32);
        self.klause.push(not_failed);

        let mut work: Vec<u32> = Vec::new();
        let mut open: u32 = 1;
        let mut p = self.trail.len();
        loop {
            if open == 0 {
                break;
            }
            open -= 1;
            let uip = loop {
                debug_assert!(p > 0);
                p -= 1;
                let candidate = self.trail[p];
                if self.marks[(candidate >> 1) as usize] != 0 {
                    break candidate;
                }
            };
            let idx = uip >> 1;
            let reason = self.vars[idx as usize].reason;
            if reason == INVALID {
                let mut lit = 2 * idx;
                if self.values[lit as usize] < 0 {
                    lit ^= 1;
                }
                debug_assert!(!self.failed[lit as usize]);
                self.failed[lit as usize] = true;
                self.klause.push(lit ^ 1);
            } else {
                self.resolved.push(reason);
                let lits: Vec<u32> = self.klause_lits(reason).to_vec();
                for other in lits {
                    let other_idx = other >> 1;
                    if self.marks[other_idx as usize] != 0 {
                        continue;
                    }
                    debug_assert!(other_idx != idx);
                    self.marks[other_idx as usize] = 1;
                    debug_assert!(self.values[other as usize] != 0);
                    if self.vars[other_idx as usize].level > 0 {
                        open += 1;
                    } else {
                        work.push(other_idx);
                    }
                    self.analyzed.push(other_idx);
                }
            }
        }
        let mut next = 0;
        while next < work.len() {
            let idx = work[next];
            next += 1;
            let reason = self.vars[idx as usize].reason;
            if reason == INVALID {
                let mut lit = 2 * idx;
                if self.values[lit as usize] < 0 {
                    lit ^= 1;
                }
                debug_assert!(!self.failed[lit as usize]);
                self.failed[lit as usize] = true;
                self.klause.push(lit ^ 1);
            } else {
                self.resolved.push(reason);
            }
        }

        for &idx in &self.analyzed {
            self.marks[idx as usize] = 0;
        }
        self.analyzed.clear();

        let resolved = self.resolved.len();
        debug_assert!(resolved > 0);
        if resolved == 1 {
            self.failing = Some(self.resolved[0]);
        } else {
            self.failing = Some(self.new_learned_klause());
        }
        self.resolved.clear();
        self.klause.clear();
    }

    // ======== decisions / solving ========

    fn flush_trail(&mut self) {
        debug_assert!(self.level == 0);
        self.propagated = 0;
        self.trail.clear();
    }

    fn decide(&mut self) -> i32 {
        if self.level == 0 && !self.trail.is_empty() {
            self.flush_trail();
        }
        let mut decision = INVALID;
        let assumptions = self.assumptions.len() as u32;
        while self.level < assumptions {
            let assumption = self.assumptions[self.level as usize];
            let value = self.values[assumption as usize];
            if value < 0 {
                self.failing();
                return 20;
            } else if value > 0 {
                self.level += 1;
            } else {
                decision = assumption;
                break;
            }
        }

        if self.unassigned == 0 {
            return 10;
        }

        if self.stats.ticks >= self.ticks_limit {
            return -1;
        }

        if decision == INVALID {
            let mut idx = match self.queue.search {
                Some(idx) => idx,
                None => {
                    // Queue empty with unassigned vars left: unreachable
                    // (every imported var is enqueued on import). Abort
                    // as Unknown rather than fabricate an answer.
                    return -1;
                }
            };
            loop {
                if idx == INVALID {
                    return -1;
                }
                if self.values[(idx * 2) as usize] == 0 {
                    break;
                }
                idx = self.links[idx as usize].prev;
            }
            self.update_search(idx);
            let phase = self.phases[idx as usize];
            decision = 2 * idx + phase as u32;
        }
        self.stats.decisions += 1;
        self.level += 1;
        self.assign(decision, INVALID);
        0
    }

    /// Iteratively resolve the root-level conflict into the inconsistent
    /// klause, tracking antecedents (`inconsistent`).
    fn register_inconsistent(&mut self, mut reference: u32) {
        debug_assert!(self.inconsistent.is_none());

        if !self.antecedents {
            self.inconsistent = Some(reference);
            return;
        }
        debug_assert!(self.analyzed.is_empty());
        debug_assert!(self.resolved.is_empty());
        let mut next = 0usize;
        loop {
            debug_assert!(reference != INVALID);
            self.resolved.push(reference);
            let lits: Vec<u32> = self.klause_lits(reference).to_vec();
            for lit in lits {
                let idx = lit >> 1;
                debug_assert!(self.vars[idx as usize].level == 0);
                if self.marks[idx as usize] != 0 {
                    continue;
                }
                debug_assert!(self.values[lit as usize] < 0);
                self.marks[idx as usize] = 1;
                self.analyzed.push(idx);
            }
            if next == self.analyzed.len() {
                break;
            }
            let idx = self.analyzed[next];
            next += 1;
            let v = self.vars[idx as usize];
            debug_assert!(v.level == 0);
            reference = v.reason;
            if reference == INVALID {
                break;
            }
        }
        debug_assert!(self.klause.is_empty());
        let reference = self.new_learned_klause();
        self.inconsistent = Some(reference);
        for &idx in &self.analyzed {
            self.marks[idx as usize] = 0;
        }
        self.analyzed.clear();
        self.resolved.clear();
    }

    fn propagate_units(&mut self) -> i32 {
        if self.inconsistent.is_some() {
            return 20;
        }
        if self.units.is_empty() {
            return 0;
        }
        let mut next = 0;
        while next < self.units.len() {
            let reference = self.units[next];
            next += 1;
            debug_assert!(self.klause_size(reference) == 1);
            let unit = self.klause_lits(reference)[0];
            let value = self.values[unit as usize];
            if value > 0 {
                continue;
            }
            if value < 0 {
                self.register_inconsistent(reference);
                return 20;
            }
            self.assign(unit, reference);
        }
        match self.propagate() {
            None => 0,
            Some(conflict) => {
                self.register_inconsistent(conflict);
                20
            }
        }
    }

    /// Solve under the current assumptions and tick limit
    /// (`kitten_solve`): 10 → [`KittenResult::Satisfied`],
    /// 20 → [`KittenResult::Inconsistent`], 0 →
    /// [`KittenResult::Unknown`].
    pub(crate) fn solve(&mut self) -> KittenResult {
        if self.status != Status::Unsolved {
            self.reset_incremental();
        } else {
            self.completely_backtrack_to_root_level();
        }
        self.stats.solved += 1;

        let mut res = self.propagate_units();
        while res == 0 {
            match self.propagate() {
                Some(conflict) => {
                    if self.level > 0 {
                        self.analyze(conflict);
                    } else {
                        self.register_inconsistent(conflict);
                        res = 20;
                    }
                }
                None => res = self.decide(),
            }
        }

        let result = if res < 0 {
            KittenResult::Unknown
        } else if res == 10 {
            KittenResult::Satisfied
        } else {
            KittenResult::Inconsistent
        };

        if result == KittenResult::Unknown && !self.assumptions.is_empty() {
            self.reset_assumptions();
        }

        self.status = match result {
            KittenResult::Satisfied => Status::Satisfied,
            KittenResult::Inconsistent => Status::Inconsistent,
            KittenResult::Unknown => Status::Unsolved,
        };
        match result {
            KittenResult::Satisfied => self.stats.sat += 1,
            KittenResult::Inconsistent => self.stats.unsat += 1,
            KittenResult::Unknown => self.stats.unknown += 1,
        }
        result
    }

    /// Current status as the C code (0/10/20/21).
    pub(crate) fn status(&self) -> u32 {
        match self.status {
            Status::Unsolved => 0,
            Status::Satisfied => 10,
            Status::Inconsistent => 20,
            Status::InconsistentCore => 21,
        }
    }

    /// Value of an external literal in the last SAT model (`kitten_value`).
    pub(crate) fn value(&self, elit: u32) -> i8 {
        debug_assert!(self.status == Status::Satisfied);
        let eidx = (elit >> 1) as usize;
        if eidx >= self.evars {
            return 0;
        }
        let iidx = self.import[eidx];
        if iidx == 0 {
            return 0;
        }
        let ilit = 2 * (iidx - 1) + (elit & 1);
        self.values[ilit as usize]
    }

    /// Root-level (fixed) value of an external literal (`kitten_fixed`).
    pub(crate) fn fixed(&self, elit: u32) -> i8 {
        let eidx = (elit >> 1) as usize;
        if eidx >= self.evars {
            return 0;
        }
        let iidx = self.import[eidx];
        if iidx == 0 {
            return 0;
        }
        let ilit = 2 * (iidx - 1) + (elit & 1);
        let res = self.values[ilit as usize];
        if res == 0 {
            return 0;
        }
        if self.vars[(ilit >> 1) as usize].level != 0 {
            return 0;
        }
        res
    }

    /// Whether the external literal is a failed assumption (status 20).
    #[allow(dead_code)]
    pub(crate) fn failed(&self, elit: u32) -> bool {
        debug_assert!(self.status == Status::Inconsistent);
        let eidx = (elit >> 1) as usize;
        if eidx >= self.evars {
            return false;
        }
        let iidx = self.import[eidx];
        if iidx == 0 {
            return false;
        }
        let ilit = 2 * (iidx - 1) + (elit & 1);
        self.failed[ilit as usize]
    }

    /// Arm antecedent tracking (`kitten_track_antecedents`); must run
    /// before any learned klause exists.
    pub(crate) fn track_antecedents(&mut self) {
        debug_assert!(self.status == Status::Unsolved);
        debug_assert!(!self.learned);
        self.antecedents = true;
    }

    // ======== clausal core ========

    /// Compute the clausal core of the last inconsistent solve
    /// (`kitten_compute_clausal_core`). Returns the number of *original*
    /// core klauses and stores the learned count in `learned_ptr`.
    /// Sets status 21.
    pub(crate) fn compute_clausal_core(&mut self, learned_ptr: &mut u64) -> u32 {
        debug_assert!(self.status == Status::Inconsistent);
        debug_assert!(self.antecedents);
        debug_assert!(self.resolved.is_empty());
        debug_assert!(self.core.is_empty());

        let mut original = 0u32;
        let mut learned = 0u64;

        let reason_ref = match self.inconsistent.or(self.failing) {
            Some(r) => r,
            None => {
                // Assumptions mutually inconsistent without a reason:
                // nothing to extract.
                self.status = Status::InconsistentCore;
                *learned_ptr = learned;
                return original;
            }
        };

        let mut stack: Vec<u32> = Vec::new();
        stack.push(reason_ref);
        while let Some(c_ref) = stack.pop() {
            if c_ref == INVALID {
                let Some(d_ref) = stack.pop() else {
                    break;
                };
                self.core.push(d_ref);
                self.set_core_klause(d_ref);
                if self.is_learned_klause(d_ref) {
                    learned += 1;
                } else {
                    original += 1;
                }
            } else {
                if self.is_core_klause(c_ref) {
                    continue;
                }
                stack.push(c_ref);
                stack.push(INVALID);
                if !self.is_learned_klause(c_ref) {
                    continue;
                }
                for &d_ref in self.klause_antecedents(c_ref) {
                    if !self.is_core_klause(d_ref) {
                        stack.push(d_ref);
                    }
                }
            }
        }

        *learned_ptr = learned;
        self.status = Status::InconsistentCore;
        original
    }

    /// Traverse the core clauses in external-literal form
    /// (`kitten_traverse_core_clauses`): calls `traverse(learned, elits)`
    /// for each core klause in extraction order.
    pub(crate) fn traverse_core_clauses(&self, mut traverse: impl FnMut(bool, &[u32])) {
        debug_assert!(self.status == Status::InconsistentCore);
        let mut eclause: Vec<u32> = Vec::new();
        for &c_ref in &self.core {
            debug_assert!(self.is_core_klause(c_ref));
            let learned = self.is_learned_klause(c_ref);
            eclause.clear();
            for &ilit in self.klause_lits(c_ref) {
                eclause.push(self.export_literal(ilit));
            }
            traverse(learned, &eclause);
        }
    }

    // ======== flipping ========

    /// Try to flip a satisfied literal's value in place, moving watches
    /// off it (`flip_literal` / `kitten_flip_literal`). Only valid while
    /// satisfied (status 10).
    pub(crate) fn flip_literal(&mut self, elit: u32) -> bool {
        debug_assert!(self.status == Status::Satisfied);
        let eidx = (elit >> 1) as usize;
        if eidx >= self.evars {
            return false;
        }
        let iidx = self.import[eidx];
        if iidx == 0 {
            return false;
        }
        let ilit = 2 * (iidx - 1) + (elit & 1);
        if self.fixed(elit) != 0 {
            return false;
        }
        self.flip_internal(ilit)
    }

    fn flip_internal(&mut self, mut lit: u32) -> bool {
        self.stats.flips += 1;
        if self.vars[(lit >> 1) as usize].level == 0 {
            return false;
        }
        if self.values[lit as usize] < 0 {
            lit ^= 1;
        }
        debug_assert!(self.values[lit as usize] > 0);
        let not_lit = lit ^ 1;
        let mut ticks = (self.watches[lit as usize].len() / 16) as u64 + 1;
        let mut res = true;
        let mut i = 0usize;
        while i < self.watches[lit as usize].len() {
            let katch = self.watches[lit as usize][i];
            i += 1;
            let blit_value = self.values[katch.blit as usize];
            if blit_value > 0 {
                continue;
            }
            let reference = katch.reference;
            let start = (reference + 3) as usize;
            let size = self.klause_size(reference);
            let lits0 = self.klauses[start];
            let lits1 = self.klauses[start + 1];
            let other = lits0 ^ lits1 ^ lit;
            let other_value = self.values[other as usize];
            ticks += 1;
            if other_value > 0 {
                continue;
            }
            let mut replacement = INVALID;
            let mut replacement_value = -1;
            let mut r_pos = start + size;
            for r in (start + 2)..(start + size) {
                replacement = self.klauses[r];
                debug_assert!(replacement != lit);
                replacement_value = self.values[replacement as usize];
                r_pos = r;
                if replacement_value > 0 {
                    break;
                }
            }
            if replacement_value > 0 {
                debug_assert!(replacement != INVALID);
                self.klauses[start] = other;
                self.klauses[start + 1] = replacement;
                self.klauses[r_pos] = lit;
                self.watch_klause(replacement, reference, false);
                self.watches[lit as usize].remove(i - 1);
                i -= 1;
            } else {
                debug_assert!(replacement_value < 0);
                res = false;
                break;
            }
        }
        self.stats.ticks += ticks;
        if res {
            self.values[lit as usize] = -1;
            self.values[not_lit as usize] = 1;
            self.stats.flipped += 1;
        }
        res
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// External literal helper: DIMACS-style signed var → kitten code.
    fn elit(lit: i32) -> u32 {
        let var = lit.unsigned_abs() - 1;
        2 * var + u32::from(lit < 0)
    }

    #[test]
    fn kitten_solves_sat_and_unsat() {
        let mut k = Kitten::new();
        k.track_antecedents();
        // (1 ∨ 2) ∧ (¬1 ∨ 2) ∧ (¬2)
        k.clause(&[elit(1), elit(2)]);
        k.clause(&[elit(-1), elit(2)]);
        k.unit(elit(-2));
        assert_eq!(k.solve(), KittenResult::Inconsistent);
        // Values/flip are invalid now; a fresh SAT check after clear.
        k.clear();
        k.track_antecedents();
        k.clause(&[elit(1), elit(2)]);
        assert_eq!(k.solve(), KittenResult::Satisfied);
        let v1 = k.value(elit(1));
        let v2 = k.value(elit(2));
        assert!(v1 > 0 || v2 > 0, "at least one of x1/x2 true");
    }

    #[test]
    fn kitten_unit_and_binary_apis() {
        let mut k = Kitten::new();
        k.unit(elit(1));
        k.binary(elit(2), elit(3));
        assert_eq!(k.solve(), KittenResult::Satisfied);
        assert_eq!(k.value(elit(1)), 1);
        assert_eq!(k.fixed(elit(1)), 1);
    }

    #[test]
    fn kitten_assumptions_and_failed() {
        let mut k = Kitten::new();
        // x1 ∧ (¬1 ∨ ¬2): assuming 1 and 2 together is unsat.
        k.unit(elit(1));
        k.clause(&[elit(-1), elit(-2)]);
        k.assume(elit(2));
        assert_eq!(k.solve(), KittenResult::Inconsistent);
        // Status 20: the failed assumption is visible.
        assert!(k.failed(elit(2)));
        // Re-solve without assumptions.
        assert_eq!(k.solve(), KittenResult::Satisfied);
        assert_eq!(k.value(elit(1)), 1);
    }

    #[test]
    fn kitten_clausal_core_of_unsat() {
        let mut k = Kitten::new();
        k.track_antecedents();
        // A tiny unsat formula needing learning:
        // (1∨2) (1∨¬2) (¬1∨2) (¬1∨¬2)
        k.clause(&[elit(1), elit(2)]);
        k.clause(&[elit(1), elit(-2)]);
        k.clause(&[elit(-1), elit(2)]);
        k.clause(&[elit(-1), elit(-2)]);
        assert_eq!(k.solve(), KittenResult::Inconsistent);
        let mut learned = 0u64;
        let original = k.compute_clausal_core(&mut learned);
        assert_eq!(original, 4, "all four originals are in the core");
        let mut clauses = 0usize;
        let mut saw_empty = false;
        k.traverse_core_clauses(|_learned, lits| {
            if lits.is_empty() {
                // The final learned empty clause closing the refutation.
                saw_empty = true;
            }
            clauses += 1;
        });
        assert!(saw_empty, "the core terminates in the empty clause");
        assert_eq!(clauses, 4 + learned as usize);
    }

    #[test]
    fn kitten_flip_literal_in_sat_model() {
        let mut k = Kitten::new();
        // (1 ∨ 2): a model satisfies one of them; flipping a true
        // non-fixed literal must keep the model valid or fail safely.
        k.clause(&[elit(1), elit(2)]);
        assert_eq!(k.solve(), KittenResult::Satisfied);
        let flipped_ok = k.flip_literal(elit(1)) || k.flip_literal(elit(-1));
        // Root-level assigned literals cannot flip; here nothing is
        // fixed, so one polarity flips.
        assert!(flipped_ok);
        // The model still satisfies the clause.
        let v1 = k.value(elit(1));
        let v2 = k.value(elit(2));
        assert!(v1 > 0 || v2 > 0);
    }

    #[test]
    fn kitten_phase_and_shuffle_control() {
        let mut k = Kitten::new();
        for v in 1..=20 {
            k.binary(elit(v), elit(v + 1));
        }
        k.randomize_phases();
        k.flip_phases();
        k.shuffle_clauses();
        assert_eq!(k.solve(), KittenResult::Satisfied);
    }

    #[test]
    fn kitten_tick_budget_returns_unknown() {
        let mut k = Kitten::new();
        // A satisfiable formula that needs decisions: free binary
        // implications that never conflict.
        for i in 1..=30u32 {
            let a = 2 * i;
            let b = 2 * (i + 1);
            k.clause(&[a, b]);
            k.clause(&[a ^ 1, b ^ 1]);
        }
        // Budget of 0 ticks: any decision aborts as Unknown.
        k.set_ticks_limit_delta(0);
        assert_eq!(k.solve(), KittenResult::Unknown);
        // Unlimited budget solves it.
        k.no_ticks_limit();
        assert_eq!(k.solve(), KittenResult::Satisfied);
    }

    #[test]
    fn kitten_clear_resets_problem() {
        let mut k = Kitten::new();
        k.unit(elit(1));
        assert_eq!(k.solve(), KittenResult::Satisfied);
        k.clear();
        k.track_antecedents();
        // Fresh (empty) formula: satisfied immediately.
        assert_eq!(k.solve(), KittenResult::Satisfied);
    }

    #[test]
    fn kitten_id_and_exception_clause_form() {
        let mut k = Kitten::new();
        k.track_antecedents();
        // The id+exception form drops the excepted literal and tags the
        // clause id: encode (1 ∨ 2 ∨ 3) minus 2 with id 42.
        k.clause_with_id_and_exception(42, &[elit(1), elit(2), elit(3)], elit(2));
        k.unit(elit(-1));
        k.unit(elit(-3));
        assert_eq!(k.solve(), KittenResult::Inconsistent);
        let mut learned = 0u64;
        let original = k.compute_clausal_core(&mut learned);
        assert_eq!(original, 3);
    }
}

#[cfg(test)]
mod flip_chain_tests {
    use super::*;

    fn elit(lit: i32) -> u32 {
        let var = lit.unsigned_abs() - 1;
        2 * var + u32::from(lit < 0)
    }

    /// On a uniform-true equivalence fragment, flipping any member must
    /// FAIL (each member is the sole satisfier of its guard clause) —
    /// this is what forces real equivalence tests instead of flips.
    #[test]
    fn flip_fails_on_equivalence_witness() {
        let mut k = Kitten::new();
        // x1 ≡ x2 ≡ x3: (¬1∨2)(1∨¬2)(¬2∨3)(2∨¬3)
        k.clause(&[elit(-1), elit(2)]);
        k.clause(&[elit(1), elit(-2)]);
        k.clause(&[elit(-2), elit(3)]);
        k.clause(&[elit(2), elit(-3)]);
        assert_eq!(k.solve(), KittenResult::Satisfied);
        let v1 = k.value(elit(1));
        let v2 = k.value(elit(2));
        assert_eq!(v1, v2, "chain model is uniform");
        let lit = if v1 > 0 { elit(1) } else { elit(-1) };
        assert!(
            !k.flip_literal(lit),
            "flipping a true chain member must fail (sole satisfier of its guard)"
        );
    }
}

#[cfg(test)]
mod flip_env_tests {
    use super::*;

    fn elit(lit: i32) -> u32 {
        let var = lit.unsigned_abs() - 1;
        2 * var + u32::from(lit < 0)
    }

    /// Exact sweep environment of x1 on the equivalence chain (depth 2,
    /// wrap clause): the model is uniform and flipping any true member
    /// must fail through its equivalence guard.
    #[test]
    fn flip_fails_on_chain_environment() {
        let mut k = Kitten::new();
        k.track_antecedents();
        // A(1) B(1) A(2) B(2) A(63) B(63) + (1 ∨ 64)
        k.clause(&[elit(-1), elit(2)]);
        k.clause(&[elit(1), elit(-2)]);
        k.clause(&[elit(-2), elit(3)]);
        k.clause(&[elit(2), elit(-3)]);
        k.clause(&[elit(-63), elit(64)]);
        k.clause(&[elit(63), elit(-64)]);
        k.clause(&[elit(1), elit(64)]);
        assert_eq!(k.solve(), KittenResult::Satisfied);
        // The model must be total and uniform over the chain fragment.
        for v in [1, 2, 3, 63, 64] {
            assert_ne!(k.value(elit(v)), 0, "var {v} must be assigned");
        }
        assert_eq!(k.value(elit(1)), k.value(elit(2)));
        assert_eq!(k.value(elit(2)), k.value(elit(3)));
        assert_eq!(k.value(elit(1)), k.value(elit(64)));
        // Flipping any true member must fail.
        for v in [1, 2, 3, 63, 64] {
            let lit = if k.value(elit(v)) > 0 {
                elit(v)
            } else {
                elit(-v)
            };
            assert!(
                !k.flip_literal(lit),
                "flipping true chain member x{v} must fail"
            );
        }
    }
}

#[cfg(test)]
mod flip_env2_tests {
    use super::*;

    fn elit(lit: i32) -> u32 {
        let var = lit.unsigned_abs() - 1;
        2 * var + u32::from(lit < 0)
    }

    /// The exact sweep env of x1 on chain.cnf (vars x1,x2,x3,x63,x64).
    #[test]
    fn flip_env_exact_chain() {
        let mut k = Kitten::new();
        k.track_antecedents();
        k.clause(&[elit(-1), elit(2)]); // A(0)
        k.clause(&[elit(1), elit(-2)]); // B(0)
        k.clause(&[elit(-2), elit(3)]); // A(1)
        k.clause(&[elit(2), elit(-3)]); // B(1)
        k.clause(&[elit(1), elit(64)]); // wrap
        k.clause(&[elit(-63), elit(64)]); // A(63)
        k.clause(&[elit(63), elit(-64)]); // B(63)
        assert_eq!(k.solve(), KittenResult::Satisfied);
        let v1 = k.value(elit(1));
        for v in [2, 3, 63, 64] {
            assert_ne!(k.value(elit(v)), 0, "assigned");
            assert_eq!(
                k.value(elit(v)),
                v1,
                "chain model must be uniform (x{v} = {} vs x1 = {})",
                k.value(elit(v)),
                v1
            );
        }
    }
}
