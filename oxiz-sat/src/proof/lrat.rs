//! LRAT proof tracer – faithful port of `lrattracer.hpp` / `lrattracer.cpp` /
//! `lrat.rs`.
//!
//! Streams an LRAT (Linear RAT) proof to a file in either **text** or
//! **binary** format. The original formula is read by the checker from the
//! DIMACS file (clauses numbered `1..N` in file order); this tracer emits the
//! derived clauses and deletions.
//!
//! Each addition is `id lits… 0 hints… 0` (text) or `'a' <varint id>
//! <varint lits…> 0 <varint hints…> 0` (binary). Deletions are *batched and
//! deferred*: each [`LratTracer::lrat_delete_clause`] only records the id, and
//! the accumulated `d …` line is flushed ahead of the next addition (or on
//! [`LratTracer::flush`]); this matches upstream's `delete_ids` buffering.
//!
//! `lrat-check` (shipped with `drat-trim`) verifies these proofs.
//!
//! # Varint encoding (binary mode)
//!
//! Literals encode as `2·|lit| + (lit < 0)`; ids as `2·|id| + (id < 0)`,
//! emitted 7 bits per byte with the high bit as a continuation flag
//! (little-endian base-128), exactly as upstream's `put_binary_lit` /
//! `put_binary_id`.

use std::fs::File;
use std::io::{self, BufWriter, Write};
use std::sync::{Arc, Mutex};

use super::tracer::Tracer;

/// A complete in-memory LRAT transcript.
///
/// Original clauses are kept separately because LRAT numbers them implicitly
/// as `1..=N`; the textual proof contains only derived clauses and deletions.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct LratTranscript {
    /// Original clauses, in clause-id order.
    pub original_clauses: Vec<Vec<i32>>,
    /// Text LRAT proof body.
    pub proof: String,
}

/// Read handle for an in-memory LRAT tracer attached to a solver.
///
/// The handle is deliberately separate from the tracer owned by the proof
/// dispatcher.  A caller can retain it across `solve` and snapshot the exact
/// transcript at the result gate without reaching into the solver's internals.
#[derive(Debug, Clone)]
pub struct LratTranscriptHandle {
    inner: Arc<Mutex<LratTranscriptState>>,
}

impl LratTranscriptHandle {
    /// Clone the transcript accumulated so far.
    ///
    /// A poisoned lock is reported as an error.  Certification callers must
    /// turn that error into an untrusted/unknown verdict, never accept a
    /// partial transcript.
    pub fn snapshot(&self) -> Result<LratTranscript, String> {
        let state = self
            .inner
            .lock()
            .map_err(|_| "in-memory LRAT transcript lock was poisoned".to_string())?;
        match &state.error {
            Some(error) => Err(error.clone()),
            None => Ok(state.transcript.clone()),
        }
    }
}

#[derive(Debug, Default)]
struct LratTranscriptState {
    transcript: LratTranscript,
    error: Option<String>,
}

/// LRAT tracer that retains both the original clause set and the proof body in
/// memory for an in-process exit-gate checker.
pub struct MemoryLratTracer {
    inner: Arc<Mutex<LratTranscriptState>>,
    latest_id: i64,
    delete_ids: Vec<i64>,
    closed: bool,
}

impl MemoryLratTracer {
    /// Create a tracer and the independent handle used to read its transcript.
    #[must_use]
    pub fn new() -> (Self, LratTranscriptHandle) {
        let inner = Arc::new(Mutex::new(LratTranscriptState::default()));
        (
            Self {
                inner: Arc::clone(&inner),
                latest_id: 0,
                delete_ids: Vec::new(),
                closed: false,
            },
            LratTranscriptHandle { inner },
        )
    }

    fn with_state(&self, f: impl FnOnce(&mut LratTranscriptState)) {
        // Tracer callbacks cannot return errors.  If the lock is poisoned we
        // leave the transcript incomplete; `snapshot` then fails closed at the
        // certification gate.
        if let Ok(mut state) = self.inner.lock() {
            f(&mut state);
        }
    }

    fn flush_deletes(&mut self) {
        if self.delete_ids.is_empty() {
            return;
        }
        let latest_id = self.latest_id;
        let ids = core::mem::take(&mut self.delete_ids);
        self.with_state(|state| {
            use core::fmt::Write as _;
            let _ = write!(state.transcript.proof, "{latest_id} d ");
            for id in ids {
                let _ = write!(state.transcript.proof, "{id} ");
            }
            state.transcript.proof.push_str("0\n");
        });
    }
}

impl Tracer for MemoryLratTracer {
    fn add_original_clause(&mut self, id: i64, _redundant: bool, clause: &[i32], restored: bool) {
        if self.closed {
            return;
        }
        self.with_state(|state| {
            if restored {
                state.error.get_or_insert_with(|| {
                    "in-memory LRAT certification does not support restored clauses".to_string()
                });
                return;
            }
            // A gap or reorder makes the implicit LRAT numbering ambiguous.
            // Preserve an explicit failure instead of fabricating a marker
            // literal that a permissive checker might accidentally accept.
            if id != state.transcript.original_clauses.len() as i64 + 1 {
                state.error.get_or_insert_with(|| {
                    format!("in-memory LRAT original clause id {id} is not the next sequential id")
                });
            } else {
                state.transcript.original_clauses.push(clause.to_vec());
            }
        });
    }

    fn add_derived_clause(
        &mut self,
        id: i64,
        _redundant: bool,
        _witness: i32,
        clause: &[i32],
        chain: &[i64],
    ) {
        if self.closed {
            return;
        }
        self.flush_deletes();
        self.latest_id = id;
        self.with_state(|state| {
            use core::fmt::Write as _;
            let _ = write!(state.transcript.proof, "{id} ");
            for lit in clause {
                let _ = write!(state.transcript.proof, "{lit} ");
            }
            state.transcript.proof.push_str("0 ");
            for hint in chain {
                let _ = write!(state.transcript.proof, "{hint} ");
            }
            state.transcript.proof.push_str("0\n");
        });
    }

    fn delete_clause(&mut self, id: i64, _redundant: bool, _clause: &[i32]) {
        if !self.closed {
            self.delete_ids.push(id);
        }
    }

    fn begin_proof(&mut self, id: i64) {
        if !self.closed {
            self.latest_id = id;
        }
    }

    fn flush(&mut self, _print: bool) {
        if !self.closed {
            self.flush_deletes();
        }
    }

    fn close(&mut self, _print: bool) {
        if !self.closed {
            self.flush_deletes();
            self.closed = true;
        }
    }

    fn closed(&self) -> bool {
        self.closed
    }
}

/// Streaming LRAT proof writer (text or binary).
pub struct LratTracer {
    writer: Mutex<BufWriter<File>>,
    binary: bool,
    /// Backing file path (matches upstream's `name`).
    pub name: String,
    /// Largest id written so far (`latest_id` in upstream).
    latest_id: i64,
    /// Deletions deferred until the next addition (`delete_ids` in upstream).
    delete_ids: Vec<i64>,
    /// Counters (mirrors the `added` / `deleted` statistics).
    added: i64,
    deleted: i64,
    closed: bool,
}

impl LratTracer {
    /// Open `path` for a **text** LRAT proof (truncates an existing file).
    pub fn open(path: &str) -> io::Result<Self> {
        Self::new(path, false)
    }

    /// Open `path` for a **binary** LRAT proof (truncates an existing file).
    pub fn open_binary(path: &str) -> io::Result<Self> {
        Self::new(path, true)
    }

    fn new(path: &str, binary: bool) -> io::Result<Self> {
        let f = File::create(path)?;
        Ok(Self {
            writer: Mutex::new(BufWriter::new(f)),
            binary,
            name: path.to_string(),
            latest_id: 0,
            delete_ids: Vec::new(),
            added: 0,
            deleted: 0,
            closed: false,
        })
    }

    /// Whether this tracer emits the binary proof format.
    #[must_use]
    pub fn binary(&self) -> bool {
        self.binary
    }

    // ======== binary primitives (faithful `put_binary_*`) ========

    #[inline]
    fn put_binary_zero(&mut self) {
        let _ = self.writer.get_mut().expect("proof writer").write_all(&[0]);
    }

    /// Emit a literal as a signed varint (`put_binary_lit`).
    #[inline]
    fn put_binary_lit(&mut self, lit: i32) {
        let idx = lit.unsigned_abs() as u64;
        let x = 2 * idx + (lit < 0) as u64;
        self.write_varint(x);
    }

    /// Emit an id as a signed varint (`put_binary_id`).
    #[inline]
    fn put_binary_id(&mut self, id: i64) {
        let a = id.unsigned_abs();
        let x = 2 * a + (id < 0) as u64;
        self.write_varint(x);
    }

    #[inline]
    fn write_varint(&mut self, mut x: u64) {
        while x & !0x7f != 0 {
            let _ = self
                .writer
                .get_mut()
                .expect("proof writer")
                .write_all(&[((x & 0x7f) | 0x80) as u8]);
            x >>= 7;
        }
        let _ = self
            .writer
            .get_mut()
            .expect("proof writer")
            .write_all(&[x as u8]);
    }

    /// Emit any buffered deletions as a `d …` line and clear the buffer.
    fn flush_deletes(&mut self) {
        if self.delete_ids.is_empty() {
            return;
        }
        let ids = self.delete_ids.clone();
        self.delete_ids.clear();
        if self.binary {
            let _ = self.writer.get_mut().expect("proof writer").write_all(b"d");
        } else {
            // Faithful to upstream: the leading index of a deletion line is the
            // id of the most-recently added clause. `lrat-check` parses but
            // ignores this index (it deletes the ids listed after `d`), so its
            // value is cosmetic; we reproduce upstream's convention exactly.
            let _ = write!(
                self.writer.get_mut().expect("proof writer"),
                "{} ",
                self.latest_id
            );
            let _ = self
                .writer
                .get_mut()
                .expect("proof writer")
                .write_all(b"d ");
        }
        for did in ids {
            if self.binary {
                self.put_binary_id(did);
            } else {
                let _ = write!(self.writer.get_mut().expect("proof writer"), "{did} ");
            }
        }
        if self.binary {
            self.put_binary_zero();
        } else {
            let _ = self
                .writer
                .get_mut()
                .expect("proof writer")
                .write_all(b"0\n");
        }
    }

    // ======== core emission (`lrat_add_clause` / `lrat_delete_clause`) ========

    /// Flush any pending deletions, then write an added clause with its RUP
    /// hint chain. Faithful port of `LratTracer::lrat_add_clause`.
    pub fn lrat_add_clause(&mut self, id: i64, clause: &[i32], chain: &[i64]) {
        self.flush_deletes();
        self.latest_id = id;

        if self.binary {
            let _ = self.writer.get_mut().expect("proof writer").write_all(b"a");
            self.put_binary_id(id);
        } else {
            let _ = write!(self.writer.get_mut().expect("proof writer"), "{id} ");
        }
        for &lit in clause {
            if self.binary {
                self.put_binary_lit(lit);
            } else {
                let _ = write!(self.writer.get_mut().expect("proof writer"), "{lit} ");
            }
        }
        if self.binary {
            self.put_binary_zero();
        } else {
            let _ = self
                .writer
                .get_mut()
                .expect("proof writer")
                .write_all(b"0 ");
        }
        for &c in chain {
            if self.binary {
                self.put_binary_id(c);
            } else {
                let _ = write!(self.writer.get_mut().expect("proof writer"), "{c} ");
            }
        }
        if self.binary {
            self.put_binary_zero();
        } else {
            let _ = self
                .writer
                .get_mut()
                .expect("proof writer")
                .write_all(b"0\n");
        }
    }

    /// Defer a clause deletion (`lrat_delete_clause`): the id is buffered and
    /// emitted as part of a batched `d …` line ahead of the next addition.
    pub fn lrat_delete_clause(&mut self, id: i64) {
        self.delete_ids.push(id);
    }

    // ======== backward-compatible convenience wrappers ========

    /// Text-style convenience wrapper: `add_derived_clause(id, false, 0, lits, hints)`.
    pub fn add_clause(&mut self, id: i64, lits: &[i32], hints: &[i64]) {
        self.add_derived_clause(id, false, 0, lits, hints);
    }

    /// Flush buffered output to disk (also flushes any pending deletions as a
    /// final `d …` line, matching upstream's `flush`).
    pub fn flush(&mut self) {
        self.flush_deletes();
        let _ = self.writer.get_mut().expect("proof writer").flush();
    }

    /// Number of added clauses emitted.
    #[must_use]
    pub fn added(&self) -> i64 {
        self.added
    }
    /// Number of deletions recorded.
    #[must_use]
    pub fn deleted(&self) -> i64 {
        self.deleted
    }
}

impl Tracer for LratTracer {
    fn add_derived_clause(
        &mut self,
        id: i64,
        _redundant: bool,
        _witness: i32,
        clause: &[i32],
        chain: &[i64],
    ) {
        if !self.closed {
            self.lrat_add_clause(id, clause, chain);
            self.added += 1;
        }
    }
    fn delete_clause(&mut self, id: i64, _redundant: bool, _clause: &[i32]) {
        if !self.closed {
            self.lrat_delete_clause(id);
            self.deleted += 1;
        }
    }
    fn begin_proof(&mut self, id: i64) {
        if !self.closed {
            self.latest_id = id;
        }
    }
    fn flush(&mut self, _print: bool) {
        if !self.closed {
            self.flush_deletes();
            let _ = self.writer.get_mut().expect("proof writer").flush();
        }
    }
    fn close(&mut self, _print: bool) {
        if !self.closed {
            self.flush_deletes();
            let _ = self.writer.get_mut().expect("proof writer").flush();
            self.closed = true;
        }
    }
    fn closed(&self) -> bool {
        self.closed
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Decode a base-128 varint (little-endian, high bit = continuation).
    fn read_varint(bytes: &[u8], i: &mut usize) -> u64 {
        let mut x = 0u64;
        let mut shift = 0u32;
        loop {
            let b = bytes[*i];
            *i += 1;
            x |= ((b & 0x7f) as u64) << shift;
            if b & 0x80 == 0 {
                return x;
            }
            shift += 7;
        }
    }

    fn decode_lit(x: u64) -> i32 {
        let idx = (x / 2) as i32;
        if x & 1 == 1 { -idx } else { idx }
    }
    fn decode_id(x: u64) -> i64 {
        let a = (x / 2) as i64;
        if x & 1 == 1 { -a } else { a }
    }

    #[test]
    fn text_add_line_format() {
        let mut t = LratTracer::open("/tmp/_oxiz_lrat_text.lrat").unwrap();
        t.add_clause(7, &[1, -2, 3], &[4, 5]);
        t.close(false);
        drop(t);
        let s = std::fs::read_to_string("/tmp/_oxiz_lrat_text.lrat").unwrap();
        assert_eq!(s, "7 1 -2 3 0 4 5 0\n");
    }

    #[test]
    fn text_deferred_deletion_batches_into_one_line() {
        let mut t = LratTracer::open("/tmp/_oxiz_lrat_del.lrat").unwrap();
        t.delete_clause(2, false, &[]);
        t.delete_clause(5, false, &[]);
        t.add_clause(9, &[1], &[]); // flushes the deferred 'd' line first
        t.close(false);
        drop(t);
        let s = std::fs::read_to_string("/tmp/_oxiz_lrat_del.lrat").unwrap();
        // delete line: "{latest_id=0} d 2 5 0\n" then the add line.
        assert_eq!(s, "0 d 2 5 0\n9 1 0 0\n");
    }

    #[test]
    fn binary_add_line_format() {
        let mut t = LratTracer::open_binary("/tmp/_oxiz_lrat_bin.lrat").unwrap();
        t.add_clause(1, &[1, -1], &[]); // id 1, lits 1,-1, no hints
        t.close(false);
        drop(t);
        let b = std::fs::read("/tmp/_oxiz_lrat_bin.lrat").unwrap();
        let mut i = 0;
        assert_eq!(b[i], b'a');
        i += 1;
        assert_eq!(decode_id(read_varint(&b, &mut i)), 1);
        assert_eq!(decode_lit(read_varint(&b, &mut i)), 1);
        assert_eq!(decode_lit(read_varint(&b, &mut i)), -1);
        assert_eq!(b[i], 0);
        i += 1;
        assert_eq!(b[i], 0); // empty hint chain terminator
    }

    #[test]
    fn varint_roundtrip() {
        let mut t = LratTracer::open_binary("/tmp/_oxiz_lrat_v.lrat").unwrap();
        // lit 100 → 200, lit -100 → 201; id 1 → 2.
        t.add_clause(1, &[100, -100], &[]);
        t.close(false);
        drop(t);
        let b = std::fs::read("/tmp/_oxiz_lrat_v.lrat").unwrap();
        let mut i = 1; // skip 'a'
        assert_eq!(decode_id(read_varint(&b, &mut i)), 1);
        assert_eq!(decode_lit(read_varint(&b, &mut i)), 100);
        assert_eq!(decode_lit(read_varint(&b, &mut i)), -100);
    }

    #[test]
    fn memory_tracer_captures_originals_and_proof() {
        let (mut tracer, handle) = MemoryLratTracer::new();
        tracer.add_original_clause(1, false, &[1], false);
        tracer.add_original_clause(2, false, &[-1], false);
        tracer.add_derived_clause(3, false, 0, &[], &[1, 2]);

        let transcript = handle.snapshot().expect("transcript lock");
        assert_eq!(transcript.original_clauses, vec![vec![1], vec![-1]]);
        assert_eq!(transcript.proof, "3 0 1 2 0\n");
    }

    #[test]
    fn memory_tracer_rejects_non_sequential_original_ids() {
        let (mut tracer, handle) = MemoryLratTracer::new();
        tracer.add_original_clause(2, false, &[1], false);

        assert!(
            handle
                .snapshot()
                .is_err_and(|error| error.contains("not the next sequential id"))
        );
    }

    #[test]
    fn memory_tracer_rejects_restored_originals() {
        let (mut tracer, handle) = MemoryLratTracer::new();
        tracer.add_original_clause(1, false, &[1], true);

        assert!(
            handle
                .snapshot()
                .is_err_and(|error| error.contains("restored clauses"))
        );
    }
}
