//! DRAT (Delete, Resolution Asymmetric Tautology) proof tracer — faithful
//! port of `drattracer.hpp` / `drattracer.cpp` / `drat.rs`.
//!
//! Streams a DRAT proof to a file in either **text** or **binary** format.
//! The checker (`drat-trim`) reads the original formula from the DIMACS file
//! and the derived clauses + deletions from this proof.
//!
//! - Additions: `lits… 0` (text) or `'a' <varint lits…> 0` (binary).
//! - Deletions: `d lits… 0` (text) or `'d' <varint lits…> 0` (binary).
//!
//! # Varint encoding (binary mode)
//!
//! A literal encodes as `2·|lit| + (lit < 0)`, emitted 7 bits per byte with
//! the high bit as a continuation flag (little-endian base-128), exactly as
//! upstream's `put_binary_lit`.

use std::fs::File;
use std::io::{self, BufWriter, Write};
use std::sync::Mutex;

use super::tracer::Tracer;

/// Streaming DRAT proof writer (text or binary).
pub struct DratTracer {
    writer: Mutex<BufWriter<File>>,
    binary: bool,
    /// Backing file path (matches upstream's `name`).
    pub name: String,
    /// Counters (mirror the `added` / `deleted` statistics).
    added: i64,
    deleted: i64,
    closed: bool,
}

impl DratTracer {
    /// Open `path` for a **text** DRAT proof (truncates an existing file).
    pub fn open(path: &str) -> io::Result<Self> {
        Self::new(path, false)
    }

    /// Open `path` for a **binary** DRAT proof (truncates an existing file).
    pub fn open_binary(path: &str) -> io::Result<Self> {
        Self::new(path, true)
    }

    fn new(path: &str, binary: bool) -> io::Result<Self> {
        let f = File::create(path)?;
        Ok(Self {
            writer: Mutex::new(BufWriter::new(f)),
            binary,
            name: path.to_string(),
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

    // -- binary primitives (faithful `put_binary_*`) ------------------

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

    // -- core emission (`drat_add_clause` / `drat_delete_clause`) -----

    /// `drat_add_clause` — emit an added (derived) clause.
    pub fn drat_add_clause(&mut self, clause: &[i32]) {
        if self.binary {
            let _ = self.writer.get_mut().expect("proof writer").write_all(b"a");
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
                .write_all(b"0\n");
        }
    }

    /// `drat_delete_clause` — emit a clause deletion.
    pub fn drat_delete_clause(&mut self, clause: &[i32]) {
        if self.binary {
            let _ = self.writer.get_mut().expect("proof writer").write_all(b"d");
        } else {
            let _ = self
                .writer
                .get_mut()
                .expect("proof writer")
                .write_all(b"d ");
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
                .write_all(b"0\n");
        }
    }

    // -- backward-compatible convenience wrappers ----------------------

    /// Text-style convenience wrapper: `add_derived_clause(0, false, 0, lits, &[])`.
    pub fn add_clause(&mut self, lits: &[i32]) {
        self.add_derived_clause(0, false, 0, lits, &[]);
    }

    /// Emit the empty clause (final line of an UNSAT proof).
    pub fn add_empty(&mut self) {
        self.drat_add_clause(&[]);
    }

    /// Flush buffered output to disk.
    pub fn flush(&mut self) {
        let _ = self.writer.get_mut().expect("proof writer").flush();
    }

    /// Number of added clauses emitted.
    #[must_use]
    pub fn added(&self) -> i64 {
        self.added
    }
    /// Number of deletions emitted.
    #[must_use]
    pub fn deleted(&self) -> i64 {
        self.deleted
    }
}

impl Tracer for DratTracer {
    /// `add_original_clause` — no-op for DRAT (originals come from the DIMACS
    /// file; the `redundant` flag, `witness` and `chain` are unused).
    fn add_original_clause(
        &mut self,
        _id: i64,
        _redundant: bool,
        _clause: &[i32],
        _restored: bool,
    ) {
    }

    /// `add_derived_clause` (`id`, `redundant`, `witness` and `chain` are
    /// unused by the DRAT format).
    fn add_derived_clause(
        &mut self,
        _id: i64,
        _redundant: bool,
        _witness: i32,
        clause: &[i32],
        _chain: &[i64],
    ) {
        if !self.closed {
            self.drat_add_clause(clause);
            self.added += 1;
        }
    }

    /// `delete_clause`.
    fn delete_clause(&mut self, _id: i64, _redundant: bool, clause: &[i32]) {
        if !self.closed {
            self.drat_delete_clause(clause);
            self.deleted += 1;
        }
    }

    fn begin_proof(&mut self, _id: i64) {}

    fn flush(&mut self, _print: bool) {
        if !self.closed {
            let _ = self.writer.get_mut().expect("proof writer").flush();
        }
    }

    fn close(&mut self, _print: bool) {
        if !self.closed {
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

    #[test]
    fn text_add_and_delete_format() {
        let mut t = DratTracer::open("/tmp/_oxiz_drat_text.drat").unwrap();
        t.add_clause(&[1, -2, 3]);
        t.delete_clause(7, false, &[4, 5]);
        t.close(false);
        drop(t);
        let s = std::fs::read_to_string("/tmp/_oxiz_drat_text.drat").unwrap();
        assert_eq!(s, "1 -2 3 0\nd 4 5 0\n");
    }

    #[test]
    fn binary_add_and_delete_format() {
        let mut t = DratTracer::open_binary("/tmp/_oxiz_drat_bin.drat").unwrap();
        t.add_clause(&[1, -2, 3]);
        t.delete_clause(7, false, &[4, 5]);
        t.close(false);
        drop(t);
        let b = std::fs::read("/tmp/_oxiz_drat_bin.drat").unwrap();
        let mut i = 0;
        // add: 'a' 1 -2 3 0
        assert_eq!(b[i], b'a');
        i += 1;
        assert_eq!(decode_lit(read_varint(&b, &mut i)), 1);
        assert_eq!(decode_lit(read_varint(&b, &mut i)), -2);
        assert_eq!(decode_lit(read_varint(&b, &mut i)), 3);
        assert_eq!(b[i], 0);
        i += 1;
        // delete: 'd' 4 5 0
        assert_eq!(b[i], b'd');
        i += 1;
        assert_eq!(decode_lit(read_varint(&b, &mut i)), 4);
        assert_eq!(decode_lit(read_varint(&b, &mut i)), 5);
        assert_eq!(b[i], 0);
    }

    #[test]
    fn empty_clause_emits_lone_zero() {
        let mut t = DratTracer::open("/tmp/_oxiz_drat_empty.drat").unwrap();
        t.add_empty();
        t.close(false);
        drop(t);
        let s = std::fs::read_to_string("/tmp/_oxiz_drat_empty.drat").unwrap();
        assert_eq!(s, "0\n");
    }
}
