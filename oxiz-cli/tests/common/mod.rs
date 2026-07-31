//! Shared test-only helpers for `oxiz-cli`'s integration test binaries.
//!
//! Each file directly under `tests/` compiles as its own separate test
//! binary (its own OS process), and on top of that `cargo test` (unlike
//! `cargo nextest`) runs every `#[test]` fn *within* one such binary as a
//! thread inside a single process. Several of these test files used to
//! build "unique" temp file names from a timestamp (down to nanoseconds in
//! some copies). A timestamp is not actually unique: two threads/processes
//! can sample the same instant, and even when they don't, narrowing the
//! window only makes the collision rarer, not impossible. When two tests
//! did collide on the same path, one truncated or overwrote the other's
//! input file mid-read -- observed in production as a parser choking on a
//! corrupted `.smt2` file (e.g. `const` overwritten mid-word into `onst`)
//! or a file vanishing out from under a running solve. Both looked like
//! unrelated solver flakiness and were misdiagnosed as such more than once.
//!
//! [`unique_temp_path`] makes a collision impossible by construction
//! instead of merely unlikely: the OS process id distinguishes concurrent
//! processes, and a per-process, monotonically increasing `AtomicU64`
//! counter distinguishes concurrent threads/tests within one process. Every
//! call, from any thread, in any test binary, produces a path no other call
//! anywhere can ever produce again.
//!
//! [`TempPath`] and [`TempDirPath`] additionally create the file/directory
//! with `create_new(true)` (files) so a residual collision -- e.g. a stale
//! file left over from a killed previous run -- fails loudly and
//! immediately instead of silently corrupting another test's data, and they
//! remove themselves on `Drop`, which runs even when a test panics (the
//! default test harness unwinds rather than aborts), so a failing
//! assertion never leaks files into the shared system temp directory.

#![allow(dead_code)] // Not every test binary that pulls in this module uses every helper.

use std::fs::{self, OpenOptions};
use std::io::Write;
use std::ops::Deref;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

/// Per-process counter distinguishing concurrent callers within one test
/// binary; combined with the process id this makes every returned path
/// globally unique for the lifetime of the machine.
static COUNTER: AtomicU64 = AtomicU64::new(0);

/// Build a path under [`std::env::temp_dir`] that cannot collide with any
/// other call to this function, in this process or any other, ever again.
///
/// `prefix` and `extension` only affect readability of leftover files if
/// cleanup is ever skipped (e.g. a `kill -9` mid-test); they play no role
/// in uniqueness.
pub fn unique_temp_path(prefix: &str, extension: &str) -> PathBuf {
    let pid = std::process::id();
    let seq = COUNTER.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!("{prefix}_{pid}_{seq}.{extension}"))
}

/// An RAII guard around a single temp file path. Removes the file on
/// `Drop`, including when the owning test panics.
#[derive(Debug)]
pub struct TempPath(PathBuf);

impl TempPath {
    /// Reserve a collision-proof path without creating anything at it yet
    /// (for paths the CLI-under-test is expected to create, or paths a test
    /// deliberately leaves absent).
    pub fn reserve(prefix: &str, extension: &str) -> Self {
        Self(unique_temp_path(prefix, extension))
    }

    /// Reserve a collision-proof path and eagerly create it with `content`,
    /// using `create_new(true)` so a residual collision is reported as an
    /// immediate I/O error rather than silently truncating another test's
    /// file.
    pub fn write(prefix: &str, extension: &str, content: &str) -> Self {
        let this = Self::reserve(prefix, extension);
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&this.0)
            .expect("unique temp path must not already exist");
        file.write_all(content.as_bytes())
            .expect("failed to write temp file contents");
        this
    }

    /// Borrow the underlying path explicitly (equivalent to `&*self`).
    pub fn path(&self) -> &Path {
        &self.0
    }
}

impl Deref for TempPath {
    type Target = Path;

    fn deref(&self) -> &Path {
        &self.0
    }
}

impl AsRef<Path> for TempPath {
    fn as_ref(&self) -> &Path {
        &self.0
    }
}

impl AsRef<std::ffi::OsStr> for TempPath {
    fn as_ref(&self) -> &std::ffi::OsStr {
        self.0.as_os_str()
    }
}

impl Drop for TempPath {
    fn drop(&mut self) {
        // Best-effort: the path may never have been created (`reserve`), or
        // may already have been removed explicitly by the test; either way
        // a missing file at cleanup time is not an error.
        let _ = fs::remove_file(&self.0);
    }
}

/// An RAII guard around a temp *directory* path (e.g. `--checkpoint-dir`).
/// Recursively removes the directory on `Drop`, including when the owning
/// test panics.
#[derive(Debug)]
pub struct TempDirPath(PathBuf);

impl TempDirPath {
    /// Reserve a collision-proof directory path without creating it (the
    /// CLI-under-test, or the test itself, is expected to create it).
    pub fn reserve(prefix: &str) -> Self {
        let pid = std::process::id();
        let seq = COUNTER.fetch_add(1, Ordering::Relaxed);
        Self(std::env::temp_dir().join(format!("{prefix}_{pid}_{seq}")))
    }

    pub fn path(&self) -> &Path {
        &self.0
    }
}

impl Deref for TempDirPath {
    type Target = Path;

    fn deref(&self) -> &Path {
        &self.0
    }
}

impl AsRef<Path> for TempDirPath {
    fn as_ref(&self) -> &Path {
        &self.0
    }
}

impl AsRef<std::ffi::OsStr> for TempDirPath {
    fn as_ref(&self) -> &std::ffi::OsStr {
        self.0.as_os_str()
    }
}

impl Drop for TempDirPath {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
