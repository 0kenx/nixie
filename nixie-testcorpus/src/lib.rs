//! Shared loader for the external SMT/SAT corpora used by integration
//! tests (`satcomp2024/`, `satcomp2025/`, `smt-lib/`, `satlib/`).
//!
//! Those corpora are **gitignored external data** (see `.gitignore`: they
//! are multi-hundred-thousand-file trees that are deliberately not
//! tracked), which means **git worktrees do not contain them** — only the
//! primary checkout has them on disk.  A test that reads a corpus file
//! from a worktree therefore used to fail in one of three confusing ways:
//! a cryptic `No such file or directory` panic that looked like a solver
//! regression (this exact shape once sent a debugging session into a
//! multi-hour bisect), a *vacuous pass* from a quiet early-return, or an
//! `Unknown` verdict that failed downstream assertions.
//!
//! This crate makes the failure mode uniform and actionable:
//!
//! * [`read`] / [`require_path`] — the default: **fail loudly** with a
//!   `[corpus-missing]` diagnosis that detects linked worktrees, prints
//!   the exact `ln -s` command to import the corpus from the primary
//!   checkout, and names the opt-out.  A soundness test that cannot run
//!   its input must never report success.
//! * `NIXIE_CORPUS_MISSING=skip` — an explicit, per-run opt-out: tests
//!   written with [`read_or_skip!`] print a visible per-file note and
//!   return early (the test then shows as *passed*, so reserve this for
//!   environments that intentionally run corpus-less).
//!
//! All path resolution is relative to the workspace root (the parent of
//! this crate's directory), so the helper works identically from any
//! workspace member's integration tests.

use std::path::{Path, PathBuf};
use std::sync::OnceLock;

/// Environment variable that turns loud failure into a visible skip:
/// `NIXIE_CORPUS_MISSING=skip`.
pub const SKIP_ENV: &str = "NIXIE_CORPUS_MISSING";

/// Workspace root (this crate's parent directory), computed once.
pub fn repo_root() -> &'static Path {
    static ROOT: OnceLock<PathBuf> = OnceLock::new();
    ROOT.get_or_init(|| {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .map(Path::to_path_buf)
            .unwrap_or_else(|| PathBuf::from("."))
    })
}

/// Absolute path of a corpus file `rel` (relative to the workspace root).
#[must_use]
pub fn corpus_path(rel: &str) -> PathBuf {
    repo_root().join(rel.trim_start_matches('/'))
}

/// Whether the operator asked for visible-skips instead of loud failure.
#[must_use]
pub fn skip_requested() -> bool {
    std::env::var(SKIP_ENV).as_deref() == Ok("skip")
}

/// Read a corpus file, or `None` when absent (and skipping was requested).
///
/// When the file is absent and skipping was *not* requested this panics
/// with the loud `[corpus-missing]` diagnosis (see [`read`]).
pub fn read_opt(rel: &str) -> Option<String> {
    let path = corpus_path(rel);
    match std::fs::read_to_string(&path) {
        Ok(text) => Some(text),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            if skip_requested() {
                eprintln!("[corpus-skip] {rel}: not present in this checkout ({SKIP_ENV}=skip)");
                None
            } else {
                panic!("{}", missing_diagnosis(rel, &path));
            }
        }
        Err(e) => panic!("[corpus-error] reading {}: {e}", path.display()),
    }
}

/// Read a corpus file, failing loudly (and actionably) when absent.
///
/// # Panics
///
/// With a `[corpus-missing]` message when the file is not present —
/// including worktree detection and the exact symlink command to fix it —
/// unless `NIXIE_CORPUS_MISSING=skip`, in which case this still panics:
/// use [`read_or_skip!`] for the visible-skip form.
pub fn read(rel: &str) -> String {
    let path = corpus_path(rel);
    match std::fs::read_to_string(&path) {
        Ok(text) => text,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            panic!("{}", missing_diagnosis(rel, &path))
        }
        Err(e) => panic!("[corpus-error] reading {}: {e}", path.display()),
    }
}

/// Path of a corpus file as a `String`, failing loudly when absent (for
/// parsers that take a path, e.g. `DimacsParser::parse_file`).
///
/// # Panics
///
/// Same diagnosis as [`read`].
pub fn require_path(rel: &str) -> String {
    let path = corpus_path(rel);
    if path.is_file() {
        return path.to_string_lossy().into_owned();
    }
    panic!("{}", missing_diagnosis(rel, &path));
}

/// Read a corpus file or visibly skip the current test.
///
/// Expands to an expression of type `String`: the file's content when
/// present; when absent, prints a `[corpus-skip]` note (only under
/// `NIXIE_CORPUS_MISSING=skip`) and `return`s from the enclosing test —
/// which must therefore return `()`.
#[macro_export]
macro_rules! read_or_skip {
    ($rel:expr) => {
        match $crate::read_opt($rel) {
            Some(text) => text,
            None => return,
        }
    };
}

/// The loud, actionable missing-file diagnosis.
fn missing_diagnosis(rel: &str, path: &Path) -> String {
    let root = repo_root();
    let mut msg = String::new();
    msg.push_str("[corpus-missing] external corpus file not present:\n  ");
    msg.push_str(&path.display().to_string());
    msg.push_str("\n\nThe SMT/SAT corpora (satcomp2024, satcomp2025, smt-lib, satlib) are\ngitignored external data and are NOT copied into git worktrees; only\nthe primary checkout has them on disk.\n");
    if let Some(primary) = linked_worktree_primary(root) {
        let corpus_root = rel.split('/').next().unwrap_or(rel);
        msg.push_str(&format!(
            "\nThis checkout is a linked worktree; its primary checkout is:\n  {}\nThe corpus root `{corpus_root}` is missing here{}.\n\nFix (from the worktree root):\n  ln -s {}/{} {}/{}\n",
            primary.display(),
            if primary.join(corpus_root).is_dir() {
                " but present in the primary checkout"
            } else {
                " (and not present in the primary checkout either)"
            },
            primary.display(),
            corpus_root,
            root.display(),
            corpus_root,
        ));
    } else {
        msg.push_str("\nThis checkout is not a linked worktree; place the corpus root\n(satcomp2024/satcomp2025/smt-lib/satlib) at the workspace root, or run\nthe tests from the checkout that has the corpora on disk.\n");
    }
    msg.push_str(&format!(
        "\nTo run corpus-dependent tests without the corpora (each prints a\nvisible [corpus-skip] note and returns early), set:\n  {SKIP_ENV}=skip"
    ));
    msg
}

/// If `root` is a linked git worktree, resolve its primary checkout's
/// root directory (best effort; `None` when not a worktree or anything is
/// unexpected — diagnostics then fall back to the generic message).
fn linked_worktree_primary(root: &Path) -> Option<PathBuf> {
    let dot_git = root.join(".git");
    if !dot_git.is_file() {
        return None; // primary checkout (or not a git repo): no `.git` file
    }
    let git_link = std::fs::read_to_string(&dot_git).ok()?;
    let gitdir = git_link.strip_prefix("gitdir:")?.trim();
    let gitdir = Path::new(gitdir);
    // `<primary>/.git/worktrees/<name>/commondir` holds the common dir
    // (relative to gitdir), which is `<primary>/.git`.
    let common_raw = std::fs::read_to_string(gitdir.join("commondir")).ok()?;
    let common_raw = common_raw.trim();
    let common = if Path::new(common_raw).is_absolute() {
        PathBuf::from(common_raw)
    } else {
        gitdir.join(common_raw)
    };
    // Canonicalise away the `worktrees/<name>/../..` hops.
    let common = common.canonicalize().unwrap_or(common);
    common.parent().map(Path::to_path_buf)
}

#[cfg(test)]
mod tests {
    use super::*;

    const FIXTURE: &str = "nixie-testcorpus/tests/fixtures/hello.txt";

    #[test]
    fn reads_present_file() {
        assert_eq!(read(FIXTURE).trim(), "corpus fixture");
        assert_eq!(
            read_opt(FIXTURE).map(|s| s.trim().to_string()).as_deref(),
            Some("corpus fixture")
        );
        assert!(require_path(FIXTURE).ends_with("hello.txt"));
    }

    #[test]
    fn missing_file_panics_with_actionable_diagnosis() {
        let result = std::panic::catch_unwind(|| read("smt-lib/definitely/not/here.smt2"));
        let msg = match result {
            Err(payload) => payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_default(),
            Ok(_) => panic!("read() must panic on a missing corpus file"),
        };
        assert!(msg.contains("[corpus-missing]"), "message: {msg}");
        assert!(msg.contains("NIXIE_CORPUS_MISSING=skip"), "message: {msg}");
        assert!(
            msg.contains("worktree") || msg.contains("workspace root"),
            "message: {msg}"
        );
    }

    #[test]
    fn missing_path_require_panics_loudly() {
        let result = std::panic::catch_unwind(|| require_path("satcomp2024/nope.cnf"));
        assert!(result.is_err(), "require_path() must panic on missing file");
    }

    #[test]
    fn corpus_path_is_root_relative() {
        let p = corpus_path("satcomp2024/bench/x.cnf");
        assert!(p.starts_with(repo_root()));
        assert!(p.ends_with("satcomp2024/bench/x.cnf"));
    }

    #[test]
    fn skip_env_not_set_in_tests() {
        // nextest runs each test in its own process, so asserting the
        // *unset* default here also documents the default policy.
        assert!(!skip_requested());
    }

    #[test]
    fn read_or_skip_macro_yields_content() {
        // In-process: with the file present the macro is just read().
        let text: String = read_or_skip!(FIXTURE);
        assert_eq!(text.trim(), "corpus fixture");
    }
}
