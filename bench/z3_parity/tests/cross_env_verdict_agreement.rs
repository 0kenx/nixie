//! Cross-environment verdict-agreement check for the tracked parity records.
//!
//! # The invariant this pins
//!
//! `bench/z3_parity` commits one tracked record per environment,
//! `results.<os>-<arch>.json` (currently `results.macos-aarch64.json` and
//! `results.linux-x86_64.json`). Those files are the evidence behind the
//! published "168/168 Correct" parity claim, and the rule that makes them
//! usable as evidence is:
//!
//! > Every tracked `results.<os>-<arch>.json` must agree on the VERDICT of
//! > every benchmark (`nixie_result`, `z3_result`, `match_status`). Timings
//! > (`nixie_time`, `z3_time`) are machine-dependent and are expected to
//! > differ.
//!
//! This test is the standing enforcement of that rule.
//!
//! # Why it exists
//!
//! The layout used to be a single tracked `bench/z3_parity/results.json`,
//! cited everywhere as *the* authoritative result while it actually held
//! "whatever machine ran last". On 2026-07-31 a Linux run overwrote
//! macOS-recorded numbers and nothing in the file signalled it – a run on
//! one platform could silently overwrite another platform's recorded
//! evidence, and a genuine cross-platform verdict divergence would have
//! been indistinguishable from a routine re-run. `results.json` is now the
//! untracked scratch output of a local run, each environment commits its
//! own record, and this test is what notices when two of those records
//! stop telling the same story.
//!
//! # Cost
//!
//! None worth mentioning: this reads committed JSON only. No `z3` binary,
//! no solving, no benchmark execution – it runs anywhere `cargo test`
//! runs, including machines that have never had Z3 installed.

use nixie_z3_parity::{ParityReport, ParityResult, SCHEMA_VERSION, SCRATCH_RESULTS_FILE_NAME};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

/// Tracked records are named `results.<os>-<arch>.json`.
const TRACKED_PREFIX: &str = "results.";
const TRACKED_SUFFIX: &str = ".json";

/// Schema version this test understands. Spelled out rather than taken
/// from the library so that bumping `SCHEMA_VERSION` cannot silently carry
/// this test along: a new layout needs a deliberate look at the checks
/// below.
const EXPECTED_SCHEMA_VERSION: u32 = 1;

/// Upper bound on how many individual differences a failure message spells
/// out. The total count is always reported, so a wholesale divergence is
/// still visible without dumping thousands of lines.
const MAX_REPORTED_DIFFERENCES: usize = 25;

/// One tracked record: the library's own on-disk envelope plus the file it
/// came from. The schema itself is *not* redeclared here – `ParityReport`,
/// `RunMetadata` and `ParityResult` are the writer's types, so this test
/// cannot drift away from what the runner actually produces.
struct TrackedRecord {
    /// File name as committed, e.g. `results.macos-aarch64.json`.
    file_name: String,
    /// `<os>-<arch>` as taken from the file name.
    environment: String,
    report: ParityReport,
}

impl TrackedRecord {
    /// One-line provenance summary used in failure messages.
    ///
    /// The z3 version is included deliberately: a verdict disagreement
    /// between records produced by *different* z3 versions is
    /// unattributable – it says nothing about Nixie until both sides are
    /// re-measured against the same z3 binary.
    fn describe(&self) -> String {
        format!(
            "{} ({}/{}, nixie {}, z3 {}, {} benchmarks)",
            self.file_name,
            self.report.metadata.os,
            self.report.metadata.arch,
            self.report.metadata.nixie_version,
            self.report
                .metadata
                .z3_version
                .as_deref()
                .unwrap_or("unrecorded"),
            self.report.results.len()
        )
    }
}

/// Directory holding the benchmark suite and its tracked records. Resolved
/// from the crate manifest so the test is location-independent.
fn parity_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// Every committed `results.<os>-<arch>.json`, sorted by file name so the
/// reference record is chosen deterministically. The scratch
/// `results.json` is skipped.
fn discover_tracked_files() -> Vec<PathBuf> {
    let dir = parity_dir();
    let entries =
        fs::read_dir(&dir).unwrap_or_else(|e| panic!("failed to read {}: {e}", dir.display()));

    let mut files = Vec::new();
    for entry in entries {
        let entry = entry.unwrap_or_else(|e| panic!("failed to enumerate {}: {e}", dir.display()));
        let raw_name = entry.file_name();
        let Some(name) = raw_name.to_str() else {
            continue;
        };
        // The scratch file is whatever this machine produced last, not the
        // committed evidence of any environment.
        if name == SCRATCH_RESULTS_FILE_NAME {
            continue;
        }
        if !name.starts_with(TRACKED_PREFIX) || !name.ends_with(TRACKED_SUFFIX) {
            continue;
        }
        let path = entry.path();
        if path.is_file() {
            files.push(path);
        }
    }
    files.sort();
    files
}

fn load_record(path: &Path) -> TrackedRecord {
    let file_name = path
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or_else(|| panic!("tracked record has no UTF-8 file name: {}", path.display()))
        .to_string();

    let environment = file_name
        .strip_prefix(TRACKED_PREFIX)
        .and_then(|rest| rest.strip_suffix(TRACKED_SUFFIX))
        .unwrap_or_else(|| panic!("{file_name} is not named `results.<os>-<arch>.json`"))
        .to_string();

    let raw = fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));

    let report: ParityReport = serde_json::from_str(&raw).unwrap_or_else(|e| {
        panic!(
            "{file_name} does not deserialize into the harness's own `ParityReport` envelope \
             (`schema_version` + `metadata` + `results`): {e}. Note that the pre-envelope format \
             was a bare array of results – such a file has to be migrated, not renamed."
        )
    });

    TrackedRecord {
        file_name,
        environment,
        report,
    }
}

/// All tracked records. Panics when none exist – see the message for why
/// an empty set is a regression rather than a benign "nothing to check".
fn load_tracked_records() -> Vec<TrackedRecord> {
    let files = discover_tracked_files();
    if files.is_empty() {
        let dir = parity_dir();
        panic!(
            "no tracked parity record found in {}.\n\
             At least one `results.<os>-<arch>.json` (e.g. `results.macos-aarch64.json`) must be \
             committed: those files are the recorded evidence behind the published \
             \"168/168 Correct\" parity claim, so their disappearance is a real regression, not an \
             empty state. Note that `{SCRATCH_RESULTS_FILE_NAME}` is the git-ignored scratch \
             output of the most recent local run and is deliberately not counted as evidence.",
            dir.display()
        );
    }
    let mut records = Vec::with_capacity(files.len());
    for path in &files {
        records.push(load_record(path));
    }
    records
}

/// Record one difference: always counted, spelled out only while the
/// report is still short enough to be read.
fn push_difference(detail: String, count: &mut usize, sink: &mut Vec<String>) {
    *count += 1;
    if sink.len() < MAX_REPORTED_DIFFERENCES {
        sink.push(detail);
    }
}

/// The three fields that must agree across every environment, paired with
/// their names so a failure can say which one moved.
///
/// `nixie_time` and `z3_time` are deliberately absent and must stay absent:
/// they are wall-clock measurements of the machine that produced the file,
/// so two records of the *same* verdicts will legitimately differ in every
/// one of those fields. Comparing them would make this test fail on every
/// second environment for no reason and, worse, would train maintainers to
/// ignore it.
fn verdict_fields(result: &ParityResult) -> [(&'static str, String); 3] {
    [
        ("nixie_result", format!("{:?}", result.nixie_result)),
        ("z3_result", format!("{:?}", result.z3_result)),
        ("match_status", format!("{:?}", result.match_status)),
    ]
}

/// Index a record by `(logic, benchmark)`, rejecting duplicate keys: a
/// duplicate would silently shadow an entry and could hide a divergence.
fn index_by_benchmark(record: &TrackedRecord) -> BTreeMap<(&str, &str), &ParityResult> {
    let mut index = BTreeMap::new();
    for result in &record.report.results {
        let key = (result.logic.as_str(), result.benchmark.as_str());
        if let Some(previous) = index.insert(key, result) {
            panic!(
                "{} records logic {} benchmark {} twice ({:?} then {:?}); \
                 `(logic, benchmark)` must identify a benchmark uniquely",
                record.file_name,
                result.logic,
                result.benchmark,
                previous.match_status,
                result.match_status
            );
        }
    }
    index
}

#[test]
fn tracked_parity_records_are_present_and_well_formed() {
    assert_eq!(
        SCHEMA_VERSION, EXPECTED_SCHEMA_VERSION,
        "the harness now writes schema_version {SCHEMA_VERSION}, but this test only knows how to \
         validate version {EXPECTED_SCHEMA_VERSION}; review the checks in this file before \
         bumping the schema"
    );

    for record in load_tracked_records() {
        assert_eq!(
            record.report.schema_version, EXPECTED_SCHEMA_VERSION,
            "{} declares schema_version {} but this test understands only version \
             {EXPECTED_SCHEMA_VERSION}",
            record.file_name, record.report.schema_version
        );

        let actual = record.report.results.len();
        assert_eq!(
            record.report.metadata.benchmark_count, actual,
            "{} declares metadata.benchmark_count = {} but carries {actual} results; \
             the file is truncated, or the count was hand-edited",
            record.file_name, record.report.metadata.benchmark_count
        );
    }
}

#[test]
fn tracked_parity_record_file_names_match_recorded_environment() {
    for record in load_tracked_records() {
        let expected = format!(
            "{}-{}",
            record.report.metadata.os, record.report.metadata.arch
        );
        assert_eq!(
            record.environment, expected,
            "{} records os={} arch={}, so it must be named `results.{expected}.json`; \
             a record filed under another environment's name is exactly the confusion \
             the per-environment layout exists to prevent",
            record.file_name, record.report.metadata.os, record.report.metadata.arch
        );
    }
}

#[test]
fn tracked_parity_records_agree_on_every_verdict() {
    let records = load_tracked_records();

    // Fewer than two records: there is nothing to cross-check, so this
    // passes. (Zero records is already a hard failure inside
    // `load_tracked_records` – the evidence would be missing entirely.)
    if let [only] = records.as_slice() {
        eprintln!(
            "only one tracked parity record is present ({}); cross-environment agreement is \
             vacuous until a second environment commits its own results.<os>-<arch>.json",
            only.describe()
        );
        return;
    }

    // Agreement is an equivalence relation, so checking every record
    // against a single reference is enough to establish that all of them
    // agree with each other.
    let (reference, others) = records
        .split_first()
        .expect("load_tracked_records guarantees at least one record");
    let reference_index = index_by_benchmark(reference);

    let mut differences: Vec<String> = Vec::new();
    let mut difference_count: usize = 0;

    for record in others {
        let index = index_by_benchmark(record);

        // 1. The benchmark sets must be identical, reported by name.
        for (logic, benchmark) in reference_index.keys() {
            if !index.contains_key(&(*logic, *benchmark)) {
                push_difference(
                    format!(
                        "benchmark {benchmark} (logic {logic}): present in {} but MISSING from {}",
                        reference.file_name, record.file_name
                    ),
                    &mut difference_count,
                    &mut differences,
                );
            }
        }
        for (logic, benchmark) in index.keys() {
            if !reference_index.contains_key(&(*logic, *benchmark)) {
                push_difference(
                    format!(
                        "benchmark {benchmark} (logic {logic}): EXTRA in {}, absent from {}",
                        record.file_name, reference.file_name
                    ),
                    &mut difference_count,
                    &mut differences,
                );
            }
        }

        // 2. Every benchmark present in both must carry the same verdict.
        //    Timings are not compared – see `verdict_fields`.
        for (key, reference_result) in &reference_index {
            let Some(result) = index.get(key) else {
                // Already reported above as missing.
                continue;
            };
            let (logic, benchmark) = key;
            for ((field, reference_value), (_, value)) in verdict_fields(reference_result)
                .into_iter()
                .zip(verdict_fields(result))
            {
                if reference_value != value {
                    push_difference(
                        format!(
                            "benchmark {benchmark} (logic {logic}): field `{field}` differs – \
                             {} says {reference_value}, {} says {value}",
                            reference.file_name, record.file_name
                        ),
                        &mut difference_count,
                        &mut differences,
                    );
                }
            }
        }
    }

    if difference_count == 0 {
        return;
    }

    let provenance: Vec<String> = records
        .iter()
        .map(|record| format!("  - {}", record.describe()))
        .collect();
    let shown = differences.join("\n  ");
    let elided = difference_count.saturating_sub(differences.len());
    let elision_note = if elided == 0 {
        String::new()
    } else {
        format!("\n  ... and {elided} further difference(s) not shown")
    };

    panic!(
        "tracked parity records disagree in {difference_count} place(s).\n\n\
         Every tracked results.<os>-<arch>.json must agree on the VERDICT of every benchmark \
         (nixie_result, z3_result, match_status); only nixie_time/z3_time may differ between \
         machines.\n\n\
         Records compared:\n{}\n\n\
         Differences (reference = {}):\n  {shown}{elision_note}\n\n\
         If the records were produced by different z3 versions (see above), re-measure both \
         against the same z3 before attributing the disagreement to Nixie.",
        provenance.join("\n"),
        reference.file_name
    );
}
