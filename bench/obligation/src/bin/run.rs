//! `obligation-run` — check a solver against the certificates.
//!
//! For every instance: run the solver, parse one answer per `check-sat`
//! (SMT-LIB or SAT-competition format), compare against the expected
//! vector. Optionally cross-check the *generator* by running Z3 (SMT2 and
//! CNF) and CaDiCaL (CNF) — a Z3 disagreement with the certificate is
//! reported as GENFAIL, distinct from a solver mismatch.
//!
//! Timeouts use a poll/kill/reap loop: the child is always reaped, unlike
//! a detached-thread timeout that leaks a running solver.
//!
//! Mismatches, crashes and generator disagreements are written to the
//! artifacts directory together with the exact input, expected answers,
//! and provenance — never deleted automatically.

use nixie_obligation::registry::{self, Size};
use nixie_obligation::stress::StressCfg;
use nixie_obligation::{Answer, Instance};
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};
use std::time::{Duration, Instant};

struct Opts {
    corpus: Option<PathBuf>,
    seeds: u64,
    size: Size,
    family: String,
    stress: Option<StressCfg>,
    nixie: PathBuf,
    z3: Option<PathBuf>,
    cadical: Option<PathBuf>,
    timeout: Duration,
    artifacts: PathBuf,
    strict: bool,
}

fn parse_args() -> Result<Opts, String> {
    let env_or = |k: &str, d: &str| -> PathBuf {
        std::env::var(k)
            .ok()
            .map(PathBuf::from)
            .unwrap_or_else(|| d.into())
    };
    let mut o = Opts {
        corpus: None,
        seeds: 3,
        size: Size::Medium,
        family: "all".into(),
        stress: None,
        nixie: env_or("NIXIE_BIN", "target/release/nixie"),
        z3: std::env::var("Z3_BIN")
            .ok()
            .map(PathBuf::from)
            .or(Some("z3".into())),
        cadical: std::env::var("CADICAL_BIN").ok().map(PathBuf::from),
        timeout: Duration::from_millis(10_000),
        artifacts: PathBuf::from("obligation-artifacts"),
        strict: false,
    };
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--corpus" => {
                i += 1;
                o.corpus = Some(PathBuf::from(args.get(i).ok_or("--corpus needs a path")?));
            }
            "--seeds" => {
                i += 1;
                o.seeds = args
                    .get(i)
                    .and_then(|v| v.parse::<u64>().ok())
                    .ok_or("--seeds needs an integer")?;
            }
            "--size" => {
                i += 1;
                o.size = Size::parse(args.get(i).ok_or("--size needs a value")?)
                    .ok_or("--size needs small|medium|large")?;
            }
            "--family" => {
                i += 1;
                o.family = args.get(i).ok_or("--family needs a value")?.clone();
            }
            "--stress" => {
                i += 1;
                o.stress = Some(match args.get(i).map(|s| s.as_str()) {
                    Some("mild") => StressCfg::mild(),
                    Some("heavy") => StressCfg::heavy(),
                    _ => return Err("--stress needs mild|heavy".into()),
                });
            }
            "--nixie" => {
                i += 1;
                o.nixie = PathBuf::from(args.get(i).ok_or("--nixie needs a path")?);
            }
            "--z3" => {
                i += 1;
                o.z3 = Some(PathBuf::from(args.get(i).ok_or("--z3 needs a path")?));
            }
            "--no-z3" => o.z3 = None,
            "--cadical" => {
                i += 1;
                o.cadical = Some(PathBuf::from(args.get(i).ok_or("--cadical needs a path")?));
            }
            "--timeout-ms" => {
                i += 1;
                let ms = args
                    .get(i)
                    .and_then(|v| v.parse::<u64>().ok())
                    .ok_or("--timeout-ms needs an integer")?;
                o.timeout = Duration::from_millis(ms);
            }
            "--artifacts" => {
                i += 1;
                o.artifacts = PathBuf::from(args.get(i).ok_or("--artifacts needs a path")?);
            }
            "--strict" => o.strict = true,
            other => return Err(format!("unknown argument {other:?}")),
        }
        i += 1;
    }
    Ok(o)
}

enum RunOutcome {
    Done {
        code: Option<i32>,
        stdout: String,
        stderr: String,
    },
    Timeout,
}

/// Spawn, poll, kill-and-reap on timeout. Output of our instances is small
/// (well under pipe capacity), so reading after exit is safe.
fn run_with_timeout(cmd: &mut Command, timeout: Duration) -> Result<RunOutcome, String> {
    let mut child = cmd
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("spawn {}: {e}", cmd.get_program().to_string_lossy()))?;
    let deadline = Instant::now() + timeout;
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let mut stdout = String::new();
                let mut stderr = String::new();
                if let Some(mut h) = child.stdout.take() {
                    let _ = h.read_to_string(&mut stdout);
                }
                if let Some(mut h) = child.stderr.take() {
                    let _ = h.read_to_string(&mut stderr);
                }
                return Ok(RunOutcome::Done {
                    code: status.code(),
                    stdout,
                    stderr,
                });
            }
            Ok(None) => {}
            Err(e) => return Err(format!("wait: {e}")),
        }
        if Instant::now() >= deadline {
            let _ = child.kill();
            let _ = child.wait(); // reap
            return Ok(RunOutcome::Timeout);
        }
        std::thread::sleep(Duration::from_millis(15));
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Verdict {
    Pass,
    Fail,
    Unknown,
    Timeout,
    Crash,
    GenFail,
}

impl Verdict {
    fn name(self) -> &'static str {
        match self {
            Verdict::Pass => "pass",
            Verdict::Fail => "FAIL",
            Verdict::Unknown => "unknown",
            Verdict::Timeout => "timeout",
            Verdict::Crash => "CRASH",
            Verdict::GenFail => "GENFAIL",
        }
    }
}

fn parse_answers(stdout: &str) -> (Vec<Answer>, bool) {
    let mut answers = Vec::new();
    let mut saw_error = false;
    for line in stdout.lines() {
        let t = line.trim();
        if t.starts_with("(error") {
            saw_error = true;
            continue;
        }
        if let Some(a) = Answer::parse_line(t) {
            answers.push(a);
        }
    }
    (answers, saw_error)
}

fn compare(expected: &[Answer], got: &[Answer]) -> Verdict {
    if got.len() < expected.len() {
        // Fewer answers than queries: if the tail is 'unknown' the solver
        // gave up; treat missing answers as unknown.
        let g: Vec<Answer> = got
            .iter()
            .cloned()
            .chain(std::iter::repeat_n(
                Answer::Unknown,
                expected.len() - got.len(),
            ))
            .collect();
        return classify(expected, &g);
    }
    classify(expected, got)
}

fn classify(expected: &[Answer], got: &[Answer]) -> Verdict {
    if expected == got {
        return Verdict::Pass;
    }
    if got.contains(&Answer::Unknown) {
        Verdict::Unknown
    } else {
        Verdict::Fail
    }
}

fn main() -> ExitCode {
    let opts = match parse_args() {
        Ok(o) => o,
        Err(e) => {
            eprintln!("obligation-run: {e}");
            return ExitCode::FAILURE;
        }
    };

    // Assemble the instance list, either from a corpus dir or on the fly.
    let instances: Vec<Instance> = match &opts.corpus {
        Some(dir) => match load_corpus(dir) {
            Ok(v) => v,
            Err(e) => {
                eprintln!("obligation-run: {e}");
                return ExitCode::FAILURE;
            }
        },
        None => {
            let families: Vec<&str> = if opts.family == "all" {
                registry::FAMILIES.to_vec()
            } else {
                vec![opts.family.as_str()]
            };
            let mut v = Vec::new();
            for &f in &families {
                for seed in 0..opts.seeds {
                    match registry::generate_family(f, seed, opts.size, opts.stress.as_ref()) {
                        Ok(mut insts) => v.append(&mut insts),
                        Err(e) => {
                            eprintln!("obligation-run: {f} seed {seed}: {e}");
                            return ExitCode::FAILURE;
                        }
                    }
                }
            }
            v
        }
    };

    let tmp = std::env::temp_dir().join(format!("obligation-run-{}", std::process::id()));
    if let Err(e) = std::fs::create_dir_all(&tmp) {
        eprintln!("obligation-run: cannot create {}: {e}", tmp.display());
        return ExitCode::FAILURE;
    }
    let nixie_version = Command::new(&opts.nixie)
        .arg("--version")
        .output()
        .ok()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|| "unknown".into());
    println!(
        "nixie: {} ({}) | {} instances | timeout {:?}",
        opts.nixie.display(),
        nixie_version,
        instances.len(),
        opts.timeout
    );

    let mut per_family: std::collections::BTreeMap<
        String,
        std::collections::BTreeMap<&'static str, usize>,
    > = std::collections::BTreeMap::new();
    let mut bad = 0usize;
    let mut unknowns = 0usize;
    let mut timeouts = 0usize;

    for inst in &instances {
        let file = tmp.join(format!("{}.{}", inst.name, inst.extension()));
        if let Err(e) = std::fs::write(&file, &inst.script) {
            eprintln!("obligation-run: cannot write {}: {e}", file.display());
            return ExitCode::FAILURE;
        }
        // nixie: quiet keeps only result lines; --no-color keeps them clean.
        let mut cmd = Command::new(&opts.nixie);
        cmd.arg("-q").arg("--no-color").arg(&file);
        let verdict = match run_with_timeout(&mut cmd, opts.timeout) {
            Err(e) => {
                eprintln!("obligation-run: {}: {e}", inst.name);
                Verdict::Crash
            }
            Ok(RunOutcome::Timeout) => Verdict::Timeout,
            Ok(RunOutcome::Done {
                code,
                stdout,
                stderr,
            }) => {
                let (answers, saw_error) = parse_answers(&stdout);
                if code != Some(0) || saw_error {
                    eprintln!(
                        "[CRASH] {} rc={code:?}\n  stderr: {}",
                        inst.name,
                        stderr
                            .lines()
                            .take(6)
                            .collect::<Vec<_>>()
                            .join("\n         ")
                    );
                    Verdict::Crash
                } else {
                    let v = compare(&inst.expected, &answers);
                    if v == Verdict::Fail {
                        eprintln!(
                            "[FAIL] {}: expected {:?}, got {:?}",
                            inst.name,
                            inst.expected.iter().map(|a| a.name()).collect::<Vec<_>>(),
                            answers.iter().map(|a| a.name()).collect::<Vec<_>>()
                        );
                    }
                    v
                }
            }
        };

        // Generator self-check with Z3 (and CaDiCaL for CNF).
        let mut genfail = false;
        if let Some(z3) = &opts.z3 {
            let mut cmd = Command::new(z3);
            cmd.arg(&file);
            if let Ok(RunOutcome::Done {
                code: _,
                stdout,
                stderr: _,
            }) = run_with_timeout(&mut cmd, opts.timeout)
            {
                let (answers, saw_error) = parse_answers(&stdout);
                if saw_error {
                    eprintln!(
                        "[GENFAIL] {}: z3 rejected the instance: {}",
                        inst.name,
                        stdout
                            .lines()
                            .find(|l| l.trim().starts_with("(error"))
                            .unwrap_or("")
                    );
                    genfail = true;
                } else if answers != inst.expected && !answers.is_empty() {
                    eprintln!(
                        "[GENFAIL] {}: z3 says {:?}, certificate says {:?}",
                        inst.name,
                        answers.iter().map(|a| a.name()).collect::<Vec<_>>(),
                        inst.expected.iter().map(|a| a.name()).collect::<Vec<_>>()
                    );
                    genfail = true;
                }
            }
        }
        if matches!(inst.kind, nixie_obligation::InstanceKind::Cnf)
            && let Some(cad) = &opts.cadical
        {
            let mut cmd = Command::new(cad);
            cmd.arg(&file);
            if let Ok(RunOutcome::Done {
                code: _,
                stdout,
                stderr: _,
            }) = run_with_timeout(&mut cmd, opts.timeout)
            {
                let (answers, saw_error) = parse_answers(&stdout);
                if saw_error {
                    eprintln!("[GENFAIL] {}: cadical rejected the instance", inst.name);
                    genfail = true;
                } else if answers != inst.expected && !answers.is_empty() {
                    eprintln!(
                        "[GENFAIL] {}: cadical says {:?}, certificate says {:?}",
                        inst.name,
                        answers.iter().map(|a| a.name()).collect::<Vec<_>>(),
                        inst.expected.iter().map(|a| a.name()).collect::<Vec<_>>()
                    );
                    genfail = true;
                }
            }
        }

        let final_verdict = if genfail { Verdict::GenFail } else { verdict };
        match final_verdict {
            Verdict::Pass => {}
            Verdict::Unknown => unknowns += 1,
            Verdict::Timeout => timeouts += 1,
            Verdict::Fail | Verdict::Crash | Verdict::GenFail => {
                bad += 1;
                save_artifact(&opts.artifacts, inst, &file, final_verdict, &nixie_version);
            }
        }
        *per_family
            .entry(inst.family.to_string())
            .or_default()
            .entry(final_verdict.name())
            .or_insert(0) += 1;
        print!(
            "{}",
            if final_verdict == Verdict::Pass {
                "."
            } else {
                "!"
            }
        );
        use std::io::Write;
        let _ = std::io::stdout().flush();
    }
    println!();
    let _ = std::fs::remove_dir_all(&tmp);

    println!(
        "{:<12} {:>6} {:>6} {:>8} {:>8} {:>7} {:>8}",
        "family", "pass", "FAIL", "unknown", "timeout", "CRASH", "GENFAIL"
    );
    for (f, counts) in &per_family {
        println!(
            "{:<12} {:>6} {:>6} {:>8} {:>8} {:>7} {:>8}",
            f,
            counts.get("pass").copied().unwrap_or(0),
            counts.get("FAIL").copied().unwrap_or(0),
            counts.get("unknown").copied().unwrap_or(0),
            counts.get("timeout").copied().unwrap_or(0),
            counts.get("CRASH").copied().unwrap_or(0),
            counts.get("GENFAIL").copied().unwrap_or(0),
        );
    }
    println!(
        "\n{} bad, {} unknown, {} timeout(s) out of {} instances",
        bad,
        unknowns,
        timeouts,
        instances.len()
    );
    if bad > 0 || (opts.strict && (unknowns + timeouts) > 0) {
        println!("artifacts: {}", opts.artifacts.display());
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}

fn load_corpus(dir: &Path) -> Result<Vec<Instance>, String> {
    // Regenerate from manifest names is not possible without seeds in the
    // name — but names embed family/seed/size, so parse them back.
    let manifest = std::fs::read_to_string(dir.join("manifest.json"))
        .map_err(|e| format!("cannot read manifest: {e}"))?;
    let mut out = Vec::new();
    for line in manifest.lines() {
        let Some(rest) = line.trim().strip_prefix("\"file\": \"") else {
            continue;
        };
        let Some(file) = rest.strip_suffix("\",") else {
            let file = rest.strip_suffix('"').unwrap_or(rest);
            push_instance(dir, file, &mut out)?;
            continue;
        };
        push_instance(dir, file, &mut out)?;
    }
    if out.is_empty() {
        return Err("manifest contained no files".into());
    }
    Ok(out)
}

fn push_instance(dir: &Path, file: &str, out: &mut Vec<Instance>) -> Result<(), String> {
    let script =
        std::fs::read_to_string(dir.join(file)).map_err(|e| format!("cannot read {file}: {e}"))?;
    let stem = file.trim_end_matches(".smt2").trim_end_matches(".cnf");
    // Recompute the expected answers by regenerating from the name:
    // names are `family-variant-s<seed>-<size>`.
    let (family, seed, size) = parse_name(stem)?;
    let insts = registry::generate_family(family, seed, size, None)
        .map_err(|e| format!("regenerating {stem}: {e}"))?;
    let found = insts.into_iter().find(|i| i.name == stem);
    match found {
        Some(i) => out.push(Instance { script, ..i }),
        None => {
            // Stressed variants differ only in script; try with stress tags
            // by matching on family/seed/size and name prefix.
            return Err(format!(
                "manifest entry {stem} not reproducible without stress settings"
            ));
        }
    }
    Ok(())
}

fn parse_name(stem: &str) -> Result<(&'static str, u64, Size), String> {
    // ...-s<seed>-<size>
    let mut parts = stem.rsplit('-');
    let size_s = parts.next().ok_or("bad name")?;
    let seed_s = parts.next().ok_or("bad name")?;
    let size = Size::parse(size_s).ok_or(format!("bad size in {stem}"))?;
    let seed = seed_s
        .strip_prefix('s')
        .and_then(|s| s.parse::<u64>().ok())
        .ok_or(format!("bad seed in {stem}"))?;
    let family = stem.split('-').next().ok_or("bad name")?;
    let fam = registry::FAMILIES
        .iter()
        .find(|f| **f == family)
        .ok_or(format!("unknown family in {stem}"))?;
    Ok((fam, seed, size))
}

fn save_artifact(
    dir: &Path,
    inst: &Instance,
    source: &Path,
    verdict: Verdict,
    nixie_version: &str,
) {
    if std::fs::create_dir_all(dir).is_err() {
        return;
    }
    let _ = std::fs::copy(
        source,
        dir.join(format!("{}.{}", inst.name, inst.extension())),
    );
    let _ = std::fs::write(
        dir.join(format!("{}.verdict.json", inst.name)),
        format!(
            "{{\n  \"name\": \"{}\",\n  \"verdict\": \"{}\",\n  \"expected\": [{}],\n  \"certificate\": \"{}\",\n  \"nixie_version\": \"{}\"\n}}\n",
            inst.name,
            verdict.name(),
            inst.expected
                .iter()
                .map(|a| format!("\"{}\"", a.name()))
                .collect::<Vec<_>>()
                .join(", "),
            inst.certificate
                .replace('\\', "\\\\")
                .replace('"', "\\\"")
                .replace('\n', "\\n"),
            nixie_version,
        ),
    );
    let _ = std::fs::write(
        dir.join(format!("{}.meta.json", inst.name)),
        inst.meta_json(),
    );
}
