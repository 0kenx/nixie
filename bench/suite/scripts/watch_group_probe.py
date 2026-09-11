#!/usr/bin/env python3
"""Run the registered shared-blocker observation panel, reusing cached controls.

Build cnf_solve with --features bcp-groups, cache it at its source commit,
then pass --binary and --sha. The observed runs need DIAG=1 (set by this
script) for the stats_solve-style diagnostics stdout the controls were
recorded with. Observed timings are NOT throughput estimates.
See docs/studies/2026-09-07-nixie-propagation-redesign.md.
"""

import argparse
import datetime
import fcntl
import hashlib
import json
import os
import platform
import re
import subprocess
from pathlib import Path

import benchstore

ROOT = Path(__file__).resolve().parents[3]
STORE = ROOT / "precompile"
CONTROL_SHA = "eb3a62d"
CONTROL_BINARY = STORE / CONTROL_SHA / "stats_solve"
SUITE = "shared-satisfaction-probe"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def full_sha(sha):
    return subprocess.check_output(["git", "rev-parse", sha], cwd=ROOT, text=True).strip()


def check_model(cnf, stdout):
    model = {}
    for line in stdout.splitlines():
        if not line.startswith("v "):
            continue
        for token in line.split()[1:]:
            lit = int(token)
            if lit:
                assert abs(lit) not in model or model[abs(lit)] == (lit > 0), "contradictory model"
                model[abs(lit)] = lit > 0
    clause, count, header = [], 0, None
    for line in cnf.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith(("c", "%")):
            continue
        if line.startswith("p "):
            _, kind, nvars, nclauses = line.split()
            assert kind == "cnf" and header is None
            header = (int(nvars), int(nclauses))
            continue
        for token in line.split():
            lit = int(token)
            if lit:
                clause.append(lit)
            else:
                assert any(model.get(abs(v)) == (v > 0) for v in clause), "unsatisfied original clause"
                clause.clear()
                count += 1
    assert not clause and header is not None and count == header[1]
    assert all(0 < v <= header[0] for v in model)


def cached_control(name, cnf, cap, seed):
    binary_hash = digest(CONTROL_BINARY)
    input_hash = digest(cnf)
    for path in STORE.glob(f"*/benchmark/runs/*/{benchstore.slug(name)}__*__s{seed}.json"):
        r = json.loads(path.read_text())
        if (r["binary"]["sha256"] == binary_hash
                and r["instance"]["sha256"] == input_hash
                and r["host"]["id"] == platform.node()
                and r["config"]["flags"].get("max_conflicts") == cap
                and "stdout" in r.get("observations", {})):
            flags = r["config"]["flags"]
            if flags.get("stride", 0) == 0 and r["config"]["id"] == "candidate-eager-final":
                benchstore.validate(r)
                assert r["record_id"] == benchstore.record_id(r)
                return r
            if r["suite"] == SUITE and flags.get("stride") == 0:
                benchstore.validate(r)
                assert r["record_id"] == benchstore.record_id(r)
                return r
    return None


def cell_flags(args, cap, observed):
    return dict(cpu=args.cpu, max_conflicts=cap, stride=args.stride if observed else 0,
                 emergency_timeout_s=300, profile="release", preset="CaDiCaL",
                 measurement="sampled-watch-lists-v1", print_model=True)


def run_cell(args, name, cnf, cap, observed, control=None):
    binary = args.binary if observed else CONTROL_BINARY
    sha = full_sha(args.sha if observed else CONTROL_SHA)
    flags = cell_flags(args, cap, observed)
    r = dict(schema=benchstore.SCHEMA,
             created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), suite=SUITE,
             host=dict(id=platform.node(), cpu=platform.machine(), os=platform.platform()),
             git=dict(sha_long=sha, sha_short=sha[:7], dirty=False),
             binary=dict(path=str(binary), sha256=digest(binary)),
             instance=dict(name=name, sha256=digest(cnf), family=name),
             config=dict(id="observation" if observed else "control", flags=flags,
                         features=["bcp-groups"] if observed else []), seed=args.seed,
             arm=dict(role="treatment" if observed else "baseline"))
    r["config_hash"] = benchstore.canonical_flags(flags)
    dest = benchstore.record_path(STORE, r)
    if dest.exists():
        prior = json.loads(dest.read_text())
        benchstore.validate(prior)
        assert benchstore.canonical_join_key(prior) == benchstore.canonical_join_key(r)
        print("reuse", r["config"]["id"], name, args.seed, flush=True)
        return prior
    raw = STORE / sha[:7] / "benchmark" / SUITE / ("c" + r["config_hash"])
    raw.mkdir(parents=True, exist_ok=True)
    prefix = raw / f"{name}.s{args.seed}"
    started_path = Path(str(prefix) + ".started.json")
    assert not started_path.exists(), f"incomplete prior recording: inspect {started_path}"
    command = ["taskset", "-c", str(args.cpu), str(binary), str(cnf)]
    r["config"]["cmdline"] = command
    started_path.write_text(json.dumps(r, indent=2) + "\n")
    env = {k: v for k, v in os.environ.items() if not k.startswith((
        "NIXIE_", "ELS", "FACTOR", "NO_", "MAXC", "SEED", "INPROC", "STAB_",
        "REPHASE", "WALK", "RANDPOL", "PRINT_MODEL", "PHASE_HINT", "GATE_COUNT", "SCC_MASS"))}
    env.update(MAXC=str(cap), SEED=str(args.seed), DIAG="1", PRINT_MODEL="1", LC_ALL="C")
    if observed:
        env["NIXIE_WATCH_GROUPS"] = str(args.stride)
    stdout_path, stderr_path = Path(str(prefix) + ".stdout"), Path(str(prefix) + ".stderr")
    print("start", r["config"]["id"], name, args.seed, flush=True)
    with stdout_path.open("w") as out, stderr_path.open("w") as err:
        result = subprocess.run(command, env=env, stdout=out, stderr=err, timeout=300)
    assert result.returncode == 0, stderr_path.read_text()[-2000:]
    stdout = stdout_path.read_text()
    answer = re.search(r"^result=(\w+)", stdout, re.M)
    conflicts = re.search(r"^conflicts=(\d+)", stdout, re.M)
    assert answer and conflicts, "missing solver result/counters"
    answer = answer.group(1).lower()
    checked = answer == "sat"
    if checked:
        check_model(cnf, stdout)
    obs = dict(stdout=str(stdout_path), stderr=str(stderr_path), reported_answer=answer,
               conflicts=int(conflicts.group(1)))
    if observed:
        reports = [json.loads(line) for line in stderr_path.read_text().splitlines()
                   if line.startswith('{"schema":"nixie-watch-groups/1"')]
        assert len(reports) == 1, "expected exactly one complete observation report"
        report = reports[0]
        assert report["stride"] == args.stride and report["visited"] > 0
        assert report["duplicate_entry_true"] == report["entry_true"] - report["entry_true_groups"]
        assert sum(report["group_entries"]) == report["entry_true"]
        assert sum(row[0] for row in report["by_conflicts"]) == report["visited"]
        report_path = Path(str(prefix) + ".groups.json")
        report_path.write_text(json.dumps(report, indent=2) + "\n")
        obs.update(report=str(report_path), control_record_id=control["record_id"],
                   stdout_identical=stdout_path.read_bytes() == Path(control["observations"]["stdout"]).read_bytes())
        primary = dict(name="sampled_visited_watch_entries", value=report["visited"])
        secondary = report.copy()
    else:
        primary = dict(name="conflicts", value=obs["conflicts"])
        secondary = {}
    r.update(observations=obs, metrics=dict(primary=primary, secondary=secondary,
                                           counter_coverage_verified=True),
             verdict=dict(answer=answer if checked else "unknown", verified_model_or_proof=checked))
    r["record_id"] = benchstore.record_id(r)
    benchstore.validate(r)
    dest.parent.mkdir(parents=True, exist_ok=True)
    with dest.open("x") as f:
        json.dump(r, f, indent=2, sort_keys=True)
        f.write("\n")
    print("done", r["config"]["id"], name, answer, obs["conflicts"], flush=True)
    return r


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--binary", required=True, type=lambda p: Path(p).resolve())
    ap.add_argument("--sha", required=True)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--stride", type=int, default=256)
    ap.add_argument("--cpu", type=int, default=2)
    ap.add_argument("--only", nargs="+", choices=["break_unsat_06_07", "circuit_48in64out", "noL_11_14"])
    args = ap.parse_args()
    assert args.stride > 0 and args.seed >= 0
    assert full_sha(args.sha) == full_sha("HEAD"), "run the committed source being recorded"
    assert not subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT), "commit before measuring"
    circuit = sorted((ROOT / "satcomp2024/bench").glob("*circuit*.cnf"))
    assert len(circuit) == 1
    files = {"break_unsat_06_07": (ROOT / "nixie-sat/tests/fixtures/break_unsat_06_07.cnf", 10_000_000),
             "circuit_48in64out": (circuit[0], 10_000_000),
             "noL_11_14": (ROOT / "nixie-sat/tests/fixtures/noL_11_14.cnf", 100_000)}
    if args.only:
        files = {k: v for k, v in files.items() if k in args.only}
    out = STORE / full_sha(args.sha)[:7] / "benchmark" / SUITE
    out.mkdir(parents=True, exist_ok=True)
    with (out / "measurement.lock").open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        manifest = dict(suite=SUITE, host=platform.node(), seeds=[args.seed],
                        instances=[dict(name=n, path=str(p), cap=cap) for n, (p, cap) in files.items()],
                        binary_sha256=digest(args.binary), stride=args.stride, cpu=args.cpu)
        (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
        for name, (cnf, cap) in files.items():
            cell_manifest = dict(suite=SUITE, host=platform.node(), seeds=[args.seed],
                                 instances=[dict(name=name, path=str(cnf))],
                                 configs=[dict(id="observation", flags=cell_flags(args, cap, True))])
            (out / f"{name}.manifest.json").write_text(json.dumps(cell_manifest, indent=2) + "\n")
        summary = []
        for name, (cnf, cap) in files.items():
            control = cached_control(name, cnf, cap, args.seed)
            if control is None:
                assert name == "noL_11_14", "registration allows only one new noL control"
                control = run_cell(args, name, cnf, cap, False)
            r = run_cell(args, name, cnf, cap, True, control)
            report = json.loads(Path(r["observations"]["report"]).read_text())
            row = dict(instance=name, record_id=r["record_id"], control_record_id=control["record_id"],
                       stdout_identical=r["observations"]["stdout_identical"],
                       coverage_complete=report["skipped_lists"] == 0 and report["history_skipped"] == 0,
                       duplicate_fraction=report["duplicate_entry_true"] / report["visited"],
                       large_group_fraction=report["large_group_entries"] / report["visited"],
                       observations=report)
            row["passes_opportunity_gate"] = (row["coverage_complete"] and row["stdout_identical"]
                                              and row["duplicate_fraction"] >= .30
                                              and row["large_group_fraction"] >= .20)
            summary.append(row)
            (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
            print(json.dumps({k: v for k, v in row.items() if k != "observations"}), flush=True)
            assert row["stdout_identical"], "observation changed solver diagnostics"


if __name__ == "__main__":
    main()
