#!/usr/bin/env python3
"""Four-cell screen for the registered watch-tile kernel; reuse eager controls."""

import argparse
import datetime
import fcntl
import hashlib
import json
import math
import os
import platform
import re
import subprocess
from pathlib import Path

import benchstore
from watch_group_probe import check_model

SOURCE = Path(__file__).resolve().parents[3]
SUITE = "watch-tile-prototype"
EVENTS = ["instructions:u", "cycles:u", "branches:u", "branch-misses:u"]
CONTROL_IDS = {"break_unsat_06_07": "50fa8316e92aed2a", "circuit_48in64out": "a6b0151744a458c1"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_perf(text):
    values = {}
    for line in text.splitlines():
        if not line or line.startswith("#"):
            continue
        fields = line.split(";")
        if len(fields) < 5:
            continue
        event = fields[2].removeprefix("cpu_core/").removeprefix("cpu_atom/").removesuffix("/u").removesuffix(":u")
        if event not in {e.removesuffix(":u") for e in EVENTS}:
            continue
        if fields[0] == "<not counted>" and fields[2].startswith("cpu_atom/"):
            # CPU 2 is a core PMU CPU; the inactive atom PMU is expected.
            continue
        assert fields[0].isdigit(), f"invalid PMU counter: {line}"
        assert float(fields[4]) == 100.0, f"multiplexed PMU counter: {line}"
        assert event not in values, f"multiple active PMUs for {event}"
        values[event] = int(fields[0])
    assert set(values) == {e.removesuffix(":u") for e in EVENTS}
    assert all(v > 0 for v in values.values())
    return values


def control(root, name, cnf):
    matches = []
    for p in (root / "precompile/219bed6/benchmark/runs/mode-matched-throughput").glob(name + "__*__s1.json"):
        r = json.loads(p.read_text())
        if r["record_id"] == CONTROL_IDS[name]:
            benchstore.validate(r)
            assert benchstore.record_id(r) == r["record_id"]
            assert r["host"]["id"] == platform.node() and r["instance"]["sha256"] == digest(cnf)
            assert r["config"]["flags"]["cpu"] == 2 and r["seed"] == 1
            assert r["config"]["flags"]["max_conflicts"] == 10_000_000
            assert r["config"]["flags"]["pmu"] == EVENTS
            assert r["binary"]["sha256"] == "76a883a819c437d1e8dd4c43828975b860212027b13554219f4b8f5cde119332"
            matches.append(r)
    assert len(matches) == 1, f"missing registered control: {name}"
    return matches[0]


def cell_flags(mode):
    flags = dict(cpu=2, max_conflicts=10_000_000, emergency_timeout_s=900,
                 profile="release", solver_options=["CaDiCaL-preset"], tile_width=64,
                 min_tile=16, min_group=4, rebuild_edits=64, mode=mode, print_model=True)
    if mode == "optimized":
        flags["pmu"] = EVENTS
    return flags


def run(args, name, cnf, mode, base):
    binary = args.optimized if mode == "optimized" else args.diagnostic
    flags = cell_flags(mode)
    rec = dict(schema=benchstore.SCHEMA, suite=SUITE,
               created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
               host=dict(id=platform.node(), cpu=platform.machine(), os=platform.platform()),
               git=dict(sha_long=args.sha, sha_short=args.sha[:7], dirty=False),
               binary=dict(path=str(binary), sha256=digest(binary)),
               instance=dict(name=name, sha256=digest(cnf), family=name), seed=1,
               config=dict(id=mode, flags=flags, features=["bcp-tiles" if mode == "optimized" else "bcp-tiles-stats"]),
               arm=dict(role="treatment"))
    rec["config_hash"] = benchstore.canonical_flags(flags)
    dest = benchstore.record_path(args.root / "precompile", rec)
    if dest.exists():
        old = json.loads(dest.read_text())
        benchstore.validate(old)
        assert benchstore.canonical_join_key(old) == benchstore.canonical_join_key(rec)
        print("reuse", mode, name, flush=True)
        return old
    raw = args.root / "precompile" / args.sha[:7] / "benchmark" / SUITE / ("c" + rec["config_hash"])
    raw.mkdir(parents=True, exist_ok=True)
    prefix = raw / name
    started = prefix.with_suffix(".started.json")
    assert not started.exists(), f"inspect incomplete recording: {started}"
    stdout_path, stderr_path, perf_path = [prefix.with_suffix(s) for s in [".stdout", ".stderr", ".perf"]]
    command = ["taskset", "-c", "2"]
    if mode == "optimized":
        command += ["perf", "stat", "-x", ";", "-o", str(perf_path), "-e", ",".join(EVENTS), "--"]
    command += [str(binary), str(cnf)]
    rec["config"]["cmdline"] = command
    started.write_text(json.dumps(rec, indent=2) + "\n")
    env = {k: v for k, v in os.environ.items() if not k.startswith((
        "NIXIE_", "ELS", "FACTOR", "NO_", "MAXC", "SEED", "INPROC", "STAB_",
        "REPHASE", "WALK", "RANDPOL", "PRINT_MODEL", "PHASE_HINT", "GATE_COUNT", "SCC_MASS"))}
    env.update(MAXC="10000000", SEED="1", PRINT_MODEL="1", LC_ALL="C", NIXIE_WATCH_TILES="1")
    print("start", mode, name, flush=True)
    with stdout_path.open("w") as out, stderr_path.open("w") as err:
        result = subprocess.run(command, env=env, stdout=out, stderr=err, timeout=900)
    assert result.returncode == 0, stderr_path.read_text()[-3000:]
    stdout = stdout_path.read_text()
    answer = re.search(r"^result=(\w+)", stdout, re.M)
    conflicts = re.search(r"^conflicts=(\d+)", stdout, re.M)
    assert answer and conflicts
    answer, conflicts = answer.group(1).lower(), int(conflicts.group(1))
    checked = answer == "sat"
    if checked:
        check_model(cnf, stdout)
    same = stdout_path.read_bytes() == Path(base["observations"]["stdout"]).read_bytes()
    obs = dict(stdout=str(stdout_path), stderr=str(stderr_path), reported_answer=answer,
               conflicts=conflicts, stdout_identical=same, control_record_id=base["record_id"])
    if mode == "optimized":
        counts = parse_perf(perf_path.read_text())
        obs["perf"] = str(perf_path)
        secondary = dict(counts, conflicts=conflicts, cycles_per_conflict=counts["cycles"] / conflicts,
                         instructions_per_conflict=counts["instructions"] / conflicts)
        primary = dict(name="instructions", value=counts["instructions"])
    else:
        reports = [json.loads(line) for line in stderr_path.read_text().splitlines()
                   if line.startswith('{"schema":"nixie-watch-tiles/1"')]
        assert len(reports) == 1 and reports[0]["skipped"] > 0
        secondary = reports[0]
        primary = dict(name="logical_watch_visits", value=secondary["scalar_visits"] + secondary["skipped"])
    rec.update(observations=obs,
               metrics=dict(primary=primary, secondary=secondary, counter_coverage_verified=True),
               verdict=dict(answer=answer if checked else "unknown", verified_model_or_proof=checked))
    rec["record_id"] = benchstore.record_id(rec)
    benchstore.validate(rec)
    dest.parent.mkdir(parents=True, exist_ok=True)
    with dest.open("x") as f:
        json.dump(rec, f, indent=2, sort_keys=True)
        f.write("\n")
    print("done", mode, name, rec["record_id"], "stdout_identical", same, flush=True)
    assert same, "kernel changed search diagnostics; recorded and stopped"
    return rec


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", type=Path, default=SOURCE, help="primary checkout containing shared data/cache")
    ap.add_argument("--sha", required=True)
    ap.add_argument("--optimized", type=Path, required=True)
    ap.add_argument("--diagnostic", type=Path, required=True)
    args = ap.parse_args()
    args.root, args.optimized, args.diagnostic = [p.resolve() for p in [args.root, args.optimized, args.diagnostic]]
    args.sha = subprocess.check_output(["git", "rev-parse", args.sha], cwd=SOURCE, text=True).strip()
    assert args.sha == subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=SOURCE, text=True).strip()
    assert not subprocess.check_output(["git", "status", "--porcelain"], cwd=SOURCE), "commit before measuring"
    circuit = list((args.root / "satcomp2024/bench").glob("*circuit*.cnf"))
    assert len(circuit) == 1
    files = {"break_unsat_06_07": args.root / "nixie-sat/tests/fixtures/break_unsat_06_07.cnf",
             "circuit_48in64out": circuit[0]}
    out = args.root / "precompile" / args.sha[:7] / "benchmark" / SUITE
    out.mkdir(parents=True, exist_ok=True)
    with (out / "measurement.lock").open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        manifest = dict(suite=SUITE, host=platform.node(), seeds=[1],
                        configs=[dict(id=m, flags=cell_flags(m)) for m in ["optimized", "diagnostic"]],
                        instances=[dict(name=n, path=str(p)) for n, p in files.items()],
                        optimized_sha256=digest(args.optimized), diagnostic_sha256=digest(args.diagnostic),
                        registration="docs/studies/2026-09-07-watch-tiles-prototype.md")
        (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
        summary = []
        for name, cnf in files.items():
            base = control(args.root, name, cnf)
            opt = run(args, name, cnf, "optimized", base)
            diag = run(args, name, cnf, "diagnostic", base)
            om, bm = opt["metrics"]["secondary"], base["metrics"]["secondary"]
            counts = diag["metrics"]["secondary"]
            row = dict(instance=name, control_record_id=base["record_id"], optimized_record_id=opt["record_id"],
                       diagnostic_record_id=diag["record_id"], stdout_identical=True,
                       conflicts=om["conflicts"], instruction_ratio=om["instructions"] / base["metrics"]["primary"]["value"],
                       cycle_ratio=om["cycles"] / bm["cycles"],
                       skipped_fraction=counts["skipped"] / (counts["skipped"] + counts["scalar_visits"]),
                       diagnostic=counts)
            summary.append(row)
            (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
            print(json.dumps({k: v for k, v in row.items() if k != "diagnostic"}), flush=True)
        ratio = math.exp(sum(math.log(r["instruction_ratio"]) for r in summary) / len(summary))
        verdict = dict(instruction_geomean=ratio, passes_screen=ratio <= .95 and all(r["instruction_ratio"] <= 1.05 for r in summary))
        (out / "verdict.json").write_text(json.dumps(verdict, indent=2) + "\n")
        print(json.dumps(verdict), flush=True)


if __name__ == "__main__":
    main()
