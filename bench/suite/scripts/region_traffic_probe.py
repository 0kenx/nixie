#!/usr/bin/env python3
"""Run the registered three-cell structured-region traffic census.

Build stats_solve with bcp-regions and cache it at the committed source SHA.
Reuses all controls; never runs a new baseline or repeats an existing cell.
"""
import argparse
import datetime
import fcntl
import json
import os
import platform
import re
import subprocess
from pathlib import Path

import benchstore
import watch_group_probe as common

SUITE = "structured-region-traffic"


def checked_report(report):
    assert report["schema"] == "nixie-region-traffic/1"
    counts, bins = report["counts"], report["by_conflicts"]
    assert len(counts) == 2 and all(len(ch) == 10 for ch in counts)
    assert len(bins) == 3 and all(len(b) == 2 for b in bins)
    for channel, classes in enumerate(counts):
        for cls, metrics in enumerate(classes):
            assert len(metrics) == 6 and all(type(n) is int and n >= 0 for n in metrics)
            visits, hits, payload, scans, props, conflicts = metrics
            assert sum(b[channel][cls] for b in bins) == visits
            if channel == 0:
                assert hits + props + conflicts == visits and payload == scans == 0
            else:
                assert hits + payload == visits and props + conflicts <= payload
    assert report["samples"] == (report["triggers"] + report["stride"] - 1) // report["stride"]
    return sum(row[0] for channel in counts for row in channel)


def fraction(a, b):
    return a / b if b else None


def summarize(r, report):
    total = checked_report(report)
    counts, bins = report["counts"], report["by_conflicts"]
    visits = [sum(row[0] for row in ch) for ch in counts]
    covered = [ch[0][0] for ch in counts]
    late = sum(sum(ch) for ch in bins[2])
    late_covered = sum(ch[0] for ch in bins[2])
    scan_total = sum(row[3] for row in counts[1])
    row = dict(instance=r["instance"]["name"], record_id=r["record_id"],
               control_record_id=r["observations"]["control_record_id"],
               stdout_identical=r["observations"]["stdout_identical"],
               sampled_visits=total, region_fraction=fraction(sum(covered), total),
               late_region_fraction=fraction(late_covered, late),
               binary_region_fraction=fraction(covered[0], visits[0]),
               long_region_fraction=fraction(covered[1], visits[1]),
               scan_region_fraction=fraction(counts[1][0][3], scan_total),
               reported_answer=r["observations"]["reported_answer"],
               conflicts=r["observations"]["conflicts"], observations=report)
    row["passes_gate"] = (row["stdout_identical"] and total > 0 and late > 0
                          and 4 * sum(covered) >= total and 4 * late_covered >= late)
    return row


def run(args, name, cnf, cap, control):
    flags = dict(cpu=2, seed=1, max_conflicts=cap, stride=256, profile="release",
                 preset="CaDiCaL", measurement="certified-snapshot-regions-v1",
                 snapshot_limit=2_000_000, minimum_component_gates=4,
                 emergency_timeout_s=300, print_model=True)
    command = ["taskset", "-c", "2", str(args.binary), str(cnf)]
    r = dict(schema=benchstore.SCHEMA, suite=SUITE,
             created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
             host=dict(id=platform.node(), cpu=platform.machine(), os=platform.platform()),
             git=dict(sha_long=args.sha, sha_short=args.sha[:7], dirty=False),
             binary=dict(path=str(args.binary), sha256=common.digest(args.binary)),
             instance=dict(name=name, family=name, sha256=common.digest(cnf)),
             config=dict(id="observation", flags=flags, features=["bcp-regions"], cmdline=command),
             seed=1, arm=dict(role="treatment"))
    r["config_hash"] = benchstore.canonical_flags(flags)
    dest = benchstore.record_path(common.STORE, r)
    if dest.exists():
        prior = json.loads(dest.read_text())
        benchstore.validate(prior)
        assert benchstore.canonical_join_key(prior) == benchstore.canonical_join_key(r)
        print("reuse", name, flush=True)
        return prior
    raw = common.STORE / args.sha[:7] / "benchmark" / SUITE / ("c" + r["config_hash"])
    raw.mkdir(parents=True, exist_ok=True)
    prefix = raw / name
    started = Path(str(prefix) + ".started.json")
    assert not started.exists(), f"incomplete prior recording: {started}"
    with started.open("x") as f:
        json.dump(r, f, indent=2)
    env = {k: v for k, v in os.environ.items() if not k.startswith((
        "NIXIE_", "ELS", "FACTOR", "NO_", "MAXC", "SEED", "INPROC", "STAB_",
        "REPHASE", "WALK", "RANDPOL", "PRINT_MODEL", "PHASE_HINT", "GATE_COUNT", "SCC_MASS"))}
    env.update(MAXC=str(cap), SEED="1", PRINT_MODEL="1", NIXIE_REGION_STATS="256", LC_ALL="C")
    stdout, stderr = Path(str(prefix) + ".stdout"), Path(str(prefix) + ".stderr")
    print("start", name, flush=True)
    with stdout.open("w") as out, stderr.open("w") as err:
        result = subprocess.run(command, env=env, stdout=out, stderr=err, timeout=300)
    assert result.returncode == 0, stderr.read_text()[-2000:]
    text = stdout.read_text()
    answer = re.search(r"^result=(\w+)", text, re.M)
    conflicts = re.search(r"^conflicts=(\d+)", text, re.M)
    assert answer and conflicts
    answer = answer.group(1).lower()
    checked = answer == "sat"
    if checked:
        common.check_model(cnf, text)
    reports = [json.loads(line) for line in stderr.read_text().splitlines()
               if line.startswith('{"schema":"nixie-region-traffic/1"')]
    assert len(reports) == 1
    report = reports[0]
    assert report["stride"] == 256
    total = checked_report(report)
    assert total > 0
    r.update(observations=dict(stdout=str(stdout), stderr=str(stderr), reported_answer=answer,
                               conflicts=int(conflicts.group(1)), control_record_id=control["record_id"],
                               stdout_identical=stdout.read_bytes() == Path(control["observations"]["stdout"]).read_bytes()),
             metrics=dict(primary=dict(name="sampled_clause_visits", value=total),
                          secondary=report, counter_coverage_verified=True),
             verdict=dict(answer=answer if checked else "unknown", verified_model_or_proof=checked))
    r["record_id"] = benchstore.record_id(r)
    benchstore.validate(r)
    dest.parent.mkdir(parents=True, exist_ok=True)
    with dest.open("x") as f:
        json.dump(r, f, indent=2, sort_keys=True)
        f.write("\n")
    print("done", name, answer, conflicts.group(1), flush=True)
    return r


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--binary", required=True, type=lambda p: Path(p).resolve())
    p.add_argument("--sha", required=True)
    p.add_argument("--root", type=lambda p: Path(p).resolve(), default=common.ROOT)
    args = p.parse_args()
    common.ROOT = args.root
    common.STORE = args.root / "precompile"
    common.CONTROL_BINARY = common.STORE / common.CONTROL_SHA / "stats_solve"
    args.sha = common.full_sha(args.sha)
    assert common.full_sha("HEAD") == args.sha
    assert not subprocess.check_output(["git", "status", "--porcelain"], cwd=args.root)
    circuits = sorted((args.root / "satcomp2024/bench").glob("*circuit*.cnf"))
    assert len(circuits) == 1
    files = [("break_unsat_06_07", args.root / "nixie-sat/tests/fixtures/break_unsat_06_07.cnf", 10_000_000, "50fa8316e92aed2a"),
             ("circuit_48in64out", circuits[0], 10_000_000, "a6b0151744a458c1"),
             ("noL_11_14", args.root / "nixie-sat/tests/fixtures/noL_11_14.cnf", 100_000, "4e70e8d19a55d4c0")]
    controls = [common.cached_control(n, f, cap, 1) for n, f, cap, _ in files]
    assert all(c is not None and c["record_id"] == expected
               for c, (_, _, _, expected) in zip(controls, files)), "registered controls must already exist"
    out = common.STORE / args.sha[:7] / "benchmark" / SUITE
    out.mkdir(parents=True, exist_ok=True)
    with (out / "measurement.lock").open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        manifest = dict(suite=SUITE, source=args.sha, binary_sha256=common.digest(args.binary),
                        host=platform.node(), seed=1, stride=256, cpu=2,
                        cells=[dict(instance=n, path=str(f), sha256=common.digest(f), cap=cap, control=cid)
                               for n, f, cap, cid in files])
        (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
        summary = []
        for (name, cnf, cap, _), control in zip(files, controls):
            r = run(args, name, cnf, cap, control)
            row = summarize(r, r["metrics"]["secondary"])
            summary.append(row)
            (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
            print(json.dumps({k: v for k, v in row.items() if k != "observations"}), flush=True)
            assert row["stdout_identical"], "observation changed solver diagnostics"
        (out / "verdict.json").write_text(json.dumps(dict(passes_screen=sum(r["passes_gate"] for r in summary) >= 2), indent=2) + "\n")


if __name__ == "__main__":
    main()
