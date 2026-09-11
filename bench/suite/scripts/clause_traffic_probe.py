#!/usr/bin/env python3
"""Registered two-input clause-cost census. Reuse controls, never repeat cells.

The observed runs need the clause-traffic build of cnf_solve (build with
`cargo build --release -p nixie-sat --example cnf_solve --features
clause-traffic`, cache as precompile/<sha>/cnf_solve-traffic) and set
DIAG=1 (this script does) for the stats_solve-style stdout the controls
were recorded with.
Instrumented timings do not measure throughput. See the registered protocol
in docs/studies/2026-09-08-learned-clause-traffic.md.
"""
import argparse
import datetime
import json
import os
from pathlib import Path
import platform
import re
import signal
import subprocess
import time

import benchstore
from watch_group_probe import check_model, digest

SUITE = "learned-clause-traffic"
METRICS = ["visits", "hits", "payloads", "scans", "units", "conflicts", "first_uip"]


def counts(row):
    return [sum(ch[i] for ch in row["counts"]) for i in range(7)]


def work(row):
    return sum(ch[2] + ch[3] for ch in row["counts"])


def direct_use(row):
    return sum(sum(ch[4:7]) for ch in row["counts"])


def summarize(report):
    assert report["schema"] == "nixie-clause-traffic/1"
    assert report["epoch_conflicts"] == 4096
    assert not report["overflow"]
    assert not any(v for ch in report["omitted"] for v in ch), "incomplete observation coverage"
    rows = report["rows"]
    by_epoch, by_id = {}, {}
    strata = {name: {} for name in ("tier", "glue", "length")}
    totals = [0] * 7
    for row in rows:
        assert len(row["counts"]) == 2 and all(len(ch) == 7 for ch in row["counts"])
        assert all(isinstance(v, int) and 0 <= v < 2**64 for ch in row["counts"] for v in ch)
        assert row["epoch"] <= report["elapsed_conflicts"] // 4096
        epoch = by_epoch.setdefault(row["epoch"], {})
        assert row["id"] not in epoch, "duplicate clause/epoch"
        epoch[row["id"]] = row
        c = counts(row)
        totals = [a + b for a, b in zip(totals, c)]
        acc = by_id.setdefault(row["id"], [0] * 7)
        by_id[row["id"]] = [a + b for a, b in zip(acc, c)]
        for name in strata:
            key = str(row[name])
            acc = strata[name].setdefault(key, dict(rows=0, work=0, direct_use=0))
            acc["rows"] += 1
            acc["work"] += work(row)
            acc["direct_use"] += direct_use(row)
    complete = report["elapsed_conflicts"] // 4096
    pairs = []
    for e in range(max(0, complete - 1)):
        previous, future = by_epoch.get(e, {}), by_epoch.get(e + 1, {})
        if not previous or not future:
            continue
        selected = sorted(previous, key=lambda cid: (-work(previous[cid]), cid))[:max(1, len(previous) // 4)]
        future_work = sum(map(work, future.values()))
        if not future_work:
            continue
        present = [future[cid] for cid in selected if cid in future]
        absent = [previous[cid] for cid in selected if cid not in future]
        top_work = sum(map(work, present))
        zero_use_work = sum(work(row) for row in present if direct_use(row) == 0)
        pairs.append(dict(previous_epoch=e, next_epoch=e + 1,
                          prior_clauses=len(previous), selected=len(selected),
                          selected_with_future_rows=len(present), missing_future_rows=len(absent),
                          missing_future_deleted_at_end=sum(row["final_status"] == "deleted" for row in absent),
                          future_work=future_work, top_future_work=top_work,
                          top_future_zero_direct_use_work=zero_use_work,
                          top_future_fraction=top_work / future_work,
                          top_future_zero_direct_use_fraction=zero_use_work / future_work))
    clause_work = sorted((c[2] + c[3] for c in by_id.values()), reverse=True)
    total_work = sum(clause_work)
    zero_use_work = sum(c[2] + c[3] for c in by_id.values() if sum(c[4:7]) == 0)
    passing = sum(p["top_future_zero_direct_use_fraction"] >= .25 for p in pairs)
    return dict(sampled_clause_epoch_rows=len(rows), sampled_learned_clauses=len(by_id),
                learned_counts=dict(zip(METRICS, totals)), total_work=total_work,
                work_without_observed_direct_use=zero_use_work,
                top_tenth_work=sum(clause_work[:max(1, len(clause_work) // 10)]),
                complete_epochs=complete, pairs=pairs, passing_pairs=passing,
                advance=len(rows) >= 1000 and bool(pairs) and 2 * passing >= len(pairs),
                strata=strata)


def run(root, sha, cnf, control):
    binary = root / "precompile" / sha[:7] / "cnf_solve-traffic"
    flags = dict(cpu=10, max_conflicts=40000, stride=16, epoch_conflicts=4096,
                 emergency_timeout_s=300, profile="release", preset="CaDiCaL",
                 measurement="learned-clause-traffic-v1", print_model=True)
    record = dict(schema=benchstore.SCHEMA, suite=SUITE,
                  created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  host=dict(id=platform.node(), cpu=platform.machine(), os=platform.platform()),
                  git=dict(sha_long=sha, sha_short=sha[:7], dirty=False),
                  binary=dict(path=str(binary), sha256=digest(binary)),
                  instance=dict(name=cnf.name, sha256=digest(cnf), family=control["instance"]["family"]),
                  config=dict(id="observation", flags=flags, features=["clause-traffic"]),
                  seed=0, arm=dict(role="treatment"))
    record["config_hash"] = benchstore.canonical_flags(flags)
    dest = benchstore.record_path(root / "precompile", record)
    if dest.exists():
        prior = json.loads(dest.read_text())
        benchstore.validate(prior)
        assert benchstore.canonical_join_key(prior) == benchstore.canonical_join_key(record)
        print("reuse", prior["record_id"], flush=True)
        return prior
    rawdir = root / "precompile" / sha[:7] / "benchmark" / SUITE
    rawdir.mkdir(parents=True, exist_ok=True)
    prefix = rawdir / record["instance"]["family"]
    files = {key: Path(str(prefix) + "." + key) for key in
             ("stdout", "stderr", "started.json", "completed.json", "report.json", "summary.json")}
    command = ["taskset", "-c", "10", str(binary), str(cnf)]
    record["config"]["cmdline"] = command
    if not files["completed.json"].exists():
        with files["started.json"].open("x") as out:
            json.dump(record, out, indent=2)
        env = {k: v for k, v in os.environ.items() if not k.startswith((
            "NIXIE_", "ELS", "FACTOR", "NO_", "MAXC", "SEED", "INPROC", "STAB_",
            "REPHASE", "WALK", "RANDPOL", "PRINT_MODEL", "PHASE_HINT", "GATE_COUNT", "SCC_MASS"))}
        env.update(MAXC="40000", SEED="0", DIAG="1", PRINT_MODEL="1", NIXIE_CLAUSE_TRAFFIC="16", LC_ALL="C")
        print("start", cnf.name, flush=True)
        start = time.monotonic()
        with files["stdout"].open("x") as out, files["stderr"].open("x") as err:
            process = subprocess.Popen(command, env=env, stdout=out, stderr=err, start_new_session=True)
            try:
                status = process.wait(timeout=300)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                status = process.wait()
        with files["completed.json"].open("x") as out:
            json.dump(dict(status=status, instrumented_wall_s=time.monotonic() - start), out)
    completion = json.loads(files["completed.json"].read_text())
    assert completion["status"] == 0, files["stderr"].read_text()[-2000:]
    stdout = files["stdout"].read_text()
    assert files["stdout"].read_bytes() == Path(control["observations"]["stdout"]).read_bytes(), "trajectory difference"
    reports = [json.loads(line) for line in files["stderr"].read_text().splitlines()
               if line.startswith('{"schema":"nixie-clause-traffic/1"')]
    assert len(reports) == 1 and reports[0]["stride"] == 16
    report = reports[0]
    summary = summarize(report)
    for key, data in [("report.json", report), ("summary.json", summary)]:
        files[key].write_text(json.dumps(data, indent=2) + "\n")
    answer = re.search(r"^result=(\w+)", stdout, re.M).group(1).lower()
    conflicts = int(re.search(r"^conflicts=(\d+)", stdout, re.M).group(1))
    assert report["elapsed_conflicts"] == conflicts
    checked = answer == "sat"
    if checked:
        check_model(cnf, stdout)
    record["verdict"] = dict(answer=answer if checked else "unknown", verified_model_or_proof=checked)
    record["metrics"] = dict(primary=dict(name="sampled_learned_payloads_plus_scans", value=summary["total_work"]),
                             secondary=summary, counter_coverage_verified=True)
    record["observations"] = dict(reported_answer=answer, conflicts=conflicts,
                                   control_record_id=control["record_id"], stdout_identical=True,
                                   **{k: str(v) for k, v in files.items()})
    record["record_id"] = benchstore.record_id(record)
    benchstore.validate(record)
    dest.parent.mkdir(parents=True, exist_ok=True)
    with dest.open("x") as out:
        json.dump(record, out, indent=2, sort_keys=True)
    print("done", record["record_id"], "advance", summary["advance"], flush=True)
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--sha", required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    sha = subprocess.check_output(["git", "rev-parse", args.sha], cwd=root, text=True).strip()
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip() == sha
    assert not subprocess.check_output(["git", "status", "--porcelain"], text=True)
    controls = [json.loads(p.read_text()) for p in
                (root / "precompile/2202f0e/benchmark/runs/bcp-positive-certificates").glob("*.json")]
    inputs = []
    for name in ["circuit_48in", "j3037"]:
        paths = list((root / "satcomp2024/bench").glob("*" + name + "*.cnf"))
        assert len(paths) == 1
        cnf = paths[0]
        matches = [r for r in controls if r["instance"]["sha256"] == digest(cnf)]
        assert len(matches) == 1
        control = matches[0]
        benchstore.validate(control)
        assert control["host"]["id"] == platform.node() and control["seed"] == 0
        assert not control["git"]["dirty"] and control["arm"]["role"] == "baseline"
        assert control["config"]["flags"]["max_conflicts"] == 40000
        assert control["binary"]["sha256"] == digest(root / "precompile/2202f0e/stats_solve")
        inputs.append((cnf, control))
    directory = root / "precompile" / sha[:7] / "benchmark" / SUITE
    directory.mkdir(parents=True, exist_ok=True)
    manifest = dict(suite=SUITE, host=platform.node(), sha=sha, seeds=[0], stride=16,
                    epoch_conflicts=4096, max_conflicts=40000,
                    inputs=[dict(path=str(p), sha256=digest(p), control_record=c["record_id"]) for p, c in inputs])
    path = directory / "manifest.json"
    if path.exists():
        assert json.loads(path.read_text()) == manifest
    else:
        with path.open("x") as out:
            json.dump(manifest, out, indent=2)
    for cnf, control in inputs:
        run(root, sha, cnf, control)


if __name__ == "__main__":
    main()
