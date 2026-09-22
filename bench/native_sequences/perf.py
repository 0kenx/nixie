#!/usr/bin/env python3
"""Pinned, run-once native-sequence comparison; see README.md for protocol."""

import argparse
from collections import Counter
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import statistics
import subprocess
import time


REVISION = "3a42cb2d7e7b3f8612a6b2d9abe760616919d133"
EVENT = "cpu_core/instructions/u"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def corpus():
    cases = []

    def add(name, family, expected, body):
        cases.append(dict(name=name, family=family, expected=expected,
                          input=f"(set-logic ALL)\n{body}\n(check-sat)\n"))

    for n in (8, 32, 128, 512):
        prefix = f"(declare-const q (Seq Int))\n(assert (= (seq.len q) {n}))"
        add(f"append-{n}", "append", "unsat", prefix +
            f"\n(declare-const x Int)\n(assert (distinct (seq.len (seq.++ q (seq.unit x))) {n+1}))")
        add(f"tail-{n}", "tail", "unsat", prefix +
            f"\n(assert (distinct (seq.nth (seq.extract q 1 {n-1}) {n-2}) (seq.nth q {n-1})))")
        add(f"split-{n}", "split", "unsat", prefix +
            f"\n(assert (distinct q (seq.++ (seq.extract q 0 {n//2}) (seq.extract q {n//2} {n}))))")
        add(f"history-{n}", "history", "sat", prefix + "\n" + "\n".join(
            f"(assert (= (seq.nth q {i}) {i}))" for i in range(n)))

    add("empty", "boundary", "unsat",
        "(assert (distinct (seq.extract (seq.unit 1) 1 0) (as seq.empty (Seq Int))))")
    add("concat-disequality", "boundary", "sat",
        "(declare-const a Int)\n(declare-const b Int)\n(assert (distinct a b))\n"
        "(assert (distinct (seq.++ (seq.unit a) (seq.unit b)) (seq.++ (seq.unit b) (seq.unit a))))")
    add("nested-congruence", "nested", "unsat",
        "(declare-const a Int)\n(declare-const b Int)\n(assert (= a b))\n"
        "(assert (distinct (seq.unit (seq.unit a)) (seq.unit (seq.unit b))))")
    add("symbolic-append", "unsupported", "unsat",
        "(declare-const q (Seq Int))\n(declare-const x Int)\n"
        "(assert (distinct (seq.len (seq.++ q (seq.unit x))) (+ (seq.len q) 1)))")
    add("symbolic-read", "unsupported", "sat",
        "(declare-const q (Seq Int))\n(declare-const i Int)\n"
        "(assert (= (seq.len q) 8))\n(assert (<= 0 i))\n(assert (< i 8))\n(assert (= (seq.nth q i) 7))")
    add("symbolic-word-equation", "unsupported", "sat",
        "(declare-const a (Seq Int))\n(declare-const b (Seq Int))\n"
        "(assert (= (seq.++ a (seq.unit 1)) (seq.++ (seq.unit 1) b)))")
    return cases


def measure(binary, arm, script, cpu, cap):
    args = [str(binary), "-in"] if arm == "z3" else [str(binary), "--smtcomp", "--no-color"]
    cmd = ["taskset", "-c", str(cpu), "perf", "stat", "-x,", "-e", EVENT, "--", *args]
    env = dict(os.environ, LC_ALL="C")
    # Avoid inherited tuning flags making a nominal default arm non-default.
    env = {k: v for k, v in env.items() if not k.startswith("NIXIE_")}
    start = time.monotonic()
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, text=True, env=env, start_new_session=True)
    timed_out = False
    try:
        stdout, stderr = proc.communicate(script, timeout=cap)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(proc.pid, signal.SIGTERM)
        try:
            stdout, stderr = proc.communicate(timeout=1)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            stdout, stderr = proc.communicate()
    wall = time.monotonic() - start
    verdicts = re.findall(r"^(sat|unsat|unknown)\s*$", stdout, re.M)
    answer = verdicts[0] if len(verdicts) == 1 else "error"
    if timed_out:
        answer = "timeout"
    elif proc.returncode != 0 or "(error" in stdout:
        answer = "error"
    counts = []
    for line in stderr.splitlines():
        fields = line.split(",")
        if len(fields) >= 5 and fields[2] == EVENT:
            # Reject multiplexed/scaled counts; no retry or quiet replacement.
            if fields[0].isdigit() and float(fields[4]) == 100.0:
                counts.append(int(fields[0]))
    return dict(answer=answer, instructions=counts[0] if len(counts) == 1 else None,
                wall_s=wall, stdout=stdout, stderr=stderr, returncode=proc.returncode,
                command=cmd)


def summarize(records):
    pairs = {}
    for r in records:
        pairs.setdefault((r["case"]["name"], r["seed"]), {})[r["arm"]] = r
    rows = []
    for name in sorted({key[0] for key in pairs}):
        samples = [p for (n, _), p in pairs.items() if n == name]
        ratios = [p["nixie"]["result"]["instructions"] / p["z3"]["result"]["instructions"]
                  for p in samples if all(
                      p[a]["result"]["answer"] == p[a]["case"]["expected"]
                      and p[a]["result"]["instructions"] is not None for a in ("nixie", "z3"))]
        row = dict(name=name, matched=len(ratios),
                   ratio_geomean=math.exp(statistics.mean(map(math.log, ratios))) if ratios else None)
        for arm in ("nixie", "z3"):
            results = [p[arm]["result"] for p in samples]
            expected = samples[0][arm]["case"]["expected"]
            counts = [r["instructions"] for r in results
                      if r["instructions"] is not None and r["answer"] == expected]
            row[arm] = dict(verdicts=dict(Counter(r["answer"] for r in results)),
                            instructions_min=min(counts) if counts else None,
                            instructions_median=statistics.median(counts) if counts else None,
                            instructions_max=max(counts) if counts else None,
                            wall_median_s=statistics.median(r["wall_s"] for r in results))
        rows.append(row)
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cpu", type=int, default=6)
    parser.add_argument("--cap", type=float, default=6)
    parser.add_argument("--summarize-only", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    out = root / "precompile" / REVISION / "benchmark" / "native-sequences-z3-perf"
    out.mkdir(parents=True, exist_ok=True)
    binaries = {"nixie": root / "precompile" / REVISION / "nixie",
                "z3": Path(shutil.which("z3") or "z3").resolve()}
    hashes = {a: digest(p.read_bytes()) for a, p in binaries.items()}
    versions = {"z3": subprocess.check_output([str(binaries["z3"]), "--version"], text=True).strip(),
                "nixie": REVISION}
    host = dict(id=platform.node(), os=platform.platform(), cpu=Path("/proc/cpuinfo").read_text())
    manifest = dict(schema="nixie-sequence-perf/1", host=host, versions=versions,
                    binaries={a: str(p) for a, p in binaries.items()}, binary_hashes=hashes,
                    cpu=args.cpu, cap_s=args.cap, event=EVENT, seeds=list(range(10)), cases=corpus())
    manifest_path = out / "manifest.json"
    if manifest_path.exists():
        old = json.loads(manifest_path.read_text())
        # /proc/cpuinfo includes current clock frequencies, not part of identity.
        old["host"]["cpu"] = host["cpu"]
        if old != manifest:
            raise SystemExit("Existing experiment has a different configuration; do not overwrite it")
    else:
        manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    records = []
    for case in corpus():
        for seed in range(10):
            script = f"(set-option :random-seed {seed})\n" + case["input"]
            for arm in (("nixie", "z3") if seed % 2 == 0 else ("z3", "nixie")):
                key = dict(host=host["id"], revision=REVISION, binary_sha256=hashes[arm],
                           input_sha256=digest(script.encode()), cpu=args.cpu, cap_s=args.cap,
                           event=EVENT, arm=arm, seed=seed)
                path = out / (digest(json.dumps(key, sort_keys=True).encode()) + ".json")
                if path.exists():
                    record = json.loads(path.read_text())
                    if record["key"] != key:
                        raise SystemExit("Cache identity mismatch")
                elif args.summarize_only:
                    raise SystemExit(f"Missing cell: {case['name']} {seed} {arm}")
                else:
                    result = measure(binaries[arm], arm, script, args.cpu, args.cap)
                    record = dict(key=key, case=case, seed=seed, arm=arm, versions=versions,
                                  result=result, created_utc=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
                    with path.open("x") as stream:
                        json.dump(record, stream, indent=2)
                        stream.write("\n")
                records.append(record)
                result = record["result"]
                if result["answer"] in ("sat", "unsat") and result["answer"] != case["expected"]:
                    raise SystemExit(f"WRONG verdict: {case['name']} {arm}; saved {path}")
        print(case["name"], {a: dict(Counter(r["result"]["answer"] for r in records
              if r["case"]["name"] == case["name"] and r["arm"] == a)) for a in binaries}, flush=True)
    summary = summarize(records)
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    if any(r["result"]["answer"] == "error" or
           (r["result"]["answer"] != "timeout" and r["result"]["instructions"] is None) for r in records):
        raise SystemExit("Incomplete measurement: errors or missing counters retained in raw records")


if __name__ == "__main__":
    main()
