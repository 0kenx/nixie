#!/usr/bin/env python3
"""Measure a candidate once and join the original native-sequence/Z3 corpus."""

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import statistics

from perf import measure


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate", required=True, type=Path)
    parser.add_argument("--baseline", required=True, type=Path,
                        help="Original native-sequences-z3-perf record directory")
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--summarize-only", action="store_true")
    args = parser.parse_args()
    candidate = args.candidate.resolve()
    binary_hash = hashlib.sha256(candidate.read_bytes()).hexdigest()
    manifest = json.loads((args.baseline / "manifest.json").read_text())
    if manifest["host"]["id"] != platform.node():
        raise SystemExit("Cross-host comparison refused")
    baseline = {}
    for path in args.baseline.glob("*.json"):
        r = json.loads(path.read_text())
        if "result" in r:
            baseline[r["case"]["name"], r["seed"], r["arm"]] = r
    # Preserve only a fingerprint, never environment values which can be secrets.
    environment = {k: v for k, v in os.environ.items() if not k.startswith("NIXIE_")}
    environment["LC_ALL"] = "C"
    env_hash = hashlib.sha256(json.dumps(environment, sort_keys=True).encode()).hexdigest()
    identity = dict(binary_sha256=binary_hash, host=platform.node(),
                    baseline_manifest_sha256=hashlib.sha256(
                        (args.baseline / "manifest.json").read_bytes()).hexdigest(),
                    event=manifest["event"], cpu=manifest["cpu"], cap_s=manifest["cap_s"])
    args.out.mkdir(parents=True, exist_ok=True)
    config = args.out / "identity.json"
    if config.exists():
        if json.loads(config.read_text()) != identity:
            raise SystemExit("Existing experiment identity differs; do not overwrite")
    else:
        config.write_text(json.dumps(identity, indent=2) + "\n")
    records = []
    for case in manifest["cases"]:
        for seed in manifest["seeds"]:
            path = args.out / f"{case['name']}-s{seed}.json"
            if path.exists():
                r = json.loads(path.read_text())
                if r["identity"] != identity:
                    raise SystemExit("Cached cell identity mismatch")
            elif args.summarize_only:
                raise SystemExit(f"Missing {path}")
            else:
                script = f"(set-option :random-seed {seed})\n" + case["input"]
                result = measure(candidate, "nixie", script, manifest["cpu"], manifest["cap_s"])
                r = dict(identity=identity, environment_sha256=env_hash,
                         case=case, seed=seed, result=result)
                with path.open("x") as stream:
                    json.dump(r, stream, indent=2)
                    stream.write("\n")
            records.append(r)
            result = r["result"]
            if result["answer"] in ("sat", "unsat") and result["answer"] != case["expected"]:
                raise SystemExit(f"WRONG verdict retained in {path}")
        print(case["name"], flush=True)
    rows = []
    for case in manifest["cases"]:
        current = [r for r in records if r["case"]["name"] == case["name"]]
        ratios, z3_ratios = [], []
        for r in current:
            result = r["result"]
            if result["answer"] == case["expected"] and result["instructions"] is not None:
                for arm, dest in (("nixie", ratios), ("z3", z3_ratios)):
                    old = baseline[case["name"], r["seed"], arm]["result"]
                    if old["answer"] == case["expected"] and old["instructions"] is not None:
                        dest.append(result["instructions"] / old["instructions"])
        counts = [r["result"]["instructions"] for r in current
                  if r["result"]["answer"] == case["expected"]
                  and r["result"]["instructions"] is not None]
        rows.append(dict(case=case["name"],
                         answers=[r["result"]["answer"] for r in current],
                         instructions_median=statistics.median(counts) if counts else None,
                         instructions_min=min(counts) if counts else None,
                         instructions_max=max(counts) if counts else None,
                         baseline_pairs=len(ratios),
                         baseline_ratio=math.exp(statistics.mean(map(math.log, ratios))) if ratios else None,
                         z3_pairs=len(z3_ratios),
                         z3_ratio=math.exp(statistics.mean(map(math.log, z3_ratios))) if z3_ratios else None))
    (args.out / "summary.json").write_text(json.dumps(rows, indent=2) + "\n")
    print(json.dumps(rows, indent=2))
    if any(r["result"]["answer"] == "error" or
           (r["result"]["answer"] != "timeout" and r["result"]["instructions"] is None)
           for r in records):
        raise SystemExit("Errors or invalid completed counters were retained")


if __name__ == "__main__":
    main()
