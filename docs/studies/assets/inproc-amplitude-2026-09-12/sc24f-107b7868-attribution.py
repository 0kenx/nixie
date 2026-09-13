#!/usr/bin/env python3
import json, glob, os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
ROOT = Path("/media/data/proj/nixie")
a, b = {}, {}
for f in glob.glob(str(ROOT / "precompile/8082e335/benchmark/runs/sc24f/*.json")):
    r = json.load(open(f))
    if r["config"]["id"] == "default" and r["seed"] <= 4:
        a[(r["instance"]["name"], r["seed"])] = r["verdict"]["answer"]
for f in glob.glob(str(ROOT / "precompile/107b7868/benchmark/runs/sc24f/*.json")):
    r = json.load(open(f))
    if r["config"]["id"] == "default":
        b[(r["instance"]["name"], r["seed"])] = r["verdict"]["answer"]
gained = [k for k in a.keys() & b.keys() if a[k] == "unknown" and b[k] != "unknown"]

def run(cell):
    name, seed = cell
    env = dict(os.environ, DIAG="1", SEED=str(seed))
    try:
        p = subprocess.run([str(ROOT / "precompile/32c88866/stats_solve"),
                            str(ROOT / "precompile/corpus-sc24f" / name)],
                           env=env, capture_output=True, text=True, timeout=60)
        v = "unknown"
        for line in p.stdout.splitlines():
            if line.startswith("result="):
                v = {"Sat": "sat", "Unsat": "unsat"}.get(line[7:], "unknown")
        return cell, v
    except subprocess.TimeoutExpired:
        return cell, "timeout"
res = {}
with ThreadPoolExecutor(max_workers=5) as ex:
    for fut in as_completed([ex.submit(run, c) for c in gained]):
        cell, v = fut.result()
        res[cell] = v
model_fix = sum(1 for v in res.values() if v != "timeout")
sched_fix = len(gained) - model_fix
import collections
per = collections.defaultdict(lambda: [0, 0])
for (name, seed), v in res.items():
    per[name.split("-", 1)[1][:24]][0 if v != "timeout" else 1] += 1
print(f"gained {len(gained)}: also-solved-by-32c88866(model-fix-only)={model_fix}, schedule-only={sched_fix}")
for f, (m, s) in sorted(per.items()): print(f"  {f}: model-fix {m}, schedule-only {s}")
