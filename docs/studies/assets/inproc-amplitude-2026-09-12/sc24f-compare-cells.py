#!/usr/bin/env python3
"""Compare two sc24f cell sets: solved cells, conflicts geomean on
both-decided pairs (per-seed), verdict disagreements."""
import json, glob, math, sys
from collections import defaultdict

def load(root):
    d = defaultdict(dict)  # (file, seed) -> (verdict, conflicts)
    for f in glob.glob(f"{root}/*.json"):
        r = json.load(open(f))
        if r["config"]["id"] != "default":
            continue
        key = (r["instance"]["name"], r["seed"])
        d[key] = (r["verdict"]["answer"], r["metrics"]["primary"]["value"])
    return d

a, b = load(sys.argv[1]), load(sys.argv[2])
solved_a = sum(1 for v, _ in a.values() if v != "unknown")
solved_b = sum(1 for v, _ in b.values() if v != "unknown")
disagree = [(k, a[k], b[k]) for k in a.keys() & b.keys() if a[k][0] != b[k][0] and b[k][0] != "unknown" and a[k][0] != "unknown"]
ratios = []
for k in a.keys() & b.keys():
    va, ca = a[k]; vb, cb = b[k]
    if va == vb and va != "unknown" and ca > 0 and cb > 0:
        ratios.append(cb / ca)
gm = math.exp(sum(math.log(r) for r in ratios) / len(ratios)) if ratios else float("nan")
flips = defaultdict(lambda: [0, 0])
for k in a.keys() & b.keys():
    va, _ = a[k]; vb, _ = b[k]
    name = k[0].split("-", 1)[1][:24]
    if va == "unknown" and vb != "unknown": flips[name][0] += 1
    if va != "unknown" and vb == "unknown": flips[name][1] += 1
print(f"A ({sys.argv[1]}): {solved_a} solved cells")
print(f"B ({sys.argv[2]}): {solved_b} solved cells")
print(f"verdict disagreements (both decided): {len(disagree)}")
for k, x, y in disagree[:8]: print("  ", k, x, y)
print(f"conflicts geomean B/A (both-decided, n={len(ratios)}): {gm:.4f}")
print("per-file flips (A-solved→B-unsolved, B-new-solves):")
for name, (gained, lost) in sorted(flips.items()):
    if gained or lost: print(f"  {name}: +{gained} -{lost}")
