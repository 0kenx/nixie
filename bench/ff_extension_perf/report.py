#!/usr/bin/env python3
"""Compare all paired binary-field cells, rejecting trace differences and missing seeds."""
import argparse
from collections import defaultdict
import csv
import json
import math
from pathlib import Path
import statistics

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('root', type=Path)
p.add_argument('baseline')
p.add_argument('treatment')
p.add_argument('--first-seed', type=int, default=0)
p.add_argument('--seeds', type=int, default=10)
p.add_argument('--csv', type=Path)
a = p.parse_args()
def read(sha):
    rows = {}
    for f in (a.root / sha / 'benchmark/runs/ff-extension').glob('*.json'):
        r = json.loads(f.read_text())
        if a.first_seed <= r['seed'] < a.first_seed + a.seeds:
            key = (r['instance']['name'], r['seed'])
            if key in rows:
                raise ValueError(f'ambiguous cell {key}')
            rows[key] = r
    return rows
base, treatment = read(a.baseline), read(a.treatment)
assert base.keys() == treatment.keys() and len(base) == 13 * a.seeds, 'incomplete comparison'
groups = defaultdict(list)
rows = []
for key, b in sorted(base.items()):
    t = treatment[key]
    assert b['host'] == t['host'] and b['config_hash'] == t['config_hash'], key
    assert b['instance'] == t['instance'], key
    assert b['verdict'] == t['verdict'], key
    assert b['metrics']['secondary']['stdout_sha256'] == t['metrics']['secondary']['stdout_sha256'], key
    bv, tv = (r['metrics']['primary']['value'] for r in [b, t])
    family = b['instance']['family']
    groups[family].append((bv, tv))
    if not key[0].startswith("control-"):
        groups["non-control"].append((bv, tv))
    groups["verdict:" + b["verdict"]["answer"]].append((bv, tv))
    groups["instance:" + key[0]].append((bv, tv))
    rows.append({'instance': key[0], 'seed': key[1], 'baseline_instructions': bv,
                 'treatment_instructions': tv, 'ratio': tv / bv})
for group, pairs in sorted(groups.items()):
    ratio = math.exp(statistics.mean(math.log(t / b) for b, t in pairs))
    baseline = sorted(b for b, _ in pairs)
    print(f'{group:20} n={len(pairs):3} ratio={ratio:.4f} baseline_min/median/max={baseline[0]}/{statistics.median(baseline):g}/{baseline[-1]}')
print(f'{len(rows)} exact output matches; SAT={11 * a.seeds}; UNSAT={a.seeds}; Unknown={a.seeds}; no lost cells')
if a.csv:
    with a.csv.open('w') as f:
        writer = csv.DictWriter(f, fieldnames=rows[0].keys())
        writer.writeheader()
        writer.writerows(rows)

noncontrol = groups['non-control']
overall = math.exp(statistics.mean(math.log(t / b) for b, t in noncontrol))
case_ratios = {g.removeprefix('instance:'): math.exp(statistics.mean(math.log(t / b) for b, t in pairs))
               for g, pairs in groups.items() if g.startswith('instance:')}
wins = sum(r <= 0.90 for n, r in case_ratios.items() if not n.startswith('control-'))
passed = overall <= 0.85 and wins >= 3 and all(r <= 1.05 for r in case_ratios.values())
print('PRE-REGISTERED GATE:', 'PASS' if passed else 'FAIL')
if not passed:
    raise SystemExit(1)
