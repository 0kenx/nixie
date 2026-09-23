#!/usr/bin/env python3
"""Join Z3's exact encoding to Nixie's logical instances, without counting Unknown as solved."""
import argparse
from collections import Counter
import csv
import json
import math
from pathlib import Path
import statistics

from z3_reference import Z3_SHA, problem, workload, sha256

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('root', type=Path)
p.add_argument('nixie_sha')
p.add_argument('--first-seed', type=int, default=0)
p.add_argument('--seeds', type=int, default=20)
p.add_argument('--csv', type=Path)
a = p.parse_args()


def read(sha, suite):
    rows = {}
    for f in (a.root / sha / 'benchmark/runs' / suite).glob('*.json'):
        r = json.loads(f.read_text())
        if a.first_seed <= r['seed'] < a.first_seed + a.seeds:
            key = (r['instance']['name'], r['seed'])
            assert key not in rows, f'ambiguous cell {key}'
            rows[key] = r
    return rows


nixie = read(a.nixie_sha, 'ff-extension')
z3 = read(Z3_SHA[:8], 'ff-extension-z3')
# The certified-SAT label has identical Z3 equations/options to shared-f256.
# Its second measured attempt was archived and excluded; reuse the first cell.
assert len(z3) == 12 * a.seeds, 'incomplete unique reference cells'
for seed in range(a.first_seed, a.first_seed + a.seeds):
    z3['certified-f256', seed] = z3['shared-f256', seed]
assert nixie.keys() == z3.keys() and len(nixie) == 13 * a.seeds, 'incomplete comparison'
cases = {c['name']: c for c in workload.CASES}
rows, ratios = [], []
for name in sorted({name for name, _ in nixie}):
    ns, zs, answers_n, answers_z = [], [], [], []
    for seed in range(a.first_seed, a.first_seed + a.seeds):
        n, z = nixie[name, seed], z3[name, seed]
        assert n['host'] == z['host'], (name, seed)
        encoded, _, original = problem(cases[name], seed)
        assert n['instance']['sha256'] == sha256(original.encode()), (name, seed)
        assert z['instance']['sha256'] == sha256(encoded.encode()), (name, seed)
        source_name = 'shared-f256' if name == 'certified-f256' else name
        source_original, _ = workload.problem(cases[source_name], seed)
        assert z['metrics']['secondary']['logical_instance_sha256'] == sha256(source_original.encode())
        assert n['metrics']['primary']['name'] == z['metrics']['primary']['name'] == 'instructions:u'
        for r in (n, z):
            assert r['metrics']['counter_coverage_verified']
            assert r['verdict']['answer'] == 'unknown' or r['verdict']['verified_model_or_proof']
        nv, zv = n['verdict']['answer'], z['verdict']['answer']
        assert nv == zv or 'unknown' in (nv, zv), (name, seed)
        ns.append(n['metrics']['primary']['value'])
        zs.append(z['metrics']['primary']['value'])
        answers_n.append(nv)
        answers_z.append(zv)
        if nv != 'unknown' and zv != 'unknown' and not name.startswith('control-'):
            ratios.append(ns[-1] / zs[-1])
    solved = all(n != 'unknown' and z != 'unknown' for n, z in zip(answers_n, answers_z))
    ratio = math.exp(statistics.mean(math.log(n/z) for n, z in zip(ns, zs))) if solved else ''
    row = {'instance': name, 'seeds': a.seeds,
           'reference_reused_from': 'shared-f256' if name == 'certified-f256' else '',
           'nixie_min': min(ns), 'nixie_median': statistics.median(ns), 'nixie_max': max(ns),
           'z3_min': min(zs), 'z3_median': statistics.median(zs), 'z3_max': max(zs),
           'nixie_over_z3_solved_ratio': ratio,
           'nixie_verdicts': str(dict(Counter(answers_n))), 'z3_verdicts': str(dict(Counter(answers_z)))}
    rows.append(row)
    print(row)
print('Nixie:', dict(Counter(r['verdict']['answer'] for r in nixie.values())))
print('Z3:', dict(Counter(r['verdict']['answer'] for r in z3.values())))
print('Non-control jointly solved instruction geomean Nixie/Z3:', math.exp(statistics.mean(map(math.log, ratios))))
print(f'{12*a.seeds} unique Z3 cells; {a.seeds} certified labels reuse shared cells.')
print('Unknown cells are excluded from solved cost ratios; no lost logical cells.')
if a.csv:
    with a.csv.open('w') as f:
        writer = csv.DictWriter(f, fieldnames=rows[0].keys())
        writer.writeheader()
        writer.writerows(rows)
