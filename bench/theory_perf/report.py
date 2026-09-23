#!/usr/bin/env python3
"""Report paired costs, distributions and failed cells without rerunning them."""
import argparse
from collections import defaultdict
import csv
import json
import math
from pathlib import Path
import statistics

from run import GRID, SUITE


def geomean(values):
    return math.exp(statistics.mean(math.log(x) for x in values))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', type=Path, required=True)
    p.add_argument('--baseline', required=True)
    p.add_argument('--treatment', required=True)
    p.add_argument('--first-seed', type=int, default=0)
    p.add_argument('--csv', type=Path, required=True)
    a = p.parse_args()
    records = {}
    for role, sha in [('baseline', a.baseline), ('reference', a.baseline), ('treatment', a.treatment)]:
        directory = a.root / sha / 'benchmark' / 'runs' / SUITE
        for path in directory.glob('*.json'):
            r = json.loads(path.read_text())
            if r['arm']['role'] != role or not a.first_seed <= r['seed'] < a.first_seed + 10:
                continue
            key = role, r['instance']['name'], r['seed']
            if key in records:
                raise ValueError(f'ambiguous cell: {key}')
            if r['git']['dirty']:
                raise ValueError(f'dirty cell: {key}')
            records[key] = r
    grouped = defaultdict(list)
    rows = []
    for family, count in GRID:
        name = f'{family}-{count}'
        for seed in range(a.first_seed, a.first_seed + 10):
            base, treatment, reference = [records[role, name, seed] for role in ['baseline', 'treatment', 'reference']]
            for r in [treatment, reference]:
                if (r['host'] != base['host'] or r['instance'] != base['instance']):
                    raise ValueError(f'mismatched host/input: {name} seed {seed}')
            if treatment['config']['flags'] != base['config']['flags']:
                raise ValueError('different Nixie configuration')
            good = all(r['verdict']['verified_model_or_proof'] and r['verdict']['answer'] == 'sat'
                       and r['metrics']['counter_coverage_verified'] for r in [base, treatment, reference])
            if not good:
                print(f'FAILED/CENSORED {name} seed {seed}')
                rows.append([family, count, seed, 'failed', '', '', '', '', ''])
                continue
            if treatment['metrics']['secondary']['stdout_sha256'] != base['metrics']['secondary']['stdout_sha256']:
                raise ValueError('different Nixie verdict transcript')
            b, t, z = [r['metrics']['primary']['value'] for r in [base, treatment, reference]]
            row = [family, count, seed, 'solved', b, t, z, t / b, t / z]
            rows.append(row)
            grouped[family].append(row)
    with a.csv.open('w') as f:
        writer = csv.writer(f)
        writer.writerow(['family', 'count', 'seed', 'status', 'baseline', 'treatment', 'z3', 'treatment/control', 'treatment/z3'])
        writer.writerows(rows)
    print('family | n | baseline instructions min/median/max | treatment/control | treatment/Z3')
    for family, values in sorted(grouped.items()):
        baseline = [row[4] for row in values]
        print(f'{family} | {len(values)} | {min(baseline):,}/{statistics.median(baseline):,.0f}/{max(baseline):,} | '
              f'{geomean([r[7] for r in values]):.4f} | {geomean([r[8] for r in values]):.4f}')
    fp = [r for r in rows if r[0].startswith('fp') and r[3] == 'solved']
    print(f'FP treatment/control: {geomean([r[7] for r in fp]):.4f}')
    solved = sum(row[3] == 'solved' for row in rows)
    print(f'solved: {solved}/{len(rows)} cells per arm; {3 * solved} checks per arm')
    if solved != len(rows):
        raise SystemExit('incomplete solved set')


if __name__ == '__main__':
    main()
