#!/usr/bin/env python3
"""Summarize frozen heap cells; never executes a solver or replaces measurements."""
import argparse
import csv
import json
import math
from pathlib import Path
import statistics
import run


def analyze(directory, output):
    records = [run.benchstore.validate(json.loads(p.read_text())) for p in directory.glob('*.json')]
    cells = {(r['instance']['name'],r['config']['id'],r['seed']): r for r in records}
    expected = set()
    for family in run.FAMILIES:
        for size in (2,4,8,16):
            arms = [a+'-total' for a in run.ARMS]
            if size in (2,16):
                arms += ['nixie-encode','nixie-solve']
                if family in ('allocate','negative'): arms += ['nixie-validate']
            expected.update((f'{family}-{size}',a,s) for a in arms for s in range(10))
    assert set(cells) == expected and len(records) == len(expected), 'missing or duplicate cells'
    assert len({r['git']['sha_long'] for r in records}) == 1
    assert len({r['host']['id'] for r in records}) == 1
    for r in records:
        name = r['instance']['name']
        expected_answer = 'sat' if name.startswith(('allocate-','negative-')) else 'unsat'
        assert r['verdict']['answer'] in (expected_answer,'unknown')
    output.mkdir(parents=True,exist_ok=True)
    run.summarize(records,output)
    rows = json.loads((output/'summary.json').read_text())
    with (output/'summary.csv').open('w') as out:
        writer = csv.DictWriter(out,fieldnames=list(rows[0]))
        writer.writeheader(); writer.writerows(rows)
    lines = ['| Case | Nixie | CVC5 SL | CVC5 array | Z3 array |',
             '|---|---:|---:|---:|---:|']
    def cost(name,arm):
        row = next(r for r in rows if r['case'] == name and r['arm'] == arm+'-total')
        value = row['instructions_median']
        return f"{value/1e6:.2f} ({row['solved']}/10)" if value is not None else '— (0/10)'
    for family in run.FAMILIES:
        for size in (2,4,8,16):
            name = f'{family}-{size}'
            lines.append('| '+name+' | '+' | '.join(cost(name,a) for a in run.ARMS)+' |')
    lines += ['', 'Millions of user-space instructions, median of completed runs; solved/10 in parentheses.',
              'Min/max distributions and RSS are in summary.csv. Unknown partial work is excluded.', '',
              '| Comparison | Shared decisive cells / 200 | Geometric mean Nixie / reference |',
              '|---|---:|---:|']
    for arm in run.ARMS[1:]:
        ratios = []
        for (case,config,seed),nixie in cells.items():
            if config != 'nixie-total': continue
            ref = cells[(case,arm+'-total',seed)]
            if any(r['verdict']['answer'] == 'unknown' for r in (nixie,ref)): continue
            ratios.append(nixie['metrics']['primary']['value']/ref['metrics']['primary']['value'])
        ratio = math.exp(statistics.mean(map(math.log,ratios))) if ratios else None
        lines.append(f'| {arm} | {len(ratios)} | {ratio:.3f} |' if ratio is not None else f'| {arm} | 0 | — |')
    lines += ['', '| Case | Encode M instructions | Check M instructions | Extra validation instructions | Backend terms |',
              '|---|---:|---:|---:|---:|']
    for family in run.FAMILIES:
        for size in (2,16):
            name = f'{family}-{size}'
            def region(phase,scale):
                row = next((r for r in rows if r['case'] == name and r['arm'] == 'nixie-'+phase),None)
                if row is None or row['instructions_median'] is None: return '—'
                return f"{row['instructions_median']/scale:.3f}"
            row = next(r for r in rows if r['case'] == name and r['arm'] == 'nixie-total')
            lines.append(f"| {name} | {region('encode',1e6)} | {region('solve',1e6)} | {region('validate',1)} | {row['backend_terms']} |")
    (output/'tables.md').write_text('\n'.join(lines)+'\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('records',type=Path)
    parser.add_argument('output',type=Path)
    args = parser.parse_args()
    analyze(args.records,args.output)
