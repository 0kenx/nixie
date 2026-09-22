#!/usr/bin/env python3
"""Analyze the frozen three-arm matrix without executing or replacing cells."""
import argparse
import csv
import json
import math
from pathlib import Path
import re
import statistics

import anchor_experiment as experiment
import run


def driver_counters(record, directory):
    # Benchstore intentionally excludes stdout/stderr from secondary metrics.
    # Recover diagnostics from the immutable raw result, checking its pairing.
    name = (f"{record['instance']['name']}-{record['config']['id']}-"
            f"{record['seed']}-{record['record_id']}.result.json")
    raw = directory.parents[1] / experiment.SUITE / name
    result = json.loads(raw.read_text())
    assert result['instructions'] == record['metrics']['primary']['value']
    assert result['payload']['answer'] == record['verdict']['answer']
    assert result['payload']['verified'] == record['verdict']['verified_model_or_proof']
    match = re.search(r'^definitions (\d+) (\d+)$', result['payload']['stdout'], re.M)
    if record['config']['id'] != 'baseline-total':
        assert match, 'candidate driver diagnostics missing'
    comparisons = re.search(r'^comparisons (\d+)$', result['payload']['stdout'], re.M)
    if record['config']['id'] != 'baseline-total':
        assert comparisons, 'candidate comparison count missing'
    return (int(match[1]), int(match[2]), int(comparisons[1]) if comparisons else None) if match else None


def analyze(directory, output):
    records = [run.benchstore.validate(json.loads(p.read_text())) for p in directory.glob('*.json')]
    cells = {(r['instance']['name'], r['config']['id'], r['seed']): r for r in records}
    expected = {(f'{family}-{n}', arm+'-total', seed)
                for family, n in experiment.CASES
                for arm in experiment.ARMS for seed in experiment.SEEDS}
    assert set(cells) == expected and len(records) == len(expected), 'missing or duplicate cells'
    assert len({r['git']['sha_long'] for r in records}) == 1
    assert len({r['host']['id'] for r in records}) == 1
    for r in records:
        wanted = 'sat' if r['instance']['family'] in ('allocate', 'negative', 'views', 'unasserted_views') else 'unsat'
        assert r['verdict']['answer'] in (wanted, 'unknown')
        if r['verdict']['answer'] != 'unknown':
            assert r['verdict']['verified_model_or_proof']
            assert r['metrics']['primary']['name'] == 'instructions:u'
            assert r['metrics']['primary']['value'] > 0
    output.mkdir(parents=True, exist_ok=True)
    run.summarize(records, output)
    rows = json.loads((output/'summary.json').read_text())
    for row in rows:
        selected = [r for r in records if r['instance']['name'] == row['case']
                    and r['config']['id'] == row['arm'] and r['verdict']['answer'] != 'unknown']
        definitions, post_terms, comparisons = [], [], []
        for r in selected:
            counters = driver_counters(r, directory)
            if counters:
                definitions.append(counters[0]); post_terms.append(counters[1])
                if counters[2] is not None: comparisons.append(counters[2])
        row['definition_assertions'] = statistics.median(definitions) if definitions else None
        row['postcheck_terms'] = statistics.median(post_terms) if post_terms else None
        row['comparisons'] = statistics.median(comparisons) if comparisons else None
    with (output/'summary.csv').open('w') as out:
        writer = csv.DictWriter(out, fieldnames=list(rows[0]))
        writer.writeheader(); writer.writerows(rows)
    lines = ['| Case | Baseline | Retained-pair control | Reduced |', '|---|---:|---:|---:|']
    for family, n in experiment.CASES:
        case = f'{family}-{n}'
        values = []
        for arm in experiment.ARMS:
            row = next(r for r in rows if r['case'] == case and r['arm'] == arm+'-total')
            value = row['instructions_median']
            values.append(f"{value/1e6:.2f} ({row['solved']}/11)" if value else '— (0/11)')
        lines.append('| '+case+' | '+' | '.join(values)+' |')
    lines += ['', 'Millions of user instructions; median among completed runs. Partial Unknown costs excluded.', '',
              '| Subset | Comparator | Shared pairs | Reduced / comparator cost |', '|---|---|---:|---:|']
    for subset in ('seeds-0-9', 'held-out-102', 'new-families', 'original-families'):
        for arm in ('baseline', 'redundant'):
            ratios = []
            for (case, config, seed), treatment in cells.items():
                if config != 'reduced-total': continue
                if subset == 'seeds-0-9' and seed == 102: continue
                if subset == 'held-out-102' and seed != 102: continue
                if subset == 'new-families' and treatment['instance']['family'] in run.FAMILIES: continue
                if subset == 'original-families' and treatment['instance']['family'] not in run.FAMILIES: continue
                control = cells[(case, arm+'-total', seed)]
                if any(r['verdict']['answer'] == 'unknown' for r in (treatment, control)): continue
                ratios.append(treatment['metrics']['primary']['value']/control['metrics']['primary']['value'])
            ratio = math.exp(statistics.mean(map(math.log, ratios))) if ratios else None
            lines.append(f'| {subset} | {arm} | {len(ratios)} | {ratio:.4f} |' if ratio else
                         f'| {subset} | {arm} | 0 | — |')
    (output/'tables.md').write_text('\n'.join(lines)+'\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('records', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    analyze(args.records, args.output)
