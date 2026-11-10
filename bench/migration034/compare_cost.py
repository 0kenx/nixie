#!/usr/bin/env python3
"""Compare a registered cost-fix snapshot without dropping censored outcomes."""
import argparse
import collections
import csv
import json
import math
from pathlib import Path
import re
import statistics

ROOT = Path(__file__).resolve().parents[2]


def geomean(values):
    return math.exp(statistics.mean(map(math.log, values))) if values else None


def counters(row):
    output = (ROOT / row['artifacts'] / 'stdout.txt').read_text()
    return dict(re.findall(r'^  (Decisions|Propagations|Conflicts|Restarts): (\d+)',
                           output, re.MULTILINE))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('manifest', type=Path)
    parser.add_argument('candidate')
    parser.add_argument('output_prefix', type=Path)
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    rows = json.loads((ROOT / manifest['results']).read_text())
    expected_cells = sum(i['kind'] in a['kinds'] for i in manifest['instances']
                         for a in manifest['arms'])
    assert len(rows) == expected_cells
    groups = collections.defaultdict(dict)
    for row in rows:
        group = groups[row['instance']['sha256']]
        assert row['arm'] not in group
        group[row['arm']] = row
    disagreements = []
    for group in groups.values():
        expected = next(iter(group.values()))['instance']['expected']
        refs = {r['answer'] for a, r in group.items()
                if a in ('z3', 'kissat', 'cadical') and r['answer'] in ('sat', 'unsat')}
        for name, row in group.items():
            if row['answer'] in ('sat', 'unsat') and (
                    expected in ('sat', 'unsat') and row['answer'] != expected or
                    refs and row['answer'] not in refs or len(refs) > 1):
                disagreements.append({'arm': name, 'path': row['instance']['path'],
                                      'answer': row['answer'], 'expected': expected,
                                      'references': sorted(refs)})
    summary = {'cells': len(rows), 'candidate': args.candidate,
               'disagreements': disagreements, 'counts': {}, 'comparisons': {},
               'cases': []}
    for kind in ('SAT', 'SMT'):
        for arm in manifest['arms']:
            subset = [r for r in rows if r['instance']['kind'] == kind
                      and r['arm'] == arm['name']]
            if subset:
                summary['counts'][kind + ':' + arm['name']] = dict(
                    collections.Counter(r['outcome'] for r in subset))
        for baseline in (arm['name'] for arm in manifest['arms']
                         if arm['name'] != args.candidate):
            relevant = [g for g in groups.values() if baseline in g and args.candidate in g
                        and g[args.candidate]['instance']['kind'] == kind]
            if not relevant:
                continue
            pairs = [(g[args.candidate], g[baseline]) for g in relevant
                     if g[args.candidate]['answer'] == g[baseline]['answer']
                     and g[baseline]['answer'] in ('sat', 'unsat')]
            summary['comparisons'][kind + ':' + baseline] = {
                'jointly_solved_agreeing': len(pairs),
                'instructions_candidate_over_baseline': geomean(
                    [a['instructions'] / b['instructions'] for a, b in pairs]),
                'gained': [g[args.candidate]['instance']['path'] for g in relevant
                           if g[args.candidate]['answer'] in ('sat', 'unsat')
                           and g[baseline]['answer'] not in ('sat', 'unsat')],
                'lost': [g[args.candidate]['instance']['path'] for g in relevant
                         if g[baseline]['answer'] in ('sat', 'unsat')
                         and g[args.candidate]['answer'] not in ('sat', 'unsat')]}
    original = [g for g in groups.values() if g['before']['instance']['kind'] == 'SMT'
                and g['before']['answer'] == g['after']['answer']
                and g['before']['answer'] in ('sat', 'unsat')]
    retained = [g for g in original if g[args.candidate]['answer'] == g['before']['answer']]
    summary['original_smt_cohort'] = {
        'original_pairs': len(original), 'candidate_retained': len(retained),
        'instructions_candidate_over_before': geomean([
            g[args.candidate]['instructions'] / g['before']['instructions'] for g in retained]),
        'instructions_candidate_over_after': geomean([
            g[args.candidate]['instructions'] / g['after']['instructions'] for g in retained])}
    for group in groups.values():
        a, b, r = group[args.candidate], group['before'], group['rollback']
        paired = a['answer'] == b['answer'] and a['answer'] in ('sat', 'unsat')
        ac, rc = counters(a), counters(r)
        summary['cases'].append({
            'kind': a['instance']['kind'], 'path': a['instance']['path'],
            'before_outcome': b['outcome'], 'rollback_outcome': r['outcome'],
            'candidate_outcome': a['outcome'], 'before_instructions': b['instructions'],
            'rollback_instructions': r['instructions'], 'candidate_instructions': a['instructions'],
            'candidate_over_before': a['instructions'] / b['instructions'] if paired else None,
            'candidate_counters': ac, 'rollback_counters': rc,
            'same_observed_counters': ac == rc if ac and rc else None,
            'candidate_artifacts': a['artifacts']})
    summary['cases'].sort(key=lambda x: (x['kind'], x['path']))
    args.output_prefix.with_suffix('.json').write_text(json.dumps(summary, indent=2) + '\n')
    with args.output_prefix.with_suffix('.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=list(summary['cases'][0]))
        writer.writeheader()
        writer.writerows(summary['cases'])
    print(json.dumps({k: v for k, v in summary.items() if k != 'cases'}, indent=2))
    if disagreements:
        raise SystemExit('Decisive disagreement: inspect before accepting the snapshot')


if __name__ == '__main__':
    main()
