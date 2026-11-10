#!/usr/bin/env python3
"""Summarize the registered benchmark, keeping timeouts and disagreements visible."""
import collections
import csv
import json
import math
from pathlib import Path
import statistics

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent


def geomean(values):
    return math.exp(statistics.mean(math.log(v) for v in values)) if values else None


def main():
    manifest = json.loads((HERE / 'manifest.json').read_text())
    rows = json.loads((ROOT / manifest['results']).read_text())
    assert len(rows) == 264
    by_instance = collections.defaultdict(dict)
    for row in rows:
        key = row['instance']['sha256']
        assert row['arm'] not in by_instance[key]
        by_instance[key][row['arm']] = row
    disagreements = []
    for key, group in by_instance.items():
        expected = next(iter(group.values()))['instance']['expected']
        refs = {r['answer'] for a, r in group.items() if a in ('z3', 'kissat', 'cadical') and r['answer'] in ('sat', 'unsat')}
        for arm, row in group.items():
            row['disagreement'] = row['answer'] in ('sat', 'unsat') and (
                expected in ('sat', 'unsat') and row['answer'] != expected or
                bool(refs) and row['answer'] not in refs or len(refs) > 1)
            row['consistent_decisive'] = row['answer'] in ('sat', 'unsat') and not row['disagreement']
            row['reference_answers'] = ','.join(sorted(refs))
            if row['disagreement']:
                disagreements.append(row)
    fields = ['kind', 'family', 'path', 'expected', 'arm', 'outcome', 'answer',
              'reference_answers', 'disagreement', 'instructions', 'wall_clock_s', 'exit_code', 'artifacts']
    with (HERE / 'results.csv').open('w', newline='') as output:
        writer = csv.DictWriter(output, fieldnames=fields)
        writer.writeheader()
        for row in sorted(rows, key=lambda r: (r['instance']['kind'], r['instance']['path'], r['arm'])):
            flat = {**row['instance'], **row}
            writer.writerow({key: flat[key] for key in fields})
    lines = ['## Results', '', 'All 264 registered cells completed. Counts below are decisive answers consistent',
             'with available corpus labels and references, not model/proof certification.', '']
    summary = {'cells': len(rows), 'disagreements': [], 'totals': [], 'paired': {}, 'gained': [], 'lost': []}
    lines += ['| Sample | Solver | Solved | SAT / UNSAT | Unknown | Timeout | Error | Total elapsed (s) | PAR-2 (s) |',
              '|---|---|---:|---:|---:|---:|---:|---:|---:|']
    for kind in ['SAT', 'SMT']:
        for arm in manifest['arms']:
            subset = [r for r in rows if r['instance']['kind'] == kind and r['arm'] == arm['name']]
            if not subset:
                continue
            solved = [r for r in subset if r['consistent_decisive']]
            counts = collections.Counter(r['outcome'] for r in subset)
            sat = sum(r['answer'] == 'sat' for r in solved)
            unsat = sum(r['answer'] == 'unsat' for r in solved)
            elapsed = sum(r['wall_clock_s'] for r in subset)
            par2 = statistics.mean(min(30, r['wall_clock_s']) if r['consistent_decisive'] else 60 for r in subset)
            lines.append(f"| {kind} ({len(subset)}) | {arm['name']} | {len(solved)} | {sat} / {unsat} | {counts['unknown']} | {counts['timeout']} | {counts['error']} | {elapsed:.2f} | {par2:.3f} |")
            summary['totals'].append({'kind': kind, 'arm': arm['name'], 'n': len(subset), 'solved': len(solved),
                                      'sat': sat, 'unsat': unsat, 'unknown': counts['unknown'],
                                      'timeout': counts['timeout'], 'error': counts['error'],
                                      'elapsed_s': elapsed, 'par2_s': par2})
    lines += ['', 'Whole-process instruction ratios are paired geometric means; lower is cheaper.',
              'Only jointly solved, agreeing cells enter a ratio. Different rows can have different',
              'pair sets, so their ratios must not be combined transitively.', '',
              '| Sample | Ratio | Pairs | Instructions | Elapsed diagnostic |',
              '|---|---|---:|---:|---:|']
    for kind in ['SAT', 'SMT']:
        for left, right in [('after', 'before'), ('after', 'z3'), ('after', 'kissat'), ('after', 'cadical')]:
            pairs = [(g[left], g[right]) for g in by_instance.values() if left in g and right in g
                     and g[left]['instance']['kind'] == kind
                     and g[left]['consistent_decisive'] and g[right]['consistent_decisive']
                     and g[left]['answer'] == g[right]['answer']]
            if not pairs:
                continue
            ins = geomean([a['instructions'] / b['instructions'] for a, b in pairs])
            wall = geomean([a['wall_clock_s'] / b['wall_clock_s'] for a, b in pairs])
            lines.append(f'| {kind} | {left}/{right} | {len(pairs)} | {ins:.4f} | {wall:.4f} |')
            summary['paired'][f'{kind}:{left}/{right}'] = {'pairs': len(pairs), 'instructions': ins, 'wall': wall}
    lines += ['', 'SAT/UNSAT split for the migration pair:', '',
              '| Kind | Answer | Pairs | After/before instructions |', '|---|---|---:|---:|']
    for kind in ['SAT', 'SMT']:
        for answer in ['sat', 'unsat']:
            pairs = [(g['after'], g['before']) for g in by_instance.values()
                     if g['after']['instance']['kind'] == kind
                     and all(g[a]['consistent_decisive'] and g[a]['answer'] == answer for a in ['before', 'after'])]
            if pairs:
                ratio = geomean([a['instructions'] / b['instructions'] for a, b in pairs])
                lines.append(f'| {kind} | {answer} | {len(pairs)} | {ratio:.4f} |')
    lines += ['', 'Per-family solved counts (Nixie columns are before/after):', '',
              '| Kind / family | N | Before | After | Z3 | Kissat | CaDiCaL |',
              '|---|---:|---:|---:|---:|---:|---:|']
    for kind, family in sorted({(r['instance']['kind'], r['instance']['family']) for r in rows}):
        sample = [r for r in rows if r['instance']['kind'] == kind and r['instance']['family'] == family]
        counts = {a: sum(r['consistent_decisive'] for r in sample if r['arm'] == a) for a in ['before', 'after', 'z3', 'kissat', 'cadical']}
        n = sum(r['arm'] == 'after' for r in sample)
        cells = [str(counts[a]) if any(r['arm'] == a for r in sample) else '—' for a in counts]
        lines.append(f'| {kind} / {family} | {n} | ' + ' | '.join(cells) + ' |')
    lines += ['', 'Migration gains and losses at the cap:', '', '| Instance | Before | After | Z3 |', '|---|---|---|---|']
    changes = 0
    for group in by_instance.values():
        a, b = group['after'], group['before']
        if a['consistent_decisive'] == b['consistent_decisive']:
            continue
        changes += 1
        name = a['instance']['path']
        summary['gained' if a['consistent_decisive'] else 'lost'].append(name)
        lines.append(f"| `{name}` | {b['outcome']} | {a['outcome']} | {group['z3']['outcome']} |")
    if not changes:
        lines.append('| None | — | — | — |')
    pairs = [(g['after'], g['before']) for g in by_instance.values()
             if g['after']['instance']['kind'] == 'SMT'
             and all(g[a]['consistent_decisive'] for a in ['before', 'after'])
             and g['after']['answer'] == g['before']['answer']]
    lines += ['', 'Largest observed SMT instruction ratios among agreeing completed pairs:', '',
              '| Instance | After/before instructions | Before (s) | After (s) |',
              '|---|---:|---:|---:|']
    for after, before in sorted(pairs, key=lambda pair: pair[0]['instructions'] / pair[1]['instructions'], reverse=True)[:5]:
        ratio = after['instructions'] / before['instructions']
        lines.append(f"| `{after['instance']['path']}` | {ratio:.3f} | {before['wall_clock_s']:.3f} | {after['wall_clock_s']:.3f} |")
    lines += ['', f'Verdict disagreements: **{len(disagreements)}**.', '']
    for row in disagreements:
        item = {'arm': row['arm'], 'path': row['instance']['path'], 'answer': row['answer'],
                'expected': row['instance']['expected'], 'references': row['reference_answers']}
        summary['disagreements'].append(item)
        lines.append('- ' + json.dumps(item))
    errors = [r for r in rows if r['outcome'] == 'error']
    if errors:
        lines += ['', 'Errors are retained as non-solves:', '']
        for row in errors:
            lines.append(f"- {row['arm']}: `{row['instance']['path']}` (exit {row['exit_code']}); see `{row['artifacts']}`.")
    (HERE / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    (HERE / 'results.md').write_text('\n'.join(lines) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
