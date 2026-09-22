"""Validate and summarize the complete frozen four-optimization matrix."""
import argparse
import csv
import json
import math
from pathlib import Path
import statistics

import next_cases as cases
import next_experiment as experiment
import next_worker as worker
import run

TARGETS = dict(no_coverage=('free_views',),
               no_equalities=('views', 'symbolic_views', 'offset_views'),
               no_cache=('cache_scopes',),
               eager=('boolean_sat', 'boolean_unsat', 'boolean_alias'))


def geomean(values):
    return math.exp(statistics.mean(map(math.log, values))) if values else None


def validate_records(records, manifest):
    cells = {(r['instance']['name'], r['config']['id'], r['seed']): r for r in records}
    expected = {(f'{f}-{n}', arm, seed) for f, n in cases.CASES
                for arm in experiment.ARMS for seed in experiment.SEEDS}
    assert set(cells) == expected and len(records) == len(expected), 'missing or duplicate cells'
    assert {r['git']['sha_long'] for r in records} == {manifest['sha']}
    assert len({json.dumps(r['host'], sort_keys=True) for r in records}) == 1
    binaries, configurations = {}, {}
    for r in records:
        assert r['reference_versions'] == manifest['versions']
        arm = r['config']['id']; flags = r['config']['flags']
        assert flags['library_revision'] == (experiment.BASELINE_SHA if arm == 'baseline' else manifest['sha'])
        assert r['binary']['sha256'] == flags['binary_sha256'] == manifest['hashes'][r['binary']['path']]
        for key, value in flags.items():
            if key.endswith('_sha256'):
                assert value in manifest['hashes'].values()
        if arm in binaries:
            assert binaries[arm] == r['binary']
            assert configurations[arm] == r['config_hash']
        binaries[arm] = r['binary']; configurations[arm] = r['config_hash']
        family, size = r['instance']['name'].rsplit('-', 1)
        wanted = cases.oracle(family, int(size), cases.generate(family, int(size)))
        answer = r['verdict']['answer']
        assert answer in (wanted[-1], 'unknown')
        secondary = r['metrics']['secondary']
        if answer != 'unknown':
            assert r['verdict']['verified_model_or_proof']
            assert secondary['check_answers'] == wanted
            assert r['metrics']['primary']['name'] == 'instructions:u'
            assert r['metrics']['primary']['value'] > 0
        else: assert not r['verdict']['verified_model_or_proof']
    return cells


def analyze(directory, output):
    rawdir = directory.parents[1]/experiment.SUITE
    manifest = json.loads((rawdir/'manifest.json').read_text())
    records = [run.benchstore.validate(json.loads(p.read_text())) for p in directory.glob('*.json')]
    cells = validate_records(records, manifest)
    for r in records:
        name = f"{r['instance']['name']}-{r['config']['id']}-{r['seed']}-{r['record_id']}"
        raw = json.loads((rawdir/(name+'.result.json')).read_text())
        assert raw['instructions'] == r['metrics']['primary']['value']
        payload = raw['payload']
        assert payload['answer'] == r['verdict']['answer']
        assert payload['verified'] == r['verdict']['verified_model_or_proof']
        if payload['answer'] != 'unknown':
            family, size = r['instance']['name'].rsplit('-', 1)
            text = cases.generate(family, int(size))
            answers, diagnostics = worker.driver_result(cases.parse(text), cases.oracle(family, int(size), text), payload['stdout'], r['config']['id'])
            assert answers == payload['check_answers'] and diagnostics == payload['diagnostics']
    output.mkdir(parents=True, exist_ok=True)
    rows = []
    for family, size in cases.CASES:
        case = f'{family}-{size}'
        for arm in experiment.ARMS:
            samples = [cells[(case, arm, seed)] for seed in experiment.SEEDS]
            solved = [r for r in samples if r['verdict']['answer'] != 'unknown']
            costs = [r['metrics']['primary']['value'] for r in solved]
            row = dict(case=case, arm=arm, solved=len(solved), total=len(samples),
                       instructions_min=min(costs) if costs else None,
                       instructions_median=statistics.median(costs) if costs else None,
                       instructions_max=max(costs) if costs else None)
            for label, field in [('definitions', 0), ('comparisons', 0), ('optimization', 0), ('optimization', 1), ('optimization', 2), ('optimization', 3)]:
                values = [r['metrics']['secondary']['diagnostics'][-1][label][field] for r in solved if label in r['metrics']['secondary']['diagnostics'][-1]]
                row[f'{label}_{field}_last_median'] = statistics.median(values) if values else None
            rows.append(row)
    with (output/'summary.csv').open('w') as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0])); writer.writeheader(); writer.writerows(rows)
    comparisons = []
    for control in experiment.ARMS:
        if control == 'all': continue
        for subset, families in [('all', None), ('original', run.FAMILIES), ('target', TARGETS.get(control))]:
            if subset == 'target' and families is None: continue
            for seeds in (list(range(10)), [103]):
                ratios, lost, gained, both_unknown = [], [], [], []
                for family, size in cases.CASES:
                    if families is not None and family not in families: continue
                    for seed in seeds:
                        name = f'{family}-{size}'; a, b = cells[(name, 'all', seed)], cells[(name, control, seed)]
                        au, bu = a['verdict']['answer'] == 'unknown', b['verdict']['answer'] == 'unknown'
                        if au and bu: both_unknown.append((name, seed))
                        elif au: lost.append((name, seed))
                        elif bu: gained.append((name, seed))
                        else: ratios.append(a['metrics']['primary']['value']/b['metrics']['primary']['value'])
                comparisons.append(dict(control=control, subset=subset, seeds='held-out-103' if seeds == [103] else '0-9',
                                        pairs=len(ratios), ratio=geomean(ratios), lost=lost, gained=gained, both_unknown=both_unknown))
    (output/'comparisons.json').write_text(json.dumps(comparisons, indent=2)+'\n')
    lines = ['| Case | Baseline | All | No coverage | No equalities | No cache | Eager |', '|---|---:|---:|---:|---:|---:|---:|']
    for family, size in cases.CASES:
        name = f'{family}-{size}'; values = []
        for arm in experiment.ARMS:
            row = next(r for r in rows if r['case'] == name and r['arm'] == arm)
            value = row['instructions_median']
            values.append(f"{value/1e6:.2f} ({row['solved']}/11)" if value else '— (0/11)')
        lines.append('| '+name+' | '+' | '.join(values)+' |')
    lines += ['', 'Median millions of instructions among known answers; Unknown costs excluded.', '',
              '| Comparator | Subset | Seeds | Pairs | All / comparator | Lost | Gained |', '|---|---|---|---:|---:|---:|---:|']
    for row in comparisons:
        ratio = f"{row['ratio']:.4f}" if row['ratio'] is not None else '—'
        lines.append(f"| {row['control']} | {row['subset']} | {row['seeds']} | {row['pairs']} | {ratio} | {len(row['lost'])} | {len(row['gained'])} |")
    (output/'tables.md').write_text('\n'.join(lines)+'\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('records', type=Path); parser.add_argument('output', type=Path)
    args = parser.parse_args(); analyze(args.records, args.output)
