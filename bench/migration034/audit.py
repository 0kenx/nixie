#!/usr/bin/env python3
"""Validate saved measurement identities and available SAT witnesses; never rerun solvers."""
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'bench/suite/scripts'))
import benchstore


def check_sat_model(instance, stdout):
    literals = [int(t) for line in stdout.splitlines() if line.startswith('v ')
                for t in line[2:].split() if t != '0']
    assert literals, 'Expected a DIMACS model'
    assignment = {}
    for lit in literals:
        assert abs(lit) not in assignment or assignment[abs(lit)] == (lit > 0)
        assignment[abs(lit)] = lit > 0
    clause = []
    checked = 0
    for line in Path(instance).read_text().splitlines():
        if not line.strip() or line.startswith(('c', 'p')):
            continue
        for lit in map(int, line.split()):
            if lit:
                clause.append(lit)
            else:
                assert any(assignment.get(abs(v)) == (v > 0) for v in clause)
                checked += 1
                clause = []
    assert not clause and checked > 0
    return checked


def main():
    manifest = json.loads((ROOT / 'bench/migration034/manifest.json').read_text())
    results_path = ROOT / manifest['results']
    rows = json.loads(results_path.read_text())
    assert len(rows) == 264
    assert len({(r['arm'], r['instance']['sha256']) for r in rows}) == 264
    models = []
    for row in rows:
        directory = ROOT / row['artifacts']
        record = json.loads((directory / 'record.json').read_text())
        benchstore.validate(record)
        assert record['metrics']['primary']['value'] == row['instructions']
        assert record['metrics']['secondary']['raw_answer'] == row['answer']
        assert record['binary']['sha256'] == row['key']['binary']
        stored = json.loads(benchstore.record_path(ROOT / 'precompile', record).read_text())
        assert benchstore.canonical_join_key(stored) == benchstore.canonical_join_key(record)
        assert stored['record_id'] == benchstore.record_id(stored)
        assert hashlib.sha256((ROOT / row['instance']['path']).read_bytes()).hexdigest() == row['instance']['sha256']
        if row['arm'] in ('kissat', 'cadical') and row['answer'] == 'sat':
            checked = check_sat_model(ROOT / row['instance']['path'], (directory / 'stdout.txt').read_text())
            models.append({'arm': row['arm'], 'instance': row['instance']['path'], 'clauses_checked': checked})
    assert len(models) == 24
    stats = {}
    for row in rows:
        if row['arm'] not in ('before', 'after') or row['instance']['kind'] != 'SAT':
            continue
        directory = ROOT / row['artifacts']
        output = (directory / 'stdout.txt').read_text() + '\n' + (directory / 'stderr.txt').read_text()
        counters = {k: int(v) for k, v in re.findall(r'^\s*(Decisions|Propagations|Conflicts|Restarts):\s+(\d+)', output, re.M)}
        assert len(counters) == 4
        stats.setdefault(row['instance']['sha256'], {})[row['arm']] = counters
    equal = sum(group['before'] == group['after'] for group in stats.values())
    assert len(stats) == 24
    log = (results_path.parent / 'run-corrected-references.log').read_text()
    summary = {'records_validated': len(rows), 'sat_models_checked': models,
               'native_sat_counter_pairs': len(stats), 'identical_native_sat_counter_pairs': equal,
               'corrected_pass_reused': sum(line.startswith('REUSE ') for line in log.splitlines()),
               'corrected_pass_executed': sum(line.startswith('DONE ') for line in log.splitlines())}
    (ROOT / 'bench/migration034/validation.json').write_text(json.dumps(summary, indent=2) + '\n')
    print({k: v for k, v in summary.items() if k != 'sat_models_checked'})
    print('Validated SAT reference models:', len(models))


if __name__ == '__main__':
    main()
