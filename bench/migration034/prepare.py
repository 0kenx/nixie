#!/usr/bin/env python3
"""Freeze a stratified, path-hash-selected sample before measuring solvers."""
import collections
import hashlib
import json
from pathlib import Path
import platform
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[2]
BEFORE = 'af14b6d2f800685b2737b02189cdae44d23f5459'
AFTER = '862c6d948f73133f1229831a0240f2558e8dbfe5'
SUITE = 'migration034-satlib-smtlib-30s'
SALT = 'nixie-migration034-20261110:'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def rank(value):
    return digest((SALT + str(value)).encode())


def main():
    out = ROOT / 'precompile' / AFTER / 'benchmark' / SUITE
    out.mkdir(parents=True, exist_ok=True)
    instances = []
    provenance = json.loads((ROOT / 'bench/migration034/satlib-provenance.json').read_text())
    for family in provenance:
        for entry in family['selected']:
            source = ROOT / entry['path']
            data = source.read_bytes()
            assert digest(data) == entry['sha256']
            # SATLIB appends a historical '%' end marker and another zero.
            # Remove only this footer, then validate the original clause count.
            lines = data.decode().splitlines()
            stop = next((i for i, line in enumerate(lines) if line.strip() == '%'), len(lines))
            assert all(line.strip() in ('', '0') for line in lines[stop + 1:])
            text = '\n'.join(lines[:stop]) + '\n'
            header = next(line.split() for line in lines[:stop] if line.startswith('p '))
            literals = [int(t) for line in lines[:stop] if line.strip() and not line.startswith(('c', 'p')) for t in line.split()]
            assert literals.count(0) == int(header[3]) and literals[-1] == 0
            assert all(abs(lit) <= int(header[2]) for lit in literals)
            path = out / 'corpus' / 'SATLIB' / family['family'] / source.name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
            instances.append({'kind': 'SAT', 'family': family['family'],
                              'path': str(path.relative_to(ROOT)), 'sha256': digest(path.read_bytes()),
                              'source': entry['path'], 'source_sha256': entry['sha256'],
                              'expected': 'unsat' if family['family'].startswith('uuf') else 'sat'})
    pools = {}
    for logic in sorted((ROOT / 'smt-lib/non-incremental').iterdir()):
        if not logic.is_dir():
            continue
        groups = collections.defaultdict(list)
        for path in logic.rglob('*.smt2'):
            if path.stat().st_size <= 1024 * 1024:
                family = path.relative_to(logic).parts[0]
                groups[family].append(path)
        pools[logic.name] = {'eligible_files': sum(map(len, groups.values())), 'families': len(groups)}
        for paths in groups.values():
            paths.sort(key=lambda p: rank(p.relative_to(ROOT)))
        selected = []
        while len(selected) < 4:
            progressed = False
            for family in sorted(groups, key=lambda f: rank(logic.name + '/' + f)):
                while groups[family]:
                    path = groups[family].pop(0)
                    text = path.read_text(errors='strict')
                    if len(re.findall(r'\(check-sat\s*\)', text)) != 1 or '(check-sat-assuming' in text:
                        continue
                    selected.append(path)
                    progressed = True
                    break
                if len(selected) == 4:
                    break
            assert progressed, 'Insufficient eligible files in ' + logic.name
        for path in selected:
            data = path.read_bytes()
            status = re.search(rb'\(set-info\s+:status\s+(sat|unsat|unknown)\s*\)', data)
            instances.append({'kind': 'SMT', 'family': logic.name,
                              'subfamily': path.relative_to(logic).parts[0],
                              'path': str(path.relative_to(ROOT)), 'sha256': digest(data),
                              'expected': status[1].decode() if status else 'unknown'})
    assert len(instances) == 72
    arms = [
        {'name': 'before', 'engine': 'nixie', 'sha': BEFORE, 'binary': f'precompile/{BEFORE}/nixie',
         'version': BEFORE, 'role': 'baseline', 'kinds': ['SAT', 'SMT'], 'build': 'release, default features, LTO=true, codegen-units=1'},
        {'name': 'after', 'engine': 'nixie', 'sha': AFTER, 'binary': f'precompile/{AFTER}/nixie-parity',
         'version': AFTER, 'role': 'treatment', 'kinds': ['SAT', 'SMT'], 'build': 'release, default features, LTO=true, codegen-units=1'},
        {'name': 'z3', 'engine': 'z3', 'sha': AFTER, 'binary': shutil.which('z3'),
         'version': subprocess.check_output(['z3', '-version'], text=True).strip(), 'role': 'reference', 'kinds': ['SAT', 'SMT'],
         'git_note': 'sha denotes result-hosting Nixie revision, not Z3 source; identity pins the actual binary hash and version'},
    ]
    for name in ['kissat', 'cadical']:
        reference = ROOT.parent / 'temp' / name
        binary = reference / 'build' / name
        arms.append({'name': name, 'engine': name,
                     'sha': subprocess.check_output(['git', '-C', str(reference), 'rev-parse', 'HEAD'], text=True).strip(),
                     'binary': str(binary), 'version': subprocess.check_output([str(binary), '--version'], text=True).strip(),
                     'role': 'reference', 'kinds': ['SAT']})
    for arm in arms:
        arm['sha256'] = digest(Path(arm['binary']).read_bytes())
    cpu = next(line.split(':', 1)[1].strip() for line in Path('/proc/cpuinfo').read_text().splitlines() if line.startswith('model name'))
    manifest = {'suite': SUITE, 'timeout_s': 30, 'selection_salt': SALT, 'seeds': [0],
                'seed_note': 'One default-configuration snapshot; zero is the store index, no solver seed override.',
                'cpus': [2, 5], 'perf': shutil.which('perf'),
                'host': {'id': platform.node(), 'cpu': cpu, 'os': platform.platform()},
                'smt_eligible_pools': pools, 'arms': arms, 'instances': instances,
                'results': str((out / 'results.json').relative_to(ROOT))}
    assert manifest['perf']
    path = ROOT / 'bench/migration034/manifest.json'
    assert not path.exists(), 'Do not change a registered sample after measurement'
    path.write_text(json.dumps(manifest, indent=2) + '\n')
    print('Pinned', len(instances), 'instances,', sum(len([a for a in arms if i['kind'] in a['kinds']]) for i in instances), 'cells')


if __name__ == '__main__':
    main()
