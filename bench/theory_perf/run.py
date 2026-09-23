#!/usr/bin/env python3
"""Immutable whole-process instruction cells for the audited theory APIs."""
import argparse
import datetime
from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
import re
import subprocess
import tempfile
import time

SUITE = 'audited-theories-z3'
GRID = [(f, n) for f in ['fp16-32', 'fp32-16', 'fp64-32'] for n in [1, 4]] + [
    (f, n) for f, sizes in [('sets', [4, 16, 32]), ('arrangements', [3, 5, 7]),
                          ('arrays', [16, 64, 256])] for n in sizes]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def expressions(text):
    root = []
    stack = [root]
    for token in re.findall(r'\(|\)|[^\s()]+', text):
        if token == '(':
            node = []
            stack[-1].append(node)
            stack.append(node)
        elif token == ')':
            if len(stack) == 1:
                raise ValueError('unbalanced response')
            stack.pop()
        else:
            stack[-1].append(token)
    if len(stack) != 1:
        raise ValueError('unclosed response')
    return root


def rational(expr):
    stack = [(expr, False)]
    values = []
    while stack:
        node, combine = stack.pop()
        if isinstance(node, str):
            values.append(Fraction(node))
        elif combine:
            if node[0] == '-' and len(node) == 2:
                values[-1] = -values[-1]
            elif node[0] == '/' and len(node) == 3:
                denominator = values.pop()
                numerator = values.pop()
                values.append(numerator / denominator)
            else:
                raise ValueError('unsupported rational')
        else:
            stack.append((node, True))
            stack.extend((child, False) for child in reversed(node[1:]))
    if len(values) != 1:
        raise ValueError('invalid rational')
    return values[0]


def verify(output, reference, family, count):
    if not reference:
        if output != 'sat\nunsat\nsat\n':
            raise ValueError('Nixie did not validate all three verdicts')
        return
    exprs = expressions(output)
    if len(exprs) != 5 or [exprs[i] for i in [0, 2, 3]] != ['sat', 'unsat', 'sat']:
        raise ValueError('Z3 did not return SAT/UNSAT/SAT and two witnesses')
    expected = count if family.startswith('fp') or family == 'arrangements' else (
        count + 1 if family == 'sets' else count - 1)
    for model in [exprs[1], exprs[4]]:
        if not isinstance(model, list) or len(model) != expected:
            raise ValueError('incomplete model')
        if any(not isinstance(pair, list) or len(pair) != 2 for pair in model):
            raise ValueError('invalid model entry')
        if family == 'arrangements':
            if [pair[0] for pair in model] != [f'x{i}' for i in range(count)]:
                raise ValueError('wrong shared variables')
            if len({rational(pair[1]) for pair in model}) != count:
                raise ValueError('shared values are not distinct')
        elif any(pair[1] != 'true' for pair in model):
            raise ValueError('witness predicate failed')


def instructions(stderr):
    total = 0
    for line in stderr.splitlines():
        parts = line.split(',')
        if len(parts) > 4 and 'instructions' in parts[2] and parts[0].isdigit():
            if float(parts[4]) < 99:
                raise ValueError('multiplexed instruction counter')
            total += int(parts[0])
    if total <= 0:
        raise ValueError('no instruction counter')
    return total


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--binary', type=Path, required=True)
    p.add_argument('--driver-binary', type=Path, required=True)
    p.add_argument('--driver', type=Path, required=True)
    p.add_argument('--sha', required=True)
    p.add_argument('--role', choices=['baseline', 'treatment', 'reference'], required=True)
    p.add_argument('--root', type=Path, required=True)
    p.add_argument('--first-seed', type=int, default=0)
    p.add_argument('--seeds', type=int, default=10)
    p.add_argument('--families', nargs='+')
    p.add_argument('--lock', type=Path, required=True)
    a = p.parse_args()
    source = Path(__file__).resolve().parents[2]
    spec = importlib.util.spec_from_file_location('benchstore', source / 'bench/suite/scripts/benchstore.py')
    store = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(store)
    binary = a.binary.resolve()
    reference = a.role == 'reference'
    version = subprocess.check_output([str(binary), '--version'], text=True).strip() if reference else 'Nixie standalone API'
    flags = {'driver_sha256': digest(a.driver.read_bytes()), 'cpu': 0,
             'counter': 'instructions:u', 'cap_seconds': 120,
             'build': 'external-release-debug1', 'lock_sha256': digest(a.lock.read_bytes()),
             'compiler': subprocess.check_output(['rustc', '--version'], text=True).strip(),
             'engine': version, 'runner_sha256': digest(Path(__file__).read_bytes())}
    print(version, flush=True)
    existing = list(store.iter_records(a.root))
    binary_hash = digest(binary.read_bytes())
    raw = a.root / a.sha / 'benchmark' / SUITE / a.role
    raw.mkdir(parents=True, exist_ok=True)
    failed = 0
    for family, count in GRID:
        if a.families and family not in a.families:
            continue
        for seed in range(a.first_seed, a.first_seed + a.seeds):
            name = f'{family}-{count}'
            script = subprocess.check_output([str(a.driver_binary.resolve()), family, str(count), str(seed), 'emit'])
            ihash = digest(script)
            matches = [r for _, r in existing if r['git']['sha_long'] == a.sha
                       and r['binary']['sha256'] == binary_hash and r['host']['id'] == platform.node()
                       and r['instance']['sha256'] == ihash and r['seed'] == seed
                       and r['config_hash'] == store.canonical_flags(flags)]
            if matches:
                print(f'reuse {name} s{seed}', flush=True)
                continue
            stem = raw / f'{name}-s{seed}'
            if stem.with_suffix('.out').exists():
                raise RuntimeError(f'unrecorded prior attempt: {stem}')
            stem.with_suffix('.smt2').write_bytes(script)
            args = [str(binary), '-in'] if reference else [str(binary), family, str(count), str(seed), 'solve']
            cmd = ['taskset', '-c', '0', 'perf', 'stat', '-x,', '-e', 'instructions:u', '--'] + args
            before = time.monotonic()
            error = ''
            try:
                result = subprocess.run(cmd, input=script if reference else None, capture_output=True, timeout=120, check=False)
                stdout, stderr = result.stdout, result.stderr
                if result.returncode:
                    error = f'exit {result.returncode}'
            except subprocess.TimeoutExpired as exc:
                stdout, stderr = exc.stdout or b'', exc.stderr or b''
                error = 'timeout'
            elapsed = time.monotonic() - before
            stem.with_suffix('.out').write_bytes(stdout)
            stem.with_suffix('.err').write_bytes(stderr)
            counter = 0
            try:
                counter = instructions(stderr.decode())
                verify(stdout.decode(), reference, family, count)
            except (ValueError, ZeroDivisionError) as exc:
                error = error or str(exc)
            record = {'schema': store.SCHEMA, 'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                      'suite': SUITE, 'host': {'id': platform.node(), 'cpu': platform.machine(), 'os': platform.platform()},
                      'git': {'sha_long': a.sha, 'sha_short': a.sha, 'dirty': False},
                      'binary': {'path': str(binary), 'sha256': binary_hash},
                      'instance': {'name': name, 'sha256': ihash, 'family': family, 'sat_expected': True},
                      'config': {'id': 'audited-theories', 'flags': flags, 'features': ['default'], 'cmdline': cmd},
                      'seed': seed, 'arm': {'role': a.role},
                      'metrics': {'primary': {'name': 'instructions:u', 'value': counter},
                                  'secondary': {'stdout_sha256': digest(stdout), 'failure': error, 'checks': 3},
                                  'wall_clock_s': elapsed, 'counter_coverage_verified': counter > 0},
                      'verdict': {'answer': 'unknown' if error else 'sat', 'verified_model_or_proof': not error}}
            store.validate(record)
            with tempfile.NamedTemporaryFile(mode='w', suffix='.json') as f:
                json.dump(record, f); f.flush()
                store.cmd_record(argparse.Namespace(record=f.name, root=a.root))
            failed += bool(error)
            print(f'{name} s{seed}: {error or counter}', flush=True)
    if failed:
        raise SystemExit(f'{failed} failed cells (retained, not solved)')


if __name__ == '__main__':
    main()
