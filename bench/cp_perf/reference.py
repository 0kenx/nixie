#!/usr/bin/env python3
"""Equivalent CP/Z3 scheduling workloads, independent model checks and stored counters."""
import argparse
from collections import defaultdict
import datetime
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import platform
import re
import statistics
import subprocess
import tempfile
import time

FAMILIES = ['unknown', 'present', 'absent', 'shared', 'blocked', 'wide', 'sparse']
SUITE = 'cp-scheduling-z3'
DEFAULT_SHAPES = [(4, 4), (8, 16)]


def parse_shape(value):
    try:
        count, width = map(int, value.split('x'))
    except ValueError as error:
        raise argparse.ArgumentTypeError('expected positive TASKSxWIDTH') from error
    if count <= 0 or width <= 0:
        raise argparse.ArgumentTypeError('expected positive TASKSxWIDTH')
    return count, width


def digest(data):
    return hashlib.sha256(data).hexdigest()


def problem(family, count, width, seed):
    """The same declarations as cp_scheduling_perf.rs, with native Int starts."""
    offset = 1 << 140 if family == 'wide' else 0
    duration = width if family == 'blocked' else 1
    capacity = 0 if family == 'blocked' else count
    guards = ['p0' if family == 'shared' else f'p{i}' for i in range(count)]
    starts = [f's{i}' for i in range(count * (5 if family == 'sparse' else 1))]
    values = [offset + (j + seed % width) % width for j in range(width)]
    lines = ['(set-logic QF_LIA)', '(set-option :produce-models true)',
             f'(set-option :smt.random_seed {seed})', f'(set-option :sat.random_seed {seed})']
    for guard in dict.fromkeys(guards):
        lines.append(f'(declare-const {guard} Bool)')
    for i, start in enumerate(starts):
        # The original driver leaves unrelated variables unshifted/unrotated.
        domain = values if i < count else list(range(width))
        lines += [f'(declare-const {start} Int)',
                  '(assert (or ' + ' '.join(f'(= {start} {v})' for v in domain) + '))']
    # With nonnegative constant demands, an overload must start at a present
    # task's start. Combine coincident endpoints through exact half-open guards.
    lines.append(f'(assert (<= 0 {capacity}))')
    for i in range(count):
        loads = [f'(ite (and {guards[j]} (<= s{j} s{i}) (< s{i} (+ s{j} {duration}))) 1 0)'
                 for j in range(count)]
        lines.append(f'(assert (=> {guards[i]} (<= (+ {" ".join(loads)}) {capacity})))')
    names = list(dict.fromkeys(guards)) + starts
    for _ in range(2):
        lines.append('(push 1)')
        if family in ['present', 'absent']:
            for guard in guards:
                lines.append(f'(assert {guard if family == "present" else "(not " + guard + ")"})')
        lines += ['(check-sat)', f'(get-value ({" ".join(names)}))', '(pop 1)']
    lines.append('(exit)')
    return '\n'.join(lines) + '\n'


def expressions(text):
    """Iterative parser for Z3's ground get-value responses; no recursive walk."""
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


def verify_z3(output, family, count, width):
    exprs = expressions(output)
    if len(exprs) != 4 or exprs[0] != 'sat' or exprs[2] != 'sat':
        raise ValueError('expected two decisive SAT answers and two complete models')
    offset = 1 << 140 if family == 'wide' else 0
    duration = width if family == 'blocked' else 1
    capacity = 0 if family == 'blocked' else count
    guards = ['p0' if family == 'shared' else f'p{i}' for i in range(count)]
    starts = [f's{i}' for i in range(count * (5 if family == 'sparse' else 1))]
    for pairs in [exprs[1], exprs[3]]:
        model = {}
        for pair in pairs:
            if not isinstance(pair, list) or len(pair) != 2 or pair[0] in model:
                raise ValueError('invalid model entry')
            name, value = pair
            if value in ['true', 'false']:
                value = value == 'true'
            elif isinstance(value, list):
                if len(value) != 2 or value[0] != '-':
                    raise ValueError('nonconstant integer')
                value = -int(value[1])
            else:
                value = int(value)
            model[name] = value
        if set(model) != set(guards + starts):
            raise ValueError('missing or extra model variable')
        for i, start in enumerate(starts):
            low = offset if i < count else 0
            if type(model[start]) is not int or not low <= model[start] < low + width:
                raise ValueError('start outside its declared domain')
        for guard in guards:
            if type(model[guard]) is not bool:
                raise ValueError('non-Boolean presence')
            if family in ['present', 'absent'] and model[guard] != (family == 'present'):
                raise ValueError('violated presence assertion')
        # Independent model replay: direct load at every active task start.
        for i in range(count):
            if not model[guards[i]]:
                continue
            timepoint = model[f's{i}']
            load = sum(model[guards[j]] and model[f's{j}'] <= timepoint < model[f's{j}'] + duration
                       for j in range(count))
            if load > capacity:
                raise ValueError('cumulative overload')


def run(a):
    spec = importlib.util.spec_from_file_location('benchstore', a.source / 'bench/suite/scripts/benchstore.py')
    store = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(store)
    binary = a.binary.resolve()
    binary_hash = digest(binary.read_bytes())
    driver_hash = digest((a.source / 'nixie-solver/examples/cp_scheduling_perf.rs').read_bytes())
    script_hash = digest(Path(__file__).read_bytes())
    host = platform.node()
    version = subprocess.check_output([str(binary), '-version'], text=True).strip() if a.arm == 'reference' else 'Nixie'
    existing = list(store.iter_records(a.root))
    modes = ['z3'] if a.arm == 'reference' else ['solver', 'certified']
    for mode in modes:
        flags = {'engine': mode, 'driver_sha256': driver_hash, 'harness_sha256': script_hash,
                 'version': version, 'cpu': 0, 'pmu': 'instructions:u', 'cap_s': 120, 'rounds': 2,
                 'build': 'installed' if mode == 'z3' else 'external-default-features-release-debug1'}
        config_hash = store.canonical_flags(flags)
        raw = a.root / a.sha / 'benchmark/cp-z3-raw' / config_hash
        raw.mkdir(parents=True, exist_ok=True)
        for count, width in a.shapes:
            for family in a.families:
                name = f'{family}-{count}x{width}'
                for seed in range(a.first_seed, a.first_seed + a.seeds):
                    smt = problem(family, count, width, seed)
                    instance_hash = digest(smt.encode())
                    matches = [r for _, r in existing if r['git']['sha_long'] == a.sha
                               and r['suite'] == SUITE and r['binary']['sha256'] == binary_hash
                               and r['host']['id'] == host and r['instance']['sha256'] == instance_hash
                               and r['seed'] == seed and r['config_hash'] == config_hash]
                    if matches:
                        print(f'reuse {mode} {name} seed={seed}', flush=True)
                        continue
                    stem = raw / f'{name}-s{seed}'
                    if stem.with_suffix('.out').exists():
                        raise RuntimeError(f'previous unrecorded attempt: {stem}')
                    smt_path = stem.with_suffix('.smt2')
                    smt_path.write_text(smt)
                    argv = [str(binary), '-smt2', str(smt_path)] if mode == 'z3' else [
                        str(binary), mode, family, str(count), str(width), str(seed), '2']
                    command = ['taskset', '-c', '0', 'perf', 'stat', '-x,', '-e', 'instructions:u', '--', *argv]
                    start = time.monotonic()
                    try:
                        result = subprocess.run(command, capture_output=True, timeout=120, check=False)
                    except subprocess.TimeoutExpired as error:
                        stem.with_suffix('.out').write_bytes(error.stdout or b'')
                        stem.with_suffix('.err').write_bytes(error.stderr or b'')
                        raise RuntimeError(f'censored: {mode} {name} {seed}') from error
                    elapsed = time.monotonic() - start
                    stem.with_suffix('.out').write_bytes(result.stdout)
                    stem.with_suffix('.err').write_bytes(result.stderr)
                    if result.returncode:
                        raise RuntimeError(f'failed: {mode} {name} {seed}: {result.stderr.decode()}')
                    output = result.stdout.decode()
                    if mode == 'z3':
                        verify_z3(output, family, count, width)
                    elif len(re.findall(r'^round \d+ Sat \d+ \d+ \d+$', output, re.M)) != 2 or output.splitlines()[-1] != 'sat':
                        raise ValueError('Nixie did not return two checked SAT results')
                    instructions = 0
                    for line in result.stderr.decode().splitlines():
                        parts = line.split(',')
                        if len(parts) > 4 and 'instructions' in parts[2] and parts[0].isdigit():
                            if float(parts[4]) < 99:
                                raise ValueError('multiplexed counter')
                            instructions += int(parts[0])
                    if instructions <= 0:
                        raise ValueError('missing instruction counter')
                    record = {'schema': store.SCHEMA, 'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                              'suite': SUITE, 'host': {'id': host, 'cpu': platform.machine(), 'os': platform.platform()},
                              'git': {'sha_long': a.sha, 'sha_short': a.sha, 'dirty': False},
                              'binary': {'path': str(binary), 'sha256': binary_hash},
                              'instance': {'name': name, 'sha256': instance_hash, 'family': family, 'sat_expected': True},
                              'config': {'id': mode, 'flags': flags, 'features': ['default'], 'cmdline': command},
                              'seed': seed, 'arm': {'role': a.arm},
                              'metrics': {'primary': {'name': 'instructions:u', 'value': instructions},
                                          'secondary': {'stdout_sha256': digest(result.stdout)},
                                          'wall_clock_s': elapsed, 'counter_coverage_verified': True},
                              'verdict': {'answer': 'sat', 'verified_model_or_proof': True}}
                    with tempfile.NamedTemporaryFile(mode='w', suffix='.json') as f:
                        json.dump(record, f)
                        f.flush()
                        store.cmd_record(argparse.Namespace(record=f.name, root=a.root))
                    print(f'{mode} {name} seed={seed} instructions={instructions}', flush=True)


def report(a):
    def read(sha):
        rows = {}
        for path in (a.root / sha / 'benchmark/runs' / SUITE).glob('*.json'):
            r = json.loads(path.read_text())
            if a.first_seed <= r['seed'] < a.first_seed + a.seeds:
                key = (r['config']['id'], r['instance']['name'], r['seed'])
                if key in rows:
                    raise ValueError(f'ambiguous record {key}')
                rows[key] = r
        return rows
    base, cand, reference = read(a.baseline), read(a.treatment), read(a.reference)
    groups = defaultdict(list)
    rows = []
    for mode in ['solver', 'certified']:
        for count, width in a.shapes:
            for family in a.families:
                name = f'{family}-{count}x{width}'
                for seed in range(a.first_seed, a.first_seed + a.seeds):
                    b, c, z = base[(mode, name, seed)], cand[(mode, name, seed)], reference[('z3', name, seed)]
                    assert b['config_hash'] == c['config_hash']
                    assert b['metrics']['secondary']['stdout_sha256'] == c['metrics']['secondary']['stdout_sha256']
                    assert b['host'] == c['host'] == z['host']
                    assert b['instance']['sha256'] == c['instance']['sha256'] == z['instance']['sha256']
                    assert b['verdict'] == c['verdict'] == z['verdict']
                    bv, cv, zv = [r['metrics']['primary']['value'] for r in [b, c, z]]
                    for group in [mode, f'{mode}-{family}', f'{mode}-{count}x{width}', f'{mode}-{name}']:
                        groups[group].append((bv, cv, zv))
                    rows.append({'mode': mode, 'instance': name, 'seed': seed, 'baseline': bv, 'candidate': cv, 'z3': zv})
    for group, triples in sorted(groups.items()):
        geo = lambda xs: math.exp(statistics.mean(math.log(x) for x in xs))
        cb = geo(c / b for b, c, z in triples)
        bz = geo(b / z for b, c, z in triples)
        cz = geo(c / z for b, c, z in triples)
        print(f'{group:27} n={len(triples):3} previous/Z3={bz:.4f} current/Z3={cz:.4f} current/previous={cb:.4f}')
    print(f'{len(rows)} paired comparisons; all decisive SAT, independently checked models; no lost samples')
    if a.csv:
        import csv
        with a.csv.open('w') as f:
            writer = csv.DictWriter(f, fieldnames=rows[0].keys())
            writer.writeheader()
            writer.writerows(rows)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    runner = sub.add_parser('run')
    runner.add_argument('--source', type=Path, required=True)
    runner.add_argument('--binary', type=Path, required=True)
    runner.add_argument('--sha', required=True)
    runner.add_argument('--arm', choices=['baseline', 'treatment', 'reference'], required=True)
    reporter = sub.add_parser('report')
    reporter.add_argument('--baseline', required=True)
    reporter.add_argument('--treatment', required=True)
    reporter.add_argument('--reference', required=True)
    reporter.add_argument('--csv', type=Path)
    for command in [runner, reporter]:
        command.add_argument('--root', type=Path, required=True)
        command.add_argument('--shape', dest='shapes', type=parse_shape, action='append',
                             help='TASKSxWIDTH, repeatable; default: 4x4 and 8x16')
        command.add_argument('--family', dest='families', choices=FAMILIES, action='append',
                             help='repeatable; default: all families')
        command.add_argument('--first-seed', type=int, default=0)
        command.add_argument('--seeds', type=int, default=10)
    args = parser.parse_args()
    args.shapes = list(dict.fromkeys(args.shapes or DEFAULT_SHAPES))
    args.families = list(dict.fromkeys(args.families or FAMILIES))
    (run if args.command == 'run' else report)(args)
