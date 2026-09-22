#!/usr/bin/env python3
"""Run immutable, independently verified binary-field CLI benchmark cells."""
import argparse
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
CASES = json.loads((HERE / 'cases.json').read_text())
BASELINE = 'df564313'
sha256 = lambda data: hashlib.sha256(data).hexdigest()


def mul(a, b, polynomial):
    """Independent coefficient convolution and high-to-low long division."""
    k = polynomial.bit_length() - 1
    coefficients = [0] * (2 * k + 1)
    for i in range(k):
        for j in range(k):
            coefficients[i + j] ^= ((a >> i) & 1) & ((b >> j) & 1)
    for i in range(2 * k - 1, k - 1, -1):
        if coefficients[i]:
            for j in range(k + 1):
                coefficients[i - k + j] ^= (polynomial >> j) & 1
    return sum(coefficients[i] << i for i in range(k))


def iterate(x, depth, polynomial):
    for _ in range(depth):
        x = mul(x, x, polynomial) ^ 1
    return x


def problem(case, seed):
    kind = case['kind']
    if kind == 'prime':
        x = 192 + seed % 63
        return (f'(set-logic QF_FF) (declare-const x (_ FiniteField 257))\n'
                f'(assert (= x #f{x}m257)) (assert (= (ff.mul x x) #f{x*x%257}m257))\n'
                '(check-sat) (get-value (x))\n'), {'answer': 'sat', 'prime_x': x}
    polynomial = int(case['polynomial'])
    q = 1 << (polynomial.bit_length() - 1)
    sort = f'(_ BinaryField {polynomial})'
    literal = lambda x: f'(as ff{x} {sort})'
    if kind == 'wide':
        x = (1 << 117) ^ (seed + 3)
        y = (1 << 101) ^ (seed * 19 + 7)
        value = mul(x, y, polynomial)
        return (f'(set-logic QF_FF) (assert (= (ff.mul {literal(x)} {literal(y)}) '
                f'{literal(value)})) (check-sat)\n'), {'answer': 'sat', 'ground_checked': True}
    depth = case['depth']
    def chain(var):
        # Alternating addition avoids flattening repeated products into 2^depth
        # operands. SMT let bindings and hash-consing retain the shared DAG.
        out = f'(let ((s0 {var})) '
        for i in range(1, depth + 1):
            out += f'(let ((s{i} (ff.add (ff.mul s{i-1} s{i-1}) {literal(1)}))) '
        return out + f's{depth}' + ')' * (depth + 1)
    x = 3 * q // 4 + (seed * 7 + 3) % (q // 4)
    y = 3 * q // 4 + (seed * 11 + 1) % (q // 4)
    header = f'(set-logic QF_FF) (declare-const x {sort})\n'
    if case.get('certified'):
        header += '(set-option :certified-mode true)\n'
    equations = []
    if kind == 'unsat':
        image = {mul(v, v, polynomial) ^ v for v in range(q)}
        missing = sorted(set(range(q)) - image)
        target = missing[seed % len(missing)]
        script = header + f'(assert (= (ff.add (ff.mul x x) x) {literal(target)}))\n(check-sat)\n'
        return script, {'answer': 'unsat', 'no_roots_checked': True}
    target_x = iterate(x, depth, polynomial)
    script = header + f'(assert (= {chain("x")} {literal(target_x)}))\n'
    equations.append(('x', target_x))
    if kind in ['pair', 'budget']:
        target_y = iterate(y, depth, polynomial)
        script = header + f'(declare-const y {sort})\n' + script[len(header):]
        script += f'(assert (= {chain("y")} {literal(target_y)}))\n'
        equations.append(('y', target_y))
    answer = 'unknown' if kind == 'budget' else 'sat'
    script += '(check-sat)\n'
    if answer == 'sat':
        script += '(get-value (' + ' '.join(var for var, _ in equations) + '))\n'
    return script, {'answer': answer, 'equations': equations, 'depth': depth, 'polynomial': polynomial}


def verify(output, expected):
    answers = re.findall(r'^(sat|unsat|unknown)$', output, re.M)
    if answers != [expected['answer']] or '(error' in output:
        raise ValueError(f'unexpected solver output: {output}')
    if expected['answer'] == 'unknown':
        return False
    if expected['answer'] == 'unsat':
        assert expected['no_roots_checked']
        return True
    if 'prime_x' in expected:
        match = re.search(r'\(x #f(\d+)m257\)', output)
        assert match and int(match[1]) == expected['prime_x'], output
    elif not expected.get('ground_checked'):
        polynomial = expected['polynomial']
        for var, target in expected['equations']:
            match = re.search(r'\(' + var + r' \(as ff(\d+) \(_ BinaryField (\d+)\)\)\)', output)
            assert match and int(match[2]) == polynomial, output
            value = int(match[1])
            assert 0 <= value < 1 << (polynomial.bit_length() - 1), output
            assert iterate(value, expected['depth'], polynomial) == target, output
    return True


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('binary', type=Path)
    p.add_argument('--sha', required=True)
    p.add_argument('--role', choices=['baseline', 'treatment'], required=True)
    p.add_argument('--root', type=Path, required=True)
    p.add_argument('--first-seed', type=int, default=0)
    p.add_argument('--seeds', type=int, default=10)
    a = p.parse_args()
    source = HERE.parent.parent
    spec = importlib.util.spec_from_file_location('benchstore', source / 'bench/suite/scripts/benchstore.py')
    store = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(store)
    binary = a.binary.resolve()
    binary_hash = sha256(binary.read_bytes())
    host = platform.node()
    flags = {'harness_sha256': sha256(Path(__file__).read_bytes()), 'cpu': 0,
             'counter': 'instructions:u', 'cap_seconds': 120, 'build': 'workspace-release-default'}
    existing = list(store.iter_records(a.root))
    outdir = a.root / a.sha / 'benchmark' / 'ff-extension-raw'
    outdir.mkdir(parents=True, exist_ok=True)
    tasks = []
    for case in CASES:
        for seed in range(a.first_seed, a.first_seed + a.seeds):
            script, expected = problem(case, seed)
            tasks.append((case, seed, script, expected, sha256(script.encode())))
    manifest = {'suite': 'ff-extension', 'host': host, 'source': a.sha, 'binary_sha256': binary_hash,
                'configs': [{'id': 'exact-computation', 'flags': flags}],
                'seeds': list(range(a.first_seed, a.first_seed + a.seeds)),
                'cells': [{'name': c['name'], 'seed': s, 'sha256': h} for c, s, _, _, h in tasks]}
    manifest_path = outdir / f'manifest-s{a.first_seed}-{a.seeds}.json'
    encoded = json.dumps(manifest, indent=2) + '\n'
    if manifest_path.exists():
        assert manifest_path.read_text() == encoded, 'changed manifest'
    else:
        manifest_path.write_text(encoded)
    for case, seed, script, expected, instance_hash in tasks:
        matches = [r for _, r in existing if r['git']['sha_long'] == a.sha
                   and r['binary']['sha256'] == binary_hash and r['host']['id'] == host
                   and r['instance']['sha256'] == instance_hash and r['seed'] == seed
                   and r['config_hash'] == store.canonical_flags(flags)]
        if matches:
            print(f'reuse {case["name"]} seed={seed}', flush=True)
            continue
        stem = outdir / f'{case["name"]}-s{seed}'
        if stem.with_suffix('.out').exists() or stem.with_suffix('.smt2').exists():
            raise RuntimeError(f'unrecorded previous attempt: {stem}')
        stem.with_suffix('.smt2').write_text(script)
        cmd = ['taskset', '-c', '0', 'perf', 'stat', '-x,', '-e', 'instructions:u',
               '--', str(binary), '--no-color', str(stem.with_suffix('.smt2'))]
        before = time.monotonic()
        try:
            result = subprocess.run(cmd, capture_output=True, timeout=120, check=False,
                                    env={**os.environ, 'NIXIE_SAT_SEED': str(seed)})
        except subprocess.TimeoutExpired as exc:
            stem.with_suffix('.out').write_bytes(exc.stdout or b'')
            stem.with_suffix('.err').write_bytes(exc.stderr or b'')
            raise RuntimeError(f'censored cell: {stem}') from exc
        elapsed = time.monotonic() - before
        stem.with_suffix('.out').write_bytes(result.stdout)
        stem.with_suffix('.err').write_bytes(result.stderr)
        if result.returncode:
            raise RuntimeError(f'failed cell {stem}: {result.stderr.decode()}')
        instructions = 0
        for line in result.stderr.decode().splitlines():
            parts = line.split(',')
            if len(parts) > 4 and 'instructions' in parts[2] and parts[0].isdigit():
                if float(parts[4]) < 99:
                    raise RuntimeError(f'multiplexed counter: {line}')
                instructions += int(parts[0])
        if instructions <= 0:
            raise RuntimeError('no instruction counter')
        verified = verify(result.stdout.decode(), expected)
        rec = {'schema': store.SCHEMA, 'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
               'suite': 'ff-extension', 'host': {'id': host, 'cpu': platform.machine(), 'os': platform.platform()},
               'git': {'sha_long': a.sha, 'sha_short': a.sha, 'dirty': False},
               'binary': {'path': str(binary), 'sha256': binary_hash},
               'instance': {'name': case['name'], 'sha256': instance_hash, 'family': case['kind'],
                            'sat_expected': expected['answer'] == 'sat'},
               'config': {'id': 'exact-computation', 'flags': flags, 'features': ['default'], 'cmdline': cmd},
               'seed': seed, 'arm': {'role': a.role},
               'metrics': {'primary': {'name': 'instructions:u', 'value': instructions},
                           'secondary': {'stdout_sha256': sha256(result.stdout)},
                           'wall_clock_s': elapsed, 'counter_coverage_verified': True},
               'verdict': {'answer': expected['answer'], 'verified_model_or_proof': verified}}
        store.validate(rec)
        with tempfile.NamedTemporaryFile(mode='w', suffix='.json') as f:
            json.dump(rec, f)
            f.flush()
            store.cmd_record(argparse.Namespace(record=f.name, root=a.root))
        print(f'{case["name"]} seed={seed} {expected["answer"]} instructions={instructions}', flush=True)


if __name__ == '__main__':
    main()
