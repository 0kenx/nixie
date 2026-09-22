#!/usr/bin/env python3
"""Exact BV reference for the frozen binary-field workload (Z3 4.16.0)."""
import argparse
import datetime
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import tempfile
import time

import run as workload

Z3_SHA = 'ddb49568d3520e99799e364fb22f35fc67d887b1'
VERSION = 'Z3 version 4.16.0 - 64 bit'
HERE = Path(__file__).resolve().parent
sha256 = workload.sha256


def bv(value, width):
    assert 0 <= value < 1 << width
    return f'(_ bv{value} {width})'


def xor(terms):
    assert terms
    value = terms[0]
    for term in terms[1:]:
        value = f'(bvxor {value} {term})'
    return value


def remainder(value, polynomial):
    # Polynomial long division on integer coefficient bitmaps; the oracle
    # instead uses explicit coefficient arrays and convolution.
    while value.bit_length() >= polynomial.bit_length():
        value ^= polynomial << (value.bit_length() - polynomial.bit_length())
    return value


def definitions(polynomial):
    k = polynomial.bit_length() - 1
    width = 2 * k
    # Frobenius is F2-linear: square(sum x_i X^i) = sum x_i X^(2i).
    square = xor([f'(ite (= ((_ extract {i} {i}) a) #b1) '
                  f'{bv(remainder(1 << (2*i), polynomial), k)} {bv(0, k)})'
                  for i in range(k)])
    pieces = [f'(ite (= ((_ extract {i} {i}) b) #b1) '
              f'(bvshl ((_ zero_extend {k}) a) {bv(i, width)}) {bv(0, width)})'
              for i in range(k)]
    product = f'(let ((r{2*k-1} {xor(pieces)})) '
    for i in range(2*k-2, k-1, -1):
        product += (f'(let ((r{i} (ite (= ((_ extract {i} {i}) r{i+1}) #b1) '
                    f'(bvxor r{i+1} {bv(polynomial << (i-k), width)}) r{i+1}))) ')
    product += f'((_ extract {k-1} 0) r{k})' + ')' * k
    return (f'(define-fun square ((a (_ BitVec {k}))) (_ BitVec {k}) {square})\n'
            f'(define-fun multiply ((a (_ BitVec {k})) (b (_ BitVec {k}))) '
            f'(_ BitVec {k}) {product})\n')


def problem(case, seed):
    original, expected = workload.problem(case, seed)
    expected = dict(expected)
    kind = case['kind']
    if kind == 'prime':
        x = expected['prime_x']
        script = (f'(set-logic QF_NIA) (declare-const x Int)\n'
                  f'(assert (and (<= 0 x) (< x 257))) (assert (= x {x}))\n'
                  f'(assert (= (mod (* x x) 257) {x*x%257}))\n'
                  '(check-sat) (get-value (x))\n')
        return script, expected, original
    polynomial = int(case['polynomial'])
    k = polynomial.bit_length() - 1
    script = '(set-logic QF_BV)\n' + definitions(polynomial)
    if kind == 'wide':
        x = (1 << 117) ^ (seed + 3)
        y = (1 << 101) ^ (seed * 19 + 7)
        script += (f'(assert (= (multiply {bv(x,k)} {bv(y,k)}) '
                   f'{bv(workload.mul(x,y,polynomial),k)})) (check-sat)\n')
        return script, expected, original
    script += f'(declare-const x (_ BitVec {k}))\n'
    if kind == 'unsat':
        # Read the frozen target; the original generator has already checked
        # its complete root set with the independent coefficient-array oracle.
        target = int(re.findall(r'\(as ff(\d+) ', original)[-1])
        script += f'(assert (= (bvxor (square x) x) {bv(target,k)}))\n(check-sat)\n'
        return script, expected, original
    if kind in ['pair', 'budget']:
        script += f'(declare-const y (_ BitVec {k}))\n'
    for var, target in expected['equations']:
        chain = f'(let ((s0 {var})) '
        for i in range(1, expected['depth'] + 1):
            chain += f'(let ((s{i} (bvxor (square s{i-1}) {bv(1,k)}))) '
        chain += f's{expected["depth"]}' + ')' * (expected['depth'] + 1)
        script += f'(assert (= {chain} {bv(target,k)}))\n'
    expected['answer'] = 'sat'  # budget case also has a planted solution
    script += '(check-sat) (get-value (' + ' '.join(v for v, _ in expected['equations']) + '))\n'
    return script, expected, original


def verify(output, expected):
    if re.findall(r'^(sat|unsat|unknown)$', output, re.M) != [expected['answer']] or '(error' in output:
        raise ValueError(output)
    if expected['answer'] == 'unsat':
        assert expected['no_roots_checked']
    elif 'prime_x' in expected:
        match = re.search(r'\(x\s+(\d+)\)', output)
        assert match and int(match[1]) == expected['prime_x'], output
    elif not expected.get('ground_checked'):
        k = expected['polynomial'].bit_length() - 1
        for var, target in expected['equations']:
            match = re.search(r'\(' + var + r'\s+(#x[0-9a-fA-F]+|#b[01]+|\(_ bv\d+ \d+\))\)', output)
            assert match, output
            token = match[1]
            if token.startswith('#'):
                value = int(token[2:], 16 if token[1] == 'x' else 2)
                assert len(token[2:]) * (4 if token[1] == 'x' else 1) == k
            else:
                value, width = map(int, re.findall(r'\d+', token))
                assert width == k
            assert 0 <= value < 1 << k
            assert workload.iterate(value, expected['depth'], expected['polynomial']) == target, output


def self_test(binary):
    # Exhaustive translation oracle, not an assertion about Nixie's arithmetic.
    for polynomial in [7, 11, 13, 19, 283]:
        k = polynomial.bit_length() - 1
        terms = [f'(distinct (square {bv(x,k)}) {bv(workload.mul(x,x,polynomial),k)})'
                 for x in range(1 << k)]
        if k <= 4:
            terms += [f'(distinct (multiply {bv(x,k)} {bv(y,k)}) {bv(workload.mul(x,y,polynomial),k)})'
                      for x in range(1 << k) for y in range(1 << k)]
        script = '(set-logic QF_BV)\n' + definitions(polynomial)
        script += '(assert (or ' + ' '.join(terms) + ')) (check-sat)\n'
        result = subprocess.run([str(binary), '-in'], input=script, text=True, capture_output=True, check=True, timeout=120)
        assert result.stdout.strip() == 'unsat', result.stdout
    for case in workload.CASES:
        script, expected, _ = problem(case, 0)
        result = subprocess.run([str(binary), '-in'], input=script, text=True, capture_output=True, check=True, timeout=120)
        verify(result.stdout, expected)
    print('PASS: exhaustive tiny-field encoding, all F256 squares, all 13 functional cases')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('binary', type=Path)
    p.add_argument('--root', type=Path, default=Path('precompile'))
    p.add_argument('--first-seed', type=int, default=0)
    p.add_argument('--seeds', type=int, default=10)
    p.add_argument('--self-test', action='store_true')
    a = p.parse_args()
    binary = a.binary.resolve()
    version = subprocess.check_output([str(binary), '--version'], text=True).strip()
    assert version == VERSION, version
    if a.self_test:
        self_test(binary)
        return
    spec = importlib.util.spec_from_file_location('benchstore', HERE.parent / 'suite/scripts/benchstore.py')
    store = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(store)
    binary_hash = sha256(binary.read_bytes())
    flags = {'harness_sha256': sha256(Path(__file__).read_bytes()),
             'workload_sha256': sha256((HERE / 'run.py').read_bytes()),
             'cpu': 0, 'counter': 'instructions:u', 'cap_seconds': 120,
             'z3_version': version, 'encoding': 'bv-frobenius-convolution-division-v1',
             'seed_parameters': ['sat.random_seed', 'smt.random_seed']}
    host = platform.node()
    outdir = a.root / Z3_SHA / 'benchmark/ff-extension-z3-raw'
    outdir.mkdir(parents=True, exist_ok=True)
    tasks = [(case, seed, *problem(case, seed)) for case in workload.CASES
             for seed in range(a.first_seed, a.first_seed + a.seeds)]
    manifest = {'suite': 'ff-extension-z3', 'host': host, 'source': Z3_SHA,
                'binary_sha256': binary_hash, 'configs': [{'id': 'z3-reference', 'flags': flags}],
                'seeds': list(range(a.first_seed, a.first_seed + a.seeds)),
                'cells': [{'name': c['name'], 'seed': s, 'sha256': sha256(script.encode())}
                          for c, s, script, _, _ in tasks]}
    path = outdir / f'manifest-s{a.first_seed}-{a.seeds}.json'
    encoded = json.dumps(manifest, indent=2) + '\n'
    if path.exists():
        assert path.read_text() == encoded, 'changed manifest'
    else:
        path.write_text(encoded)
    existing = list(store.iter_records(a.root))
    for case, seed, script, expected, original in tasks:
        instance_hash = sha256(script.encode())
        if any(r['git']['sha_long'] == Z3_SHA and r['binary']['sha256'] == binary_hash
               and r['host']['id'] == host and r['instance']['sha256'] == instance_hash
               and r['seed'] == seed and r['config_hash'] == store.canonical_flags(flags)
               for _, r in existing):
            print(f'reuse {case["name"]} seed={seed}', flush=True)
            continue
        stem = outdir / f'{case["name"]}-s{seed}'
        if stem.with_suffix('.out').exists() or stem.with_suffix('.smt2').exists():
            raise RuntimeError(f'unrecorded previous attempt: {stem}')
        stem.with_suffix('.smt2').write_text(script)
        cmd = ['taskset', '-c', '0', 'perf', 'stat', '-x,', '-e', 'instructions:u', '--',
               str(binary), f'sat.random_seed={seed}', f'smt.random_seed={seed}', str(stem.with_suffix('.smt2'))]
        before = time.monotonic()
        try:
            result = subprocess.run(cmd, capture_output=True, timeout=120, check=False, env=os.environ)
        except subprocess.TimeoutExpired as exc:
            stem.with_suffix('.out').write_bytes(exc.stdout or b'')
            stem.with_suffix('.err').write_bytes(exc.stderr or b'')
            raise RuntimeError(f'censored cell: {stem}') from exc
        elapsed = time.monotonic() - before
        stem.with_suffix('.out').write_bytes(result.stdout)
        stem.with_suffix('.err').write_bytes(result.stderr)
        assert result.returncode == 0, result.stderr
        instructions = 0
        for line in result.stderr.decode().splitlines():
            parts = line.split(',')
            if len(parts) > 4 and 'instructions' in parts[2] and parts[0].isdigit():
                assert float(parts[4]) >= 99, line
                instructions += int(parts[0])
        assert instructions > 0
        verify(result.stdout.decode(), expected)
        rec = {'schema': store.SCHEMA, 'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
               'suite': 'ff-extension-z3', 'host': {'id': host, 'cpu': platform.machine(), 'os': platform.platform()},
               'git': {'sha_long': Z3_SHA, 'sha_short': Z3_SHA[:8], 'dirty': False},
               'binary': {'path': str(binary), 'sha256': binary_hash},
               'instance': {'name': case['name'], 'sha256': instance_hash, 'family': case['kind'],
                            'sat_expected': expected['answer'] == 'sat'},
               'config': {'id': 'z3-reference', 'flags': flags, 'features': [], 'cmdline': cmd},
               'seed': seed, 'arm': {'role': 'reference'},
               'metrics': {'primary': {'name': 'instructions:u', 'value': instructions},
                           'secondary': {'stdout_sha256': sha256(result.stdout),
                                         'logical_instance_sha256': sha256(original.encode())},
                           'wall_clock_s': elapsed, 'counter_coverage_verified': True},
               'verdict': {'answer': expected['answer'], 'verified_model_or_proof': True}}
        store.validate(rec)
        with tempfile.NamedTemporaryFile(mode='w', suffix='.json') as f:
            json.dump(rec, f)
            f.flush()
            store.cmd_record(argparse.Namespace(record=f.name, root=a.root))
        print(f'{case["name"]} seed={seed} {expected["answer"]} instructions={instructions}', flush=True)


if __name__ == '__main__':
    main()
