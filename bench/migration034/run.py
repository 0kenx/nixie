#!/usr/bin/env python3
"""Run the pinned migration snapshot once per content-addressed cell."""
import argparse
import concurrent.futures
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import signal
import subprocess
import sys
import time
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'bench/suite/scripts'))
import benchstore


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def parse_answer(output):
    answers = []
    for line in output.splitlines():
        token = line.strip().lower()
        if token in ('sat', 'unsat', 'unknown'):
            answers.append(token)
        elif token in ('s satisfiable', 's unsatisfiable', 's unknown'):
            answers.append({'s satisfiable': 'sat', 's unsatisfiable': 'unsat',
                            's unknown': 'unknown'}[token])
    return answers


def parse_instructions(text):
    counts = []
    for line in text.splitlines():
        fields = line.split(';')
        if len(fields) < 3 or not re.fullmatch(r'(?:cpu_(?:core|atom)/)?instructions(?::u|/u)', fields[2]):
            continue
        if fields[0].strip() == '<not counted>':
            continue
        if not fields[0].strip().isdigit():
            raise ValueError('Instruction PMU unavailable: ' + line)
        if len(fields) > 4 and float(fields[4].replace('%', '')) < 99.9:
            raise ValueError('Multiplexed instruction PMU: ' + line)
        counts.append(int(fields[0]))
    if len(counts) != 1:
        raise ValueError(f'Expected exactly one active PMU, got {counts}')
    return counts[0]


def command(arm, instance):
    binary = arm['binary']
    path = instance['path']
    sat = instance['kind'] == 'SAT'
    if arm['engine'] == 'nixie':
        return [binary, '--stats', '--no-color'] + (['--dimacs'] if sat else []) + [path]
    if arm['engine'] == 'z3':
        # Z3 treats a bare argument containing '=' as a parameter assignment.
        literal = ['--'] if '=' in path else []
        return [binary, '-st', '-dimacs' if sat else '-smt2', *literal, path]
    if arm['engine'] == 'cadical':
        return [binary, '--stats', path]
    return [binary, '--statistics', path]


def run_cell(manifest, arm, instance, cpu):
    flags = {'timeout_s': 30, 'memory_bytes': 8589934592, 'cpu': cpu,
             'engine': arm['engine'], 'version': arm['version'],
             'argv_options': command(arm, instance)[1:-1],
             'measurement': 'perf-instructions-u-with-timeout-prlimit-v1',
             'configuration': 'default', 'environment': 'clean-nixie-variables'}
    key = {'host': manifest['host']['id'], 'sha': arm['sha'],
           'binary': arm['sha256'], 'instance': instance['sha256'],
           'suite': manifest['suite'], 'flags': flags, 'seed': 0}
    ident = hashlib.sha256(json.dumps(key, sort_keys=True).encode()).hexdigest()[:24]
    directory = ROOT / 'precompile' / arm['sha'] / 'benchmark' / manifest['suite'] / ident
    result_path = directory / 'result.json'
    if result_path.exists():
        result = json.loads(result_path.read_text())
        assert result['key'] == key
        print('REUSE', arm['name'], instance['path'], flush=True)
        return result
    directory.mkdir(parents=True, exist_ok=True)
    # Refuse to overwrite an interrupted cell; diagnose it before superseding.
    with (directory / 'started.json').open('x') as stream:
        json.dump(key, stream, indent=2)
    argv = ['taskset', '-c', str(cpu), manifest['perf'], 'stat', '-x', ';',
            '-o', str(directory / 'perf.txt'), '-e', 'instructions:u', '--',
            'timeout', '--signal=TERM', '--kill-after=1s', '30s',
            'prlimit', '--as=8589934592', '--', *command(arm, instance)]
    env = {k: v for k, v in os.environ.items()
           if not k.startswith(('NIXIE_', 'OXIZ_', 'Z3_')) and k not in ('STATS',)}
    env['LC_ALL'] = 'C'
    (directory / 'command.json').write_text(json.dumps(argv, indent=2) + '\n')
    start = time.monotonic()
    emergency = False
    with (directory / 'stdout.txt').open('x') as stdout, (directory / 'stderr.txt').open('x') as stderr:
        process = subprocess.Popen(argv, cwd=ROOT, env=env, stdout=stdout, stderr=stderr,
                                   start_new_session=True)
        try:
            status = process.wait(timeout=35)
        except subprocess.TimeoutExpired:
            emergency = True
            os.killpg(process.pid, signal.SIGKILL)
            status = process.wait()
    elapsed = time.monotonic() - start
    output = (directory / 'stdout.txt').read_text(errors='replace')
    errors = (directory / 'stderr.txt').read_text(errors='replace')
    answers = parse_answer(output)
    timed_out = status in (124, 137) or emergency
    error = status not in (0, 10, 20, 124, 137) or '(error ' in output or 'panicked at' in errors
    answer = answers[0] if len(answers) == 1 and not error and not timed_out else 'unknown'
    outcome = 'timeout' if timed_out else 'error' if error or len(answers) != 1 else answer
    instructions = parse_instructions((directory / 'perf.txt').read_text())
    result = {'key': key, 'arm': arm['name'], 'instance': instance, 'exit_code': status,
              'outcome': outcome, 'answer': answer, 'answers': answers,
              'instructions': instructions, 'wall_clock_s': elapsed,
              'artifacts': str(directory.relative_to(ROOT)),
              'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    # A differential verdict is NOT a checked proof/model. Keep the benchmark
    # response explicitly in secondary data; never fabricate certification.
    record = {'schema': benchstore.SCHEMA, 'created_utc': result['created_utc'],
              'suite': manifest['suite'], 'host': manifest['host'],
              'git': {'sha_long': arm['sha'], 'sha_short': arm['sha'], 'dirty': False},
              'binary': {'path': arm['binary'], 'sha256': arm['sha256']},
              'instance': {'name': instance['family'] + '/' + Path(instance['path']).name[:100], 'sha256': instance['sha256'],
                           'family': instance['family'], 'sat_expected': instance['expected']},
              'config': {'id': arm['name'], 'flags': flags,
                         'features': arm.get('build', 'external reference'), 'cmdline': argv},
              'seed': 0, 'arm': {'role': arm['role']},
              'metrics': {'primary': {'name': 'instructions', 'value': instructions},
                          'secondary': {'raw_answer': answer, 'outcome': outcome,
                                        'exit_code': status, 'censored': timed_out},
                          'wall_clock_s': elapsed, 'counter_coverage_verified': True},
              'verdict': {'answer': 'unknown', 'verified_model_or_proof': False}}
    record_path = directory / 'record.json'
    record_path.write_text(json.dumps(record, indent=2) + '\n')
    benchstore.cmd_record(SimpleNamespace(record=str(record_path), root=str(ROOT / 'precompile')))
    result_path.write_text(json.dumps(result, indent=2) + '\n')
    print('DONE', arm['name'], instance['path'], outcome, f'{elapsed:.3f}s', instructions, flush=True)
    return result


def run_lane(manifest, lane):
    results = []
    for index, instance in enumerate(manifest['instances']):
        if index % 2 != lane:
            continue
        arms = [a for a in manifest['arms'] if instance['kind'] in a['kinds']]
        # Rotate order, keeping each instance's arms on the same physical CPU.
        shift = index % len(arms)
        arms = arms[shift:] + arms[:shift]
        for arm in arms:
            results.append(run_cell(manifest, arm, instance, manifest['cpus'][lane]))
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, default=Path('bench/migration034/manifest.json'))
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    assert manifest['timeout_s'] == 30 and len(manifest['cpus']) == 2
    assert platform.node() == manifest['host']['id']
    for arm in manifest['arms']:
        assert digest(arm['binary']) == arm['sha256']
    for instance in manifest['instances']:
        assert digest(instance['path']) == instance['sha256']
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as executor:
        results = list(executor.map(lambda lane: run_lane(manifest, lane), range(2)))
    path = ROOT / manifest['results']
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps([r for lane in results for r in lane], indent=2) + '\n')
    print('RESULTS', path, flush=True)


if __name__ == '__main__':
    main()
