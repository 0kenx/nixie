#!/usr/bin/env python3
"""Run/reuse immutable CP benchmark cells; see README.md before use."""
import argparse
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import subprocess
import tempfile
import time

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('binary', type=Path)
p.add_argument('--sha', required=True)
p.add_argument('--role', choices=['baseline', 'treatment'], required=True)
p.add_argument('--source', type=Path, required=True)
p.add_argument('--root', type=Path, required=True, help='shared precompile directory')
p.add_argument('--driver', type=Path, required=True)
p.add_argument('--first-seed', type=int, default=0)
p.add_argument('--seeds', type=int, default=10)
a = p.parse_args()
spec = importlib.util.spec_from_file_location('benchstore', a.source / 'bench/suite/scripts/benchstore.py')
store = importlib.util.module_from_spec(spec)
spec.loader.exec_module(store)
sha256 = lambda data: hashlib.sha256(data).hexdigest()
binary = a.binary.resolve()
binary_hash = sha256(binary.read_bytes())
host = platform.node()
flags = {'driver_sha256': sha256(a.driver.read_bytes()), 'cpu': 0, 'counter': 'instructions:u',
         'cap_seconds': 120, 'build': 'external-default-features-release-debug1', 'rounds': 2}
existing = list(store.iter_records(a.root))
output_dir = a.root / a.sha / 'benchmark' / 'cp-scheduling-raw'
output_dir.mkdir(parents=True, exist_ok=True)
for mode in ['callback', 'solver', 'certified']:
    for count, width in ([(8, 8), (32, 16)] if mode == 'callback' else [(4, 4)]):
        for family in ['unknown', 'present', 'absent', 'shared', 'blocked', 'wide', 'sparse']:
            name = f'{mode}-{family}-{count}x{width}'
            instance = {'mode': mode, 'family': family, 'tasks': count, 'width': width}
            instance_hash = sha256(json.dumps(instance, sort_keys=True).encode())
            for seed in range(a.first_seed, a.first_seed + a.seeds):
                matches = [r for _, r in existing if r['git']['sha_long'] == a.sha
                           and r['binary']['sha256'] == binary_hash and r['host']['id'] == host
                           and r['instance']['sha256'] == instance_hash and r['seed'] == seed
                           and r['config_hash'] == store.canonical_flags(flags)]
                if matches:
                    print(f'reuse {name} seed={seed}', flush=True)
                    continue
                stem = output_dir / f'{name}-s{seed}'
                # Failures are immutable evidence too, not an invitation to retry.
                if stem.with_suffix('.out').exists():
                    raise RuntimeError(f'unrecorded previous attempt: {stem}')
                cmd = ['taskset', '-c', '0', 'perf', 'stat', '-x,', '-e', 'instructions:u',
                       '--', str(binary), mode, family, str(count), str(width), str(seed), '2']
                before = time.monotonic()
                try:
                    result = subprocess.run(cmd, capture_output=True, timeout=120, check=False)
                except subprocess.TimeoutExpired as exc:
                    stem.with_suffix('.out').write_bytes(exc.stdout or b'')
                    stem.with_suffix('.err').write_bytes(exc.stderr or b'')
                    raise RuntimeError(f'censored cell: {name} seed={seed}') from exc
                elapsed = time.monotonic() - before
                stem.with_suffix('.out').write_bytes(result.stdout)
                stem.with_suffix('.err').write_bytes(result.stderr)
                if result.returncode:
                    raise RuntimeError(f'failed cell: {name} seed={seed}: {result.stderr.decode()}')
                instructions = 0
                for line in result.stderr.decode().splitlines():
                    parts = line.split(',')
                    if len(parts) > 4 and 'instructions' in parts[2] and parts[0].isdigit():
                        if float(parts[4]) < 99:
                            raise RuntimeError(f'multiplexed counter: {line}')
                        instructions += int(parts[0])
                if instructions <= 0:
                    raise RuntimeError('no instruction counter')
                answer = result.stdout.decode().splitlines()[-1]
                expected = 'unknown' if mode == 'callback' else 'sat'
                if answer != expected:
                    raise RuntimeError(f'verdict {answer} != {expected}')
                rec = {'schema': store.SCHEMA, 'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                       'suite': 'cp-scheduling', 'host': {'id': host, 'cpu': platform.machine(), 'os': platform.platform()},
                       'git': {'sha_long': a.sha, 'sha_short': a.sha, 'dirty': False},
                       'binary': {'path': str(binary), 'sha256': binary_hash},
                       'instance': {'name': name, 'sha256': instance_hash, 'family': f'{mode}-{family}',
                                    'sat_expected': mode != 'callback'},
                       'config': {'id': 'exact-computation', 'flags': flags, 'features': ['default'], 'cmdline': cmd},
                       'seed': seed, 'arm': {'role': a.role},
                       'metrics': {'primary': {'name': 'instructions:u', 'value': instructions},
                                   'secondary': {'stdout_sha256': sha256(result.stdout)},
                                   'wall_clock_s': elapsed, 'counter_coverage_verified': True},
                       'verdict': {'answer': answer, 'verified_model_or_proof': mode != 'callback'}}
                store.validate(rec)
                with tempfile.NamedTemporaryFile(mode='w', suffix='.json') as f:
                    json.dump(rec, f)
                    f.flush()
                    store.cmd_record(argparse.Namespace(record=f.name, root=a.root))
                print(f'{name} seed={seed} instructions={instructions}', flush=True)
