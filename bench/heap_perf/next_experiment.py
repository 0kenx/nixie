"""Preregistered six-arm heap experiment; every cell is executed at most once."""
import argparse
import datetime
import json
import os
from pathlib import Path
import platform
import signal
import subprocess
import sys
import time

import next_cases as cases
from run import ROOT, benchstore, digest, perf_count, summarize

SUITE = 'heap-four-optimizations-v1'
BASELINE_SHA = 'cb50c87ec8331659e40c9fe257bf7191f2184d47'
ARMS = ('baseline', 'all', 'no_coverage', 'no_equalities', 'no_cache', 'eager')
SEEDS = list(range(10)) + [103]
WORKER = Path(__file__).with_name('next_worker.py').resolve()


def finish_execution(raw, execution):
    """Parse an existing execution without rerunning it or inventing counters."""
    stderr = raw.with_suffix('.stderr').read_text()
    assert 'AssertionError' not in stderr and 'WRONG ANSWER' not in stderr, stderr
    if execution['timeout']:
        payload = dict(answer='unknown', verified=False, timeout=True)
    else:
        assert execution['status'] == 0, stderr
        payload = json.loads(raw.with_suffix('.stdout').read_text())
    perf = raw.with_suffix('.perf')
    if execution['timeout'] and perf.exists() and not perf.read_text().strip():
        count = 0
        payload['region_unmeasured'] = True
        payload['measurement_note'] = 'outer timeout; perf output empty; zero is an unmeasured sentinel'
    else:
        count = perf_count(perf)
    payload['system_loadavg_before'] = execution['load_before']
    payload['system_loadavg_after'] = execution['load_after']
    return dict(instructions=count, wall_clock_s=execution['elapsed'],
                command=execution['command'], payload=payload)


def run(args):
    sha = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    assert not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=ROOT, text=True)
    directory = args.store / sha[:8] / 'benchmark' / SUITE
    directory.mkdir(parents=True, exist_ok=True)
    versions = dict(rustc=subprocess.check_output(['rustc', '--version'], text=True).strip(),
                    python=platform.python_version(), perf=subprocess.check_output(['perf', '--version'], text=True).strip(),
                    z3=subprocess.check_output([args.z3, '--version'], text=True).strip(),
                    cvc5=subprocess.check_output([args.cvc5, '--version'], text=True).splitlines()[0])
    files = [Path(__file__).resolve(), WORKER, WORKER.with_name('next_cases.py'), WORKER.with_name('run.py'),
             WORKER.with_name('anchor_cases.py'), WORKER.with_name('legacy_client.rs'),
             ROOT/'bench/suite/scripts/benchstore.py', ROOT/'nixie-solver/examples/heap_perf_next.rs', ROOT/'nixie-solver/examples/heap_perf_next_driver/mod.rs',
             Path(args.baseline), Path(args.driver)]
    hashes = {str(p): digest(p) for p in files}
    signatures = {str(p): (p.stat().st_ino, p.stat().st_size, p.stat().st_mtime_ns) for p in files}
    manifest = dict(suite=SUITE, sha=sha, baseline_library=BASELINE_SHA, versions=versions,
                    arms=ARMS, seeds=SEEDS, cases=cases.CASES, hashes=hashes)
    manifest = json.loads(json.dumps(manifest))
    manifest_path = directory/'manifest.json'
    if manifest_path.exists(): assert json.loads(manifest_path.read_text()) == manifest
    else: manifest_path.write_text(json.dumps(manifest, indent=2)+'\n')
    records = []
    host = dict(id=platform.node(), cpu=next(line.split(':', 1)[1].strip() for line in Path('/proc/cpuinfo').read_text().splitlines() if line.startswith('model name'))+f' cpu{args.cpu}', os=platform.platform())
    for family, size in cases.CASES:
        case = directory/f'{family}-{size}.heap'
        content = cases.generate(family, size)
        expected = cases.oracle(family, size, content)
        if case.exists(): assert case.read_text() == content
        else: case.write_text(content)
        for seed in SEEDS:
            order = ARMS[seed % len(ARMS):] + ARMS[:seed % len(ARMS)]
            for arm in order:
                for p in files:
                    stat = p.stat()
                    assert signatures[str(p)] == (stat.st_ino, stat.st_size, stat.st_mtime_ns), f'mutated frozen input: {p}'
                binary = args.baseline if arm == 'baseline' else args.driver
                flags = dict(mode=arm, cpu=args.cpu, cap_s=20, cleanup_s=3, pythonhashseed=0,
                             environment='NIXIE_/HEAP_PERF_ cleared', pmu='instructions:u',
                             harness_sha256=hashes[str(Path(__file__).resolve())], worker_sha256=hashes[str(WORKER)],
                             cases_sha256=hashes[str(WORKER.with_name('next_cases.py'))],
                             benchstore_sha256=hashes[str(ROOT/'bench/suite/scripts/benchstore.py')],
                             checker_utilities_sha256=hashes[str(WORKER.with_name('run.py'))],
                             anchor_cases_sha256=hashes[str(WORKER.with_name('anchor_cases.py'))],
                             client_sha256=hashes[str(WORKER.with_name('legacy_client.rs') if arm == 'baseline' else ROOT/'nixie-solver/examples/heap_perf_next.rs')],
                             shared_client_sha256=hashes[str(ROOT/'nixie-solver/examples/heap_perf_next_driver/mod.rs')],
                             library_revision=BASELINE_SHA if arm == 'baseline' else sha,
                             binary_sha256=hashes[binary], build_profile='release', lto=True,
                             codegen_units=1, strip='none', incremental=False,
                             max_conflicts=10000, max_decisions=100000, timeout_ms=0)
                rec = dict(schema=benchstore.SCHEMA, created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                           suite=SUITE, host=host, git=dict(sha_long=sha, sha_short=sha[:8], dirty=False),
                           binary=dict(path=binary, sha256=hashes[binary]),
                           instance=dict(name=case.stem, sha256=digest(case), family=family, sat_expected=expected[-1] == 'sat'),
                           config=dict(id=arm, flags=flags, features=['default'], cmdline=[]), seed=seed,
                           arm=dict(role='baseline' if arm == 'baseline' else 'treatment' if arm == 'all' else 'null'))
                rec['config_hash'] = benchstore.canonical_flags(flags)
                destination = benchstore.record_path(args.store, rec)
                if destination.exists():
                    previous = benchstore.validate(json.loads(destination.read_text()))
                    assert benchstore.canonical_join_key(previous) == benchstore.canonical_join_key(rec)
                    records.append(previous)
                    continue
                raw = directory/f'{case.stem}-{arm}-{seed}-{benchstore.record_id(rec)}'
                result_path, execution_path = raw.with_suffix('.result.json'), raw.with_suffix('.execution.json')
                if result_path.exists(): result = json.loads(result_path.read_text())
                else:
                    if execution_path.exists(): execution = json.loads(execution_path.read_text())
                    else:
                        assert not raw.with_suffix('.command.json').exists(), f'interrupted execution; preserve and investigate {raw}'
                        env = {k: v for k, v in os.environ.items() if not k.startswith(('NIXIE_', 'HEAP_PERF_'))}
                        env['PYTHONHASHSEED'] = '0'
                        command = ['taskset', '-c', str(args.cpu), 'perf', 'stat', '-x,', '-o', str(raw.with_suffix('.perf')),
                                   '-e', 'instructions:u', '--', sys.executable, str(WORKER), '--case', str(case),
                                   '--driver', binary, '--arm', arm, '--seed', str(seed), '--cvc5', args.cvc5, '--z3', args.z3]
                        raw.with_suffix('.command.json').write_text(json.dumps(dict(command=command, pythonhashseed=0)))
                        load_before = os.getloadavg(); start = time.monotonic()
                        with raw.with_suffix('.stdout').open('x') as out, raw.with_suffix('.stderr').open('x') as err:
                            process = subprocess.Popen(command, stdout=out, stderr=err, env=env, start_new_session=True)
                            timeout = False
                            try: status = process.wait(timeout=20)
                            except subprocess.TimeoutExpired:
                                timeout = True
                                os.killpg(process.pid, signal.SIGINT)
                                try: status = process.wait(timeout=3)
                                except subprocess.TimeoutExpired:
                                    os.killpg(process.pid, signal.SIGKILL); status = process.wait()
                        execution = dict(status=status, timeout=timeout, elapsed=time.monotonic()-start, command=command,
                                         load_before=load_before, load_after=os.getloadavg())
                        # Persist termination evidence BEFORE reading potentially
                        # missing PMU output; no traceback-based recovery needed.
                        execution_path.write_text(json.dumps(execution, indent=2)+'\n')
                    result = finish_execution(raw, execution)
                    result_path.write_text(json.dumps(result, indent=2)+'\n')
                payload = result['payload']
                rec['config']['cmdline'] = result['command']
                rec['metrics'] = dict(primary=dict(name='unmeasured_region' if payload.get('region_unmeasured') else 'instructions:u', value=result['instructions']),
                                      secondary={k: v for k, v in payload.items() if k not in ('stdout', 'stderr')},
                                      wall_clock_s=result['wall_clock_s'],
                                      # Coverage describes the instrumented region.
                                      # A missing sample is explicitly unmeasured,
                                      # never an available zero-cost observation.
                                      counter_coverage_verified=True)
                rec['verdict'] = dict(answer=payload['answer'], verified_model_or_proof=payload['verified'])
                rec['reference_versions'] = versions
                benchstore.validate(rec)
                rec['record_id'] = benchstore.record_id(rec)
                pending = raw.with_suffix('.record.json')
                pending.write_text(json.dumps(rec, indent=2)+'\n')
                benchstore.cmd_record(argparse.Namespace(record=str(pending), root=str(args.store)))
                pending.unlink()
                records.append(rec)
                print(f'{case.stem} {arm} seed={seed} {payload["answer"]} {result["instructions"]}', flush=True)
    assert all(digest(p) == hashes[str(p)] for p in files)
    summarize(records, directory)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', required=True)
    parser.add_argument('--driver', required=True)
    parser.add_argument('--cvc5', required=True)
    parser.add_argument('--z3', required=True)
    parser.add_argument('--store', type=Path, default=ROOT/'precompile')
    parser.add_argument('--cpu', type=int, default=2)
    run(parser.parse_args())
