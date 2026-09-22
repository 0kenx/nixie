"""Resume untouched anchor cells after an audited empty-counter timeout.

This supervisor is outside the measured worker. It never executes a cell again.
An absent counter is an unmeasured Unknown, never zero measured instructions.
"""
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys

if not __debug__:
    raise RuntimeError('recovery validation requires Python assertions (no -O/PYTHONOPTIMIZE)')


def recover(directory, log):
    trace = log.read_text()
    assert 'in perf_count' in trace and trace.rstrip().endswith('AssertionError')
    assert 'count = perf_count(' in trace
    pending = [p for p in directory.glob('*.command.json')
               if not Path(str(p).removesuffix('.command.json')+'.result.json').exists()]
    assert len(pending) == 1, 'do not infer results for ambiguous interruptions'
    command_path = pending[0]
    prefix = str(command_path).removesuffix('.command.json')
    evidence = {}
    for ext in ('.perf', '.stdout', '.stderr'):
        p = Path(prefix+ext)
        data = p.read_bytes()
        assert not data, 'only the observed empty-counter timeout is recoverable'
        evidence[ext] = hashlib.sha256(data).hexdigest()
    # The frozen runner reaches perf_count with empty stdout only after its
    # timeout branch. Otherwise JSON decoding fails before reaching that call.
    # Its monotonic elapsed time was lost; do not reconstruct or fabricate it.
    note = dict(reason='outer timeout with empty perf output; counter and elapsed time unavailable',
                controller_log=str(log), controller_log_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),
                recovered_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                raw_sha256=evidence, supervisor_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    result = dict(instructions=0, wall_clock_s=None,
                  payload=dict(answer='unknown', verified=False, timeout=True,
                               region_unmeasured=True, recovery=note),
                  command=json.loads(command_path.read_text())['command'])
    with Path(prefix+'.result.json').open('x') as out:
        out.write(json.dumps(result, indent=2)+'\n')
    print('Preserved unmeasured Unknown:', command_path.name, flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory', type=Path, required=True)
    parser.add_argument('--failed-log', type=Path, required=True)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    assert args.command
    recover(args.directory, args.failed_log)
    for attempt in range(1, 1057):
        log = args.directory.parent/f'resume-attempt-{attempt}.log'
        with log.open('x') as out:
            status = subprocess.run(args.command, stdout=out, stderr=subprocess.STDOUT).returncode
        if status == 0:
            print('Matrix complete:', log, flush=True)
            return
        recover(args.directory, log)
    sys.exit('too many interrupted cells')


if __name__ == '__main__':
    main()
