#!/usr/bin/env python3
"""Measure registered diagnostic indices without changing their CPU assignment."""
import argparse
import concurrent.futures
import json
import platform
from pathlib import Path

import run


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('manifest', type=Path)
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    assert manifest['timeout_s'] == 30 and len(manifest['cpus']) == 2
    assert platform.node() == manifest['host']['id']
    indices = manifest['selected_indices']
    assert len(indices) == len(set(indices))
    for arm in manifest['arms']:
        assert run.digest(arm['binary']) == arm['sha256']
    for index in indices:
        instance = manifest['instances'][index]
        assert run.digest(instance['path']) == instance['sha256']

    def lane(number):
        results = []
        for index in indices:
            if index % 2 != number:
                continue
            instance = manifest['instances'][index]
            arms = [a for a in manifest['arms'] if instance['kind'] in a['kinds']]
            shift = index % len(arms)
            for arm in arms[shift:] + arms[:shift]:
                results.append(run.run_cell(
                    manifest, arm, instance, manifest['cpus'][number], instance.get('seed', 0)))
        return results

    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as executor:
        rows = list(executor.map(lane, range(2)))
    output = run.ROOT / manifest['results']
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps([r for part in rows for r in part], indent=2) + '\n')


if __name__ == '__main__':
    main()
