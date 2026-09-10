#!/usr/bin/env python3
"""Direct-output, within-list consumer counts, not persistent savings or cycles."""

import argparse
from collections import Counter, defaultdict
from itertools import groupby
import json
from pathlib import Path


FIELDS = ('lists', 'visits', 'hits', 'product_visits', 'product_hits',
          'both_sides_screen', 'one_side_screen')


def integer(value, minimum=0):
    assert type(value) is int and value >= minimum, 'invalid nonnegative integer'
    return value


def validate(report):
    assert report['schema'] == 'nixie-watch-groups/1'
    p = report['products']
    assert p['schema'] == 'nixie-elimination-products/1'
    for key in ('skipped_lists', 'skipped_entries'):
        assert integer(report[key]) == 0, 'omitted watch samples'
    for key in ('omitted_batches', 'omitted_outputs', 'omitted_lists', 'omitted_entries'):
        assert integer(p[key]) == 0, 'incomplete product census'
    stride = integer(report['stride'], 1)
    assert integer(p['batches']) <= integer(p['batch_limit'], 1)
    assert len(p['lists']) == integer(report['samples']) <= integer(p['trace_list_limit'], 1)
    assert len(p['lists']) == (integer(report['lists_seen']) + stride - 1) // stride
    seen = set()
    previous = -1
    for row in p['births']:
        assert len(row) == 5
        output, batch, left, right, width = map(integer, row)
        assert previous < output < integer(p['origin_slot_limit'], 1)
        assert output not in seen and batch < p['batches']
        assert left < output and right < output and left != right and width >= 2
        seen.add(output)
        previous = output
    visits = hits = 0
    bins = [0] * 4
    for index, row in enumerate(p['lists']):
        assert len(row) == 3
        ordinal, conflict_bin, entries = row
        assert integer(ordinal) == index * stride
        assert integer(conflict_bin) < 4
        for entry in entries:
            assert len(entry) == 2
            clause, hit = map(integer, entry)
            assert clause < 2**32 and hit in (0, 1)
            hits += hit
        visits += len(entries)
        bins[conflict_bin] += len(entries)
    assert visits == integer(p['trace_entries']) == integer(report['visited'])
    assert visits <= integer(p['trace_entry_limit'], 1)
    assert hits == integer(report['hits'])
    assert len(report['by_conflicts']) == 4
    assert bins == [integer(row[0]) for row in report['by_conflicts']]
    return p


def analyze(report):
    p = validate(report)
    origins = {row[0]: row[1:] for row in p['births']}
    totals = {name: Counter(dict.fromkeys(FIELDS, 0)) for name in ('all', 'early', 'late')}
    births = defaultdict(list)
    for _, batch, left, right, width in p['births']:
        births[batch].append((left, right, width))
    shapes = Counter()
    for batch in range(p['batches']):
        rows = births[batch]
        shapes[len({r[0] for r in rows}), len({r[1] for r in rows}), len(rows)] += 1
    widths = Counter(row[4] for row in p['births'])
    traffic_shapes = Counter()
    for _, conflict_bin, entries in p['lists']:
        counts = Counter(lists=1, visits=len(entries), hits=sum(hit for _, hit in entries))
        groups = defaultdict(list)
        for clause, hit in entries:
            if clause in origins:
                batch, left, right, _ = origins[clause]
                groups[batch].append((left, right))
                counts['product_visits'] += 1
                counts['product_hits'] += hit
        for rows in groups.values():
            left = len({r[0] for r in rows})
            right = len({r[1] for r in rows})
            counts['both_sides_screen'] += max(len(rows) - left - right, 0)
            counts['one_side_screen'] += len(rows) - min(left, right)
            traffic_shapes[left, right, len(rows)] += 1
        for name in ('all', 'late' if conflict_bin == 3 else 'early'):
            totals[name].update(counts)
    gates = {name: c['lists'] >= 1000 and c['visits'] > 0
             and 5 * c['product_visits'] >= c['visits']
             and 10 * c['both_sides_screen'] >= c['visits']
             for name, c in totals.items() if name != 'early'}
    return dict(totals=totals, gates=gates,
                insertion_shapes=[[*shape, n] for shape, n in sorted(shapes.items())],
                traffic_shapes=[[*shape, n] for shape, n in sorted(traffic_shapes.items())],
                insertion_widths=sorted(widths.items()),
                interpretation='Birth coverage and optimistic within-list counts only; '
                'no cofactor state, completeness, maintenance, explanation or cycle claim.')


def audit(report):
    """Independent sorted merge join and run-length grouping (no analyze call)."""
    births = sorted(report['products']['births'])
    visits = sorted((clause, index, hit) for index, (_, _, entries) in
                    enumerate(report['products']['lists']) for clause, hit in entries)
    joined = []
    birth_index = 0
    for clause, index, hit in visits:
        while birth_index < len(births) and births[birth_index][0] < clause:
            birth_index += 1
        if birth_index < len(births) and births[birth_index][0] == clause:
            _, batch, left, right, _ = births[birth_index]
            joined.append((index, batch, left, right, hit))
    totals = {name: dict.fromkeys(FIELDS, 0) for name in ('all', 'early', 'late')}
    lists = report['products']['lists']
    for _, bin_id, entries in lists:
        for name in ('all', 'late' if bin_id == 3 else 'early'):
            totals[name]['lists'] += 1
            totals[name]['visits'] += len(entries)
            totals[name]['hits'] += sum(entry[1] for entry in entries)
    traffic = Counter()
    for (index, _), group in groupby(sorted(joined), key=lambda row: row[:2]):
        rows = list(group)
        # Distinct counts use sorted runs, independently of the set-based path.
        left = sum(1 for _ in groupby(sorted(row[2] for row in rows)))
        right = sum(1 for _ in groupby(sorted(row[3] for row in rows)))
        traffic[left, right, len(rows)] += 1
        for name in ('all', 'late' if lists[index][1] == 3 else 'early'):
            c = totals[name]
            c['product_visits'] += len(rows)
            c['product_hits'] += sum(row[4] for row in rows)
            c['both_sides_screen'] += max(0, len(rows) - (left + right))
            c['one_side_screen'] += max(len(rows) - left, len(rows) - right)
    shapes = Counter()
    nonempty = 0
    for _, group in groupby(sorted(births, key=lambda row: row[1]), key=lambda row: row[1]):
        rows = list(group)
        left = sum(1 for _ in groupby(sorted(row[2] for row in rows)))
        right = sum(1 for _ in groupby(sorted(row[3] for row in rows)))
        shapes[left, right, len(rows)] += 1
        nonempty += 1
    empty = report['products']['batches'] - nonempty
    if empty:
        shapes[0, 0, 0] = empty
    widths = [[width, sum(1 for _ in rows)] for width, rows in
              groupby(sorted(row[4] for row in births))]
    return dict(totals=totals, insertion_shapes=[[*s, n] for s, n in sorted(shapes.items())],
                traffic_shapes=[[*s, n] for s, n in sorted(traffic.items())],
                insertion_widths=widths)


def check_prior_trace(report, path):
    """Compare every visited ID, hit and epoch with the retained independent trace."""
    from itertools import zip_longest
    with path.open() as stream:
        header = json.loads(next(stream))
        assert header['schema'] == 'nixie-residual-trace/1'
        assert header['stride'] == report['stride']
        count = 0
        for current, line in zip_longest(report['products']['lists'], stream):
            assert current is not None and line is not None, 'trace length differs'
            old = json.loads(line)
            assert not old['overflow']
            conflicts = old['conflicts']
            bin_id = 0 if conflicts == 0 else 1 if conflicts < 1024 else 2 if conflicts < 16384 else 3
            assert current == [old['ordinal'], bin_id,
                               [[entry['id'], int(entry['hit'])] for entry in old['entries']]]
            count += 1
    return count


def read_report(path):
    reports = [json.loads(line) for line in path.read_text().splitlines()
               if line.startswith('{"schema":"nixie-watch-groups/1"')]
    assert len(reports) == 1, 'expected exactly one completed report'
    return reports[0]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('stderr', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--prior-trace', type=Path)
    args = parser.parse_args()
    report = read_report(args.stderr)
    result = analyze(report)
    independent = audit(report)
    for key, expected in independent.items():
        assert json.loads(json.dumps(result[key])) == expected, ('audit mismatch', key)
    result['independent_audit'] = True
    if args.prior_trace:
        result['identical_prior_lists'] = check_prior_trace(report, args.prior_trace)
    with args.output.open('x') as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
    print(json.dumps(dict(totals=result['totals'], gates=result['gates']), indent=2))


if __name__ == '__main__':
    main()
