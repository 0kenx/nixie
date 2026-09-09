#!/usr/bin/env python3
"""Offline opportunity bounds; none of these counters estimates solver cycles."""

import argparse
import collections
import json
from pathlib import Path


def shared_prefix(trie, prefix):
    node = trie
    shared = 0
    for literal in prefix:
        if literal not in node:
            break
        shared += 1
        node = node[literal]
    node = trie
    for literal in prefix:
        node = node.setdefault(literal, {})
    return shared


def analyze_list(record):
    assert not record['overflow'], 'incomplete trace sample'
    assert record['conflicts'] >= 0 and record['trigger'] >= 0
    counts = collections.Counter(lists=1)
    strata = collections.defaultdict(collections.Counter)
    hist = collections.Counter()
    ordered, sorted_trie, seen_false, values = {}, {}, set(), {}

    def observe(literal, value):
        assert literal >= 0 and value in (-1, 0, 1)
        if literal in values and values[literal]:
            assert values[literal] == value, 'assignment invalidated inside a list'
        if literal ^ 1 in values and values[literal ^ 1]:
            assert values[literal ^ 1] == -value, 'opposite assignment inside a list'
        values[literal] = value

    for entry in record['entries']:
        assert entry['kind'] in (1, 2, 3), 'missing live/deleted classification'
        row = collections.Counter(visits=1)
        row['hits'] = int(entry['hit'])
        row['payloads'] = int(not entry['hit'])
        tail = entry['tail']
        row['scans'] = len(tail)
        if entry['hit'] or entry['kind'] == 1:
            assert not tail
        else:
            assert entry['width'] >= 2
            assert len(tail) <= entry['width'] - 2
            other, value = entry['other']
            observe(other, value)
            if value > 0:
                assert not tail
                row['other_true'] = 1
            else:
                assert tail or entry['width'] == 2
                row['tail_entries'] = 1
                row['eligible_width'] = int(entry['width'] >= 6)
                assert all(v == -1 for _, v in tail[:-1])
                for literal, value in tail:
                    observe(literal, value)
                prefix = [literal for literal, value in tail if value == -1]
                row['false_scans'] = len(prefix)
                hist[len(prefix)] += 1
                if tail and tail[-1][1] >= 0:
                    row['terminal_true' if tail[-1][1] else 'terminal_undefined'] += 1
                else:
                    assert len(tail) == entry['width'] - 2
                    row['terminal_conflict' if entry['other'][1] < 0 else 'terminal_unit'] += 1
                row['candidate_lookups'] = int(len(prefix) >= 4)
                for label, trie, sequence in [('ordered', ordered, prefix),
                                               ('sorted', sorted_trie, sorted(prefix))]:
                    shared = shared_prefix(trie, sequence)
                    row[label + '_inserted_edges'] = len(sequence) - shared
                    if shared >= 4:
                        row[label + '_beneficiaries'] = 1
                        row[label + '_saved_checks'] = shared
                        row[label + '_net_checks'] = shared - 1
                for literal in prefix:
                    row['repeated_false_literal_upper_bound'] += int(literal in seen_false)
                    seen_false.add(literal)
        row['work'] = row['visits'] + row['payloads'] + row['scans']
        counts.update(row)
        strata[{1: 'dead', 2: 'original', 3: 'learned'}[entry['kind']]].update(row)
    return counts, strata, hist


def summarize(records, stride):
    totals = collections.defaultdict(collections.Counter)
    strata = collections.defaultdict(collections.Counter)
    histograms = collections.defaultdict(collections.Counter)
    for index, record in enumerate(records):
        assert record['ordinal'] == index * stride, 'missing/reordered sample'
        c, s, h = analyze_list(record)
        epoch = 'late' if record['conflicts'] >= 16384 else 'early'
        for label in ['all', epoch]:
            totals[label].update(c)
            histograms[label].update(h)
        for kind, values in s.items():
            strata[kind].update(values)
    for counts in [*totals.values(), *strata.values()]:
        for label in ['ordered', 'sorted']:
            counts[label + '_net_fraction'] = counts[label + '_net_checks'] / max(1, counts['work'])
            counts[label + '_net_after_all_candidate_lookups'] = counts[label + '_saved_checks'] - counts['candidate_lookups']
    gates = {}
    for label in ['ordered', 'sorted']:
        gates[label] = all(totals[epoch]['lists'] >= 1000 and
                           totals[epoch][label + '_net_fraction'] >= .2 for epoch in ['all', 'late'])
    return dict(totals=totals, strata=strata, false_prefix_lengths=histograms, gates=gates,
                interpretation='optimistic event savings; excludes index construction, invalidation, membership storage and hardware cost')


def read_trace(path):
    with path.open() as stream:
        header = json.loads(next(stream))
        assert header['schema'] == 'nixie-residual-trace/1'
        return summarize((json.loads(line) for line in stream), header['stride'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('trace', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    result = read_trace(args.trace)
    with args.output.open('x') as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
    print(json.dumps(dict(totals=result['totals'], gates=result['gates']), indent=2))


if __name__ == '__main__':
    main()
