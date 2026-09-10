import copy
import json
import unittest

from elimination_product_analyze import analyze, audit


def report():
    # Three-by-three complete product, then an unrelated visit and a duplicate.
    births = [[10 + 3 * left + right, 0, left, right + 3, 4]
              for left in range(3) for right in range(3)]
    entries = [[row[0], row[0] % 2] for row in births] + [[100, 1], [10, 0]]
    return dict(schema='nixie-watch-groups/1', stride=4096, samples=2, lists_seen=4097,
                skipped_lists=0, skipped_entries=0, visited=12, hits=5,
                by_conflicts=[[11, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
                products=dict(schema='nixie-elimination-products/1', batches=2,
                              omitted_batches=0, omitted_outputs=0, omitted_lists=0,
                              omitted_entries=0, trace_entries=12, origin_slot_limit=1000,
                              batch_limit=100, trace_entry_limit=100, trace_list_limit=10,
                              births=births, lists=[[0, 0, entries], [4096, 3, [[10, 0]]]]))


class EliminationProductTests(unittest.TestCase):
    def test_join_counts_multiplicity_and_keeps_unrelated_denominator(self):
        r = report()
        result = analyze(r)
        all_counts = result['totals']['all']
        self.assertEqual(all_counts['product_visits'], 11)
        self.assertEqual(all_counts['visits'], 12)
        self.assertEqual(all_counts['both_sides_screen'], 4)
        self.assertEqual(all_counts['one_side_screen'], 7)
        self.assertEqual(result['totals']['late']['both_sides_screen'], 0)
        self.assertEqual(result['insertion_shapes'], [[0, 0, 0, 1], [3, 3, 9, 1]])
        self.assertFalse(any(result['gates'].values()))
        for key, expected in audit(r).items():
            self.assertEqual(json.loads(json.dumps(result[key])), expected)

    def test_omissions_missing_lists_stale_ids_and_bad_counts_fail_closed(self):
        changes = [lambda r: r['products'].update(omitted_outputs=1),
                   lambda r: r['products']['lists'][1].__setitem__(0, 8192),
                   lambda r: r['products']['births'].append(r['products']['births'][0]),
                   lambda r: r.update(visited=13),
                   lambda r: r['products']['lists'][0][2][0].__setitem__(1, 2),
                   lambda r: r['products']['births'][0].__setitem__(2, 10)]
        for change in changes:
            with self.subTest(change=change):
                r = copy.deepcopy(report())
                change(r)
                with self.assertRaises(AssertionError):
                    analyze(r)

    def test_no_births_is_valid_but_no_candidate_pass(self):
        r = report()
        r['products']['births'] = []
        result = analyze(r)
        self.assertEqual(result['totals']['all']['product_visits'], 0)
        self.assertEqual(result['insertion_shapes'], [[0, 0, 0, 2]])
        for key, expected in audit(r).items():
            self.assertEqual(json.loads(json.dumps(result[key])), expected)

    def test_gate_requires_coverage_consumer_count_and_late_samples(self):
        r = report()
        entries = r['products']['lists'][0][2]
        r['products']['lists'] = [[i * 4096, 3, entries] for i in range(1000)]
        r['products'].update(trace_list_limit=1000, trace_entry_limit=100000)
        r.update(samples=1000, lists_seen=999 * 4096 + 1)

        def recount():
            r['visited'] = r['products']['trace_entries'] = 1000 * len(entries)
            r['hits'] = 1000 * sum(hit for _, hit in entries)
            r['by_conflicts'] = [[0, 0, 0, 0]] * 3 + [[r['visited'], 0, 0, 0]]

        recount()
        self.assertEqual(analyze(r)['gates'], dict(all=True, late=True))
        entries.extend([[100, 0]] * 39)  # 20% coverage, only 8% consumer screen.
        recount()
        self.assertEqual(analyze(r)['gates'], dict(all=False, late=False))
        entries[:] = entries[:11]
        recount()
        for row in r['products']['lists']:
            row[1] = 2
        r['by_conflicts'][2], r['by_conflicts'][3] = r['by_conflicts'][3], [0, 0, 0, 0]
        self.assertEqual(analyze(r)['gates'], dict(all=True, late=False))


if __name__ == '__main__':
    unittest.main()
