import unittest

from residual_family_analyze import analyze_list, summarize


def entry(prefix, terminal=(100, 0), kind=3):
    tail = [[literal, -1] for literal in prefix]
    if terminal:
        tail.append(list(terminal))
    return dict(id=1, hit=False, kind=kind, width=len(tail) + 2,
                other=[200, 0], tail=tail)


def record(entries, ordinal=0, conflicts=0):
    return dict(entries=entries, ordinal=ordinal, conflicts=conflicts, trigger=202, overflow=False)


class ResidualFamilyAnalysisTests(unittest.TestCase):
    def test_shared_prefix_prices_one_lookup_per_beneficiary(self):
        counts, _, _ = analyze_list(record([entry([2, 4, 6, 8, 10]), entry([2, 4, 6, 8, 12])]))
        self.assertEqual(counts['ordered_saved_checks'], 4)
        self.assertEqual(counts['ordered_net_checks'], 3)
        self.assertEqual(counts['work'], 16)
        self.assertEqual(counts['ordered_inserted_edges'], 6)

    def test_sorting_is_separate_and_short_prefix_has_no_credit(self):
        counts, _, _ = analyze_list(record([entry([2, 4, 6, 8]), entry([8, 6, 4, 2]), entry([2, 4, 6])]))
        self.assertEqual(counts['ordered_net_checks'], 0)
        self.assertEqual(counts['sorted_net_checks'], 3)
        self.assertEqual(counts['repeated_false_literal_upper_bound'], 7)

    def test_hits_payloads_and_nonfalse_terminal_stay_in_denominator(self):
        hit = dict(id=2, hit=True, kind=3, width=20, other=[-1, 0], tail=[])
        dead = dict(id=3, hit=False, kind=1, width=0, other=[-1, 0], tail=[])
        counts, strata, hist = analyze_list(record([hit, dead, entry([], terminal=(100, 1), kind=2)]))
        self.assertEqual(counts['work'], 6)
        self.assertEqual(counts['false_scans'], 0)
        self.assertEqual(hist[0], 1)
        self.assertEqual(strata['original']['terminal_true'], 1)

    def test_no_sharing_across_lists_and_late_bin_is_separate(self):
        a = record([entry([2, 4, 6, 8])])
        b = record([entry([2, 4, 6, 8])], ordinal=4096, conflicts=16384)
        result = summarize([a, b], 4096)
        self.assertEqual(result['totals']['all']['ordered_net_checks'], 0)
        self.assertEqual(result['totals']['late']['lists'], 1)
        self.assertFalse(result['gates']['ordered'])

    def test_forward_assignments_are_allowed_but_unassigning_is_rejected(self):
        analyze_list(record([entry([], terminal=(2, 0)), entry([2], terminal=None)]))
        with self.assertRaises(AssertionError):
            analyze_list(record([entry([2]), entry([], terminal=(2, 0))]))

    def test_missing_samples_and_capacity_overflow_are_rejected(self):
        with self.assertRaises(AssertionError):
            summarize([record([], ordinal=4096)], 4096)
        r = record([])
        r['overflow'] = True
        with self.assertRaises(AssertionError):
            analyze_list(r)


if __name__ == '__main__':
    unittest.main()
