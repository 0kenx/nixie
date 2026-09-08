import unittest

from clause_traffic_probe import summarize


def row(cid, epoch, payloads, uses=0, status="learned"):
    return dict(id=cid, epoch=epoch, length=3, glue=4, tier=1, final_status=status,
                counts=[[0] * 7, [payloads, 0, payloads, 0, 0, 0, uses]])


def report(rows, elapsed=8192):
    return dict(schema="nixie-clause-traffic/1", epoch_conflicts=4096,
                elapsed_conflicts=elapsed, overflow=False, omitted=[[0] * 7, [0] * 7], rows=rows)


class CensusAnalysisTests(unittest.TestCase):
    def test_rank_uses_only_previous_epoch_and_ignores_partial_final_epoch(self):
        rows = [row(1, 0, 100), row(2, 0, 1), row(3, 0, 1), row(4, 0, 1),
                row(1, 1, 10), row(2, 1, 90), row(1, 2, 10000)]
        result = summarize(report(rows, elapsed=8193))
        self.assertEqual(len(result["pairs"]), 1)
        pair = result["pairs"][0]
        self.assertEqual(pair["top_future_fraction"], .1)
        self.assertEqual(pair["top_future_zero_direct_use_fraction"], .1)

    def test_missing_future_rows_are_censored_and_do_not_become_unused_work(self):
        rows = [row(1, 0, 100, status="deleted"), row(2, 0, 1), row(3, 0, 1), row(4, 0, 1),
                row(2, 1, 100)]
        pair = summarize(report(rows))["pairs"][0]
        self.assertEqual(pair["missing_future_rows"], 1)
        self.assertEqual(pair["missing_future_deleted_at_end"], 1)
        self.assertEqual(pair["top_future_zero_direct_use_work"], 0)

    def test_future_resolution_without_bcp_is_still_a_direct_use(self):
        rows = [row(1, 0, 100), row(2, 0, 1), row(3, 0, 1), row(4, 0, 1),
                row(1, 1, 50, uses=1), row(2, 1, 10)]
        result = summarize(report(rows))
        self.assertGreater(result["pairs"][0]["top_future_fraction"], .8)
        self.assertEqual(result["pairs"][0]["top_future_zero_direct_use_fraction"], 0)
        self.assertFalse(result["advance"])

    def test_incomplete_or_duplicate_observations_are_rejected(self):
        r = report([row(1, 0, 1)])
        r["overflow"] = True
        with self.assertRaises(AssertionError):
            summarize(r)
        r["overflow"] = False
        r["omitted"][0][0] = 1
        with self.assertRaises(AssertionError):
            summarize(r)
        with self.assertRaises(AssertionError):
            summarize(report([row(1, 0, 1), row(1, 0, 2)]))


if __name__ == "__main__":
    unittest.main()
