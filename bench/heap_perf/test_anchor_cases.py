"""Validate the new oracle schemas independently of any solver verdict."""
import unittest
import tempfile
import json
from pathlib import Path
import analyze_anchor
import anchor_cases
import run


class AnchorCasesTests(unittest.TestCase):
    def test_schema_and_witness(self):
        for family in anchor_cases.NEW_FAMILIES:
            for n in (3, 8, 16, 32, 64):
                text = anchor_cases.generate(family, n)
                self.assertEqual(anchor_cases.oracle(family, n, text),
                                 'unsat' if family == 'view_conflict' else 'sat')
                with self.assertRaises(AssertionError):
                    anchor_cases.oracle(family, n, text + 'assert 0 0\n')

    def test_contradiction_has_no_shared_heap_at_pinned_addresses(self):
        case = run.parse_case(anchor_cases.generate('view_conflict', 3))
        values = {f'x{i}': i % 4 + 1 for i in range(12)}
        # Each asserted heap uniquely fixes the whole concrete map. The first
        # and last differ, so neither candidate can satisfy every assertion.
        for heaplet in (case['heaps'][0], case['heaps'][-1]):
            with self.assertRaises(AssertionError):
                run.validate(case, values, run.concrete(heaplet, values))

    def test_legacy_oracles_unchanged(self):
        for family in run.FAMILIES:
            for n in (2, 4, 8, 16):
                text = anchor_cases.generate(family, n)
                self.assertEqual(text, run.generate(family, n))
                self.assertEqual(anchor_cases.oracle(family, n, text), run.oracle(family, n, text))

    def test_report_requires_paired_comparison_diagnostics(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            suite = analyze_anchor.experiment.SUITE
            records = root / 'runs' / suite
            records.mkdir(parents=True)
            (root / suite).mkdir()
            record = dict(instance=dict(name='views-8'), config=dict(id='reduced-total'),
                          seed=0, record_id='fixture', metrics=dict(primary=dict(value=123)),
                          verdict=dict(answer='sat', verified_model_or_proof=True))
            raw = root / suite / 'views-8-reduced-total-0-fixture.result.json'
            payload = dict(instructions=123, payload=dict(answer='sat', verified=True,
                           stdout='sat\ndefinitions 8 123\ncomparisons 7\n'))
            raw.write_text(json.dumps(payload))
            self.assertEqual(analyze_anchor.driver_counters(record, records), (8, 123, 7))
            payload['payload']['stdout'] = 'sat\ndefinitions 8 123\n'
            raw.write_text(json.dumps(payload))
            with self.assertRaises(AssertionError):
                analyze_anchor.driver_counters(record, records)


if __name__ == '__main__':
    unittest.main()
