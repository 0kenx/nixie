"""Retained benchmark records omit process output; raw diagnostics stay paired."""
import json
from pathlib import Path
import tempfile
import unittest

import analyze_optimization as report
import compare_optimization as experiment


class RawDiagnosticTests(unittest.TestCase):
    def test_diagnostics_come_from_paired_raw_result(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            directory = root / 'runs' / experiment.SUITE
            directory.mkdir(parents=True)
            raw = root / experiment.SUITE
            raw.mkdir()
            record = dict(instance=dict(name='negative-4'), config=dict(id='specialized-total'),
                          seed=0, record_id='fixture', metrics=dict(primary=dict(value=123)),
                          verdict=dict(answer='sat', verified_model_or_proof=True))
            path = raw / 'negative-4-specialized-total-0-fixture.result.json'
            result = dict(instructions=123, payload=dict(answer='sat', verified=True,
                          stdout='sat\ndefinitions 0 29\n'))
            path.write_text(json.dumps(result))
            self.assertEqual(report.driver_counters(record, directory), (0, 29))
            # A different observation's output must never be silently joined.
            result['instructions'] = 124
            path.write_text(json.dumps(result))
            with self.assertRaises(AssertionError):
                report.driver_counters(record, directory)

    def test_candidate_missing_diagnostics_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            directory = root / 'runs' / experiment.SUITE
            directory.mkdir(parents=True)
            raw = root / experiment.SUITE
            raw.mkdir()
            record = dict(instance=dict(name='negative-4'), config=dict(id='identity-total'),
                          seed=0, record_id='fixture', metrics=dict(primary=dict(value=123)),
                          verdict=dict(answer='sat', verified_model_or_proof=True))
            path = raw / 'negative-4-identity-total-0-fixture.result.json'
            path.write_text(json.dumps(dict(instructions=123,
                payload=dict(answer='sat', verified=True, stdout='sat\n'))))
            with self.assertRaises(AssertionError):
                report.driver_counters(record, directory)


if __name__ == '__main__':
    unittest.main()
