"""Adversarial checks for snapshot validation and once-only measurement recovery."""
import json
from pathlib import Path
import tempfile
import unittest

import analyze_next
import next_cases as cases
import next_worker as worker
import next_experiment as experiment


class NextTests(unittest.TestCase):
    def test_report_rejects_incomplete_matrix(self):
        with self.assertRaisesRegex(AssertionError, "missing or duplicate"):
            analyze_next.validate_records([], {})

    def test_authenticate_every_schema(self):
        self.assertEqual(len(cases.CASES), 27)
        for family, size in cases.CASES:
            text = cases.generate(family, size)
            self.assertEqual(len(cases.oracle(family, size, text)), len(cases.parse(text)['checks']))
            with self.assertRaises(AssertionError):
                cases.oracle(family, size, text+'assert 0 0\n')

    def test_scopes_check_original_constraints(self):
        text = cases.generate('cache_scopes', 3)
        case = cases.parse(text)
        heap = {i+1: i for i in range(32)}
        for i, answer in enumerate(cases.oracle('cache_scopes', 3, text)):
            if answer == 'sat':
                cases.validate(case, i, {'x0': 1}, heap)
                with self.assertRaises(AssertionError):
                    cases.validate(case, i, {'x0': 1}, {**heap, 1: 99})
            else:
                with self.assertRaises(AssertionError):
                    cases.validate(case, i, {'x0': 1}, heap)

    def test_disjoint_boolean_alternatives(self):
        case = cases.parse(cases.generate('boolean_unsat', 4))
        for x in range(1, 5):
            for value in range(5):
                with self.assertRaises(AssertionError):
                    cases.validate(case, 0, {'x0': x}, {x: value})

    def test_duplicate_locations_are_invalid_even_when_values_agree(self):
        self.assertIsNone(cases.concrete([(0, ('constant', 7)), (1, ('constant', 7))], [1, 1]))
        self.assertIsNone(cases.concrete([(0, ('constant', 7))], [0]))

    def test_driver_missing_duplicate_and_corrupt_snapshots(self):
        case = cases.parse(cases.generate('boolean_sat', 2))
        text = ('begin 0\nsat\nsizes 1 2 3\ndefinitions 0\ncomparisons 0\n'
                'search 0 1 2\noptimization 0 0 0 0\nvar x0 1\ncell 1 0\nend 0\n')
        self.assertEqual(worker.driver_result(case, ['sat'], text, 'all')[0], ['sat'])
        for corrupt in (text.replace('end 0', 'end 1'), text+text,
                        text.replace('cell 1 0', 'cell 1 99'),
                        text.replace('cell 1 0', 'cell 1 0\ncell 1 0'),
                        text.replace('optimization 0 0 0 0\n', ''),
                        text.replace('sat\n', 'unsat\n')):
            with self.assertRaises(AssertionError):
                worker.driver_result(case, ['sat'], corrupt, 'all')

    def test_reference_model_checked_against_original_snapshot(self):
        case = cases.parse(cases.generate('boolean_sat', 2))
        worker.reference_model(case, 0, 'sat\n((x0 1) (h0 true) (h1 false))', False)
        with self.assertRaises(AssertionError):
            worker.reference_model(case, 0, 'sat\n((x0 0) (h0 true) (h1 false))', False)
        with self.assertRaises(AssertionError):
            worker.reference_model(case, 0, 'sat\n((x0 1) (h0 true) (h1 true))', False)
        worker.reference_model(case, 0, 'sat\n((x0 1))\n(heap (pto 1 0))', True)
        with self.assertRaises(AssertionError):
            worker.reference_model(case, 0, 'sat\n((x0 1))\n(heap (pto 1 99))', True)

    def test_timeout_is_preserved_without_fabricating_measured_work(self):
        with tempfile.TemporaryDirectory() as directory:
            raw = Path(directory)/'cell'
            raw.with_suffix('.stderr').write_text('')
            raw.with_suffix('.perf').write_text('')
            raw.with_suffix('.stdout').write_text(json.dumps(dict(answer='sat', verified=True)))
            execution = dict(timeout=True, status=-9, elapsed=23.5, command=['frozen'], load_before=[1], load_after=[2])
            result = experiment.finish_execution(raw, execution)
            self.assertEqual(result['wall_clock_s'], 23.5)
            self.assertEqual(result['instructions'], 0)
            self.assertFalse(result['payload']['verified'])
            self.assertTrue(result['payload']['region_unmeasured'])
            execution.update(timeout=False, status=0)
            with self.assertRaises((AssertionError, ValueError)):
                experiment.finish_execution(raw, execution)
            execution['timeout'] = True
            raw.with_suffix('.stderr').write_text('AssertionError: WRONG ANSWER')
            with self.assertRaises(AssertionError):
                experiment.finish_execution(raw, execution)


if __name__ == '__main__':
    unittest.main()
