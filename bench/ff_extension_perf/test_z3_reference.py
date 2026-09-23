#!/usr/bin/env python3
"""Reference-harness regressions; synthetic counters stay in temporary fixtures."""
import contextlib
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import z3_reference as reference


class ReferenceHarnessTests(unittest.TestCase):
    def test_identical_translations_are_measured_once_per_invocation(self):
        cases = [c for c in reference.workload.CASES
                 if c['name'] in ['shared-f256', 'certified-f256']]
        self.assertEqual(reference.problem(cases[0], 0)[0], reference.problem(cases[1], 0)[0])
        result = subprocess.CompletedProcess([], 0, b'sat\n((x #xc3))\n', b'123,,instructions:u,100,100.00,\n')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            binary = root / 'fixture-binary'
            binary.write_bytes(b'not an executable: subprocess is mocked')
            args = ['z3_reference.py', str(binary), '--root', str(root), '--seeds', '1']
            with (patch.object(reference.workload, 'CASES', cases),
                  patch('sys.argv', args),
                  patch.object(reference.subprocess, 'check_output', return_value=reference.VERSION),
                  patch.object(reference.subprocess, 'run', return_value=result) as run,
                  contextlib.redirect_stdout(io.StringIO())):
                reference.main()
            self.assertEqual(run.call_count, 1)
            records = list(root.glob('*/benchmark/runs/ff-extension-z3/*.json'))
            self.assertEqual(len(records), 1)
            self.assertEqual(json.loads(records[0].read_text())['instance']['name'], 'shared-f256')

    def test_model_checker_rejects_wrong_value_and_width(self):
        case = next(c for c in reference.workload.CASES if c['name'] == 'square-f256')
        _, expected, _ = reference.problem(case, 0)
        reference.verify('sat\n((x #xc3))\n', expected)
        for output in ['sat\n((x #x00))\n', 'sat\n((x #x00c3))\n', 'unknown\n']:
            with self.assertRaises((AssertionError, ValueError)):
                reference.verify(output, expected)


if __name__ == '__main__':
    unittest.main()
