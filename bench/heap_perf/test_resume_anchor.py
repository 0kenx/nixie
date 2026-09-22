"""Recovery must retain missing data and never rerun or invent measurements."""
import json
from pathlib import Path
import tempfile
import unittest
import subprocess
import sys

import resume_anchor


class RecoveryTests(unittest.TestCase):
    def test_disabled_validation_is_rejected(self):
        result = subprocess.run([sys.executable, '-O', resume_anchor.__file__, '--help'],
                                capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('requires Python assertions', result.stderr)

    def fixture(self, root):
        log = root/'attempt.log'
        log.write_text('count = perf_count(...)\nin perf_count\nAssertionError\n')
        prefix = root/'cell'
        (root/'cell.command.json').write_text(json.dumps(dict(command=['frozen', 'command'])))
        for ext in ('.perf', '.stdout', '.stderr'):
            Path(str(prefix)+ext).write_text('')
        return log, prefix

    def test_only_unknown_with_missing_metrics_is_recovered(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            log, prefix = self.fixture(root)
            resume_anchor.recover(root, log)
            result = json.loads(Path(str(prefix)+'.result.json').read_text())
            self.assertEqual(result['payload']['answer'], 'unknown')
            self.assertFalse(result['payload']['verified'])
            self.assertTrue(result['payload']['region_unmeasured'])
            self.assertIsNone(result['wall_clock_s'])
            self.assertEqual(result['command'], ['frozen', 'command'])
            with self.assertRaises(AssertionError):
                resume_anchor.recover(root, log)

    def test_present_output_is_not_reinterpreted(self):
        for ext in ('.perf', '.stdout', '.stderr'):
            with tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                log, prefix = self.fixture(root)
                Path(str(prefix)+ext).write_text('unexpected evidence')
                with self.assertRaises(AssertionError):
                    resume_anchor.recover(root, log)
                self.assertFalse(Path(str(prefix)+'.result.json').exists())

    def test_ambiguous_or_different_failure_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            log, _ = self.fixture(root)
            (root/'second.command.json').write_text('{}')
            with self.assertRaises(AssertionError):
                resume_anchor.recover(root, log)
            (root/'second.command.json').unlink()
            log.write_text('different failure\n')
            with self.assertRaises(AssertionError):
                resume_anchor.recover(root, log)


if __name__ == '__main__':
    unittest.main()
