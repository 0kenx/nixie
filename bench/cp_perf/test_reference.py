"""Focused checks for the external reference translation and model verifier."""
import argparse
import subprocess
import unittest

from reference import FAMILIES, expressions, parse_shape, problem, verify_z3


class ReferenceTests(unittest.TestCase):
    def test_generated_instances_have_checked_z3_models(self):
        for family in FAMILIES:
            for count, width in [(4, 4), (8, 16)]:
                with self.subTest(family=family, shape=(count, width)):
                    result = subprocess.run(['z3', '-in'], input=problem(family, count, width, 3),
                                            text=True, capture_output=True, check=True, timeout=30)
                    verify_z3(result.stdout, family, count, width)

    def test_larger_shapes_have_independently_checked_models(self):
        for family in ['unknown', 'present', 'sparse']:
            for count, width in [(8, 32), (16, 16), (16, 32), (32, 16)]:
                with self.subTest(family=family, shape=(count, width)):
                    result = subprocess.run(['z3', '-in'], input=problem(family, count, width, 10),
                                            text=True, capture_output=True, check=True, timeout=30)
                    verify_z3(result.stdout, family, count, width)

    def test_shape_rejects_empty_or_nonpositive_dimensions(self):
        self.assertEqual(parse_shape('16x32'), (16, 32))
        for invalid in ['0x16', '16x0', '-1x8', '8', '8x16x32', 'axb']:
            with self.subTest(shape=invalid):
                with self.assertRaises(argparse.ArgumentTypeError):
                    parse_shape(invalid)

    def test_checker_rejects_invalid_models_and_incomplete_verdicts(self):
        output = 'sat ((p0 false) (s0 0)) sat ((p0 false) (s0 0))'
        verify_z3(output, 'blocked', 1, 2)
        for invalid in [output.replace('false', 'true'), output.replace('(s0 0)', '(s0 2)'),
                        output.replace('sat', 'unknown'), output.replace(' (s0 0)', ''),
                        output.replace('(s0 0)', '(s0 true)'), output.replace('p0 false', 'p0 false) (p0 false')]:
            with self.subTest(output=invalid):
                with self.assertRaises(ValueError):
                    verify_z3(invalid, 'blocked', 1, 2)

    def test_wide_values_are_checked_exactly(self):
        # The validator's positive-capacity families use cap=count; two tasks
        # may coincide, while a start outside the exact wide domain must fail.
        big = 1 << 140
        model = f'((p0 true) (p1 true) (s0 {big}) (s1 {big + 1}))'
        verify_z3(f'sat {model} sat {model}', 'wide', 2, 2)
        with self.assertRaises(ValueError):
            verify_z3(f'sat {model} sat {model}'.replace(str(big + 1), str(big + 2)), 'wide', 2, 2)
        self.assertEqual(expressions('((- 1))'), [[['-', '1']]])


if __name__ == '__main__':
    unittest.main()
