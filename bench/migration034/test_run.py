import unittest
import run


class MeasurementTests(unittest.TestCase):
    def test_verdict_parser_never_infers_sat_from_unsat_or_statistics(self):
        self.assertEqual(run.parse_answer('s UNSATISFIABLE\nc satisfiable 3\n'), ['unsat'])
        self.assertEqual(run.parse_answer('(error "sat")\nunknown\n'), ['unknown'])
        self.assertEqual(run.parse_answer('sat\nunsat\n'), ['sat', 'unsat'])

    def test_hybrid_pmu_keeps_only_counted_event(self):
        text = '<not counted>;;cpu_atom/instructions/u;0;0.00;;\n12345;;cpu_core/instructions/u;2000;100.00;;\n'
        self.assertEqual(run.parse_instructions(text), 12345)

    def test_unavailable_or_multiplexed_counts_are_not_fabricated(self):
        for text in ['', '<not supported>;;instructions:u;0;0;;',
                     '500;;instructions:u;100;80.00;;',
                     '500;;instructions:u;100;100.00;;\n600;;instructions:u;100;100.00;;']:
            with self.assertRaises(ValueError):
                run.parse_instructions(text)

    def test_dimacs_keeps_native_sat_path(self):
        arm = {'engine': 'nixie', 'binary': 'nixie'}
        argv = run.command(arm, {'kind': 'SAT', 'path': 'sample.cnf'})
        self.assertIn('--dimacs', argv)
        self.assertNotIn('--dimacs-output', argv)
        self.assertNotIn('--timeout', argv)


if __name__ == '__main__':
    unittest.main()
