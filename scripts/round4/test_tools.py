"""Focused checks for the migrated finite oracle and comparison boundaries."""
import pathlib
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import common as c
import zjudge


class OracleTests(unittest.TestCase):
    def test_finite_verdicts_and_signed_values(self):
        sat = c.Script('(declare-const x (_ BitVec 2)) (assert (bvslt x #b00))')
        self.assertEqual(sat.brute_force()[0], 'sat')
        self.assertTrue(sat.eval_model({'x': 3}))
        unsat = c.Script('(assert (forall ((x (_ BitVec 2))) (bvult x #b11)))')
        self.assertEqual(unsat.brute_force()[0], 'unsat')
        wide = ['bvneg', ['_', 'bv1', '129']]
        self.assertEqual(c.const_value(wide, ('BV', 129)), (1 << 129) - 1)

    def test_array_store_and_shadowed_binders(self):
        script = c.Script('''(declare-const a (Array Bool (_ BitVec 1)))
            (assert (= (select (store a true #b1) true) #b1))
            (assert (forall ((x Bool)) (exists ((x Bool)) x)))''')
        self.assertEqual(script.brute_force()[0], 'sat')
        self.assertTrue(script.eval_model({'a': (0, 0)}))

    def test_model_values_are_sort_checked(self):
        self.assertIsNone(c.const_value('#b1', c.BOOL))
        self.assertIsNone(c.const_value('true', ('BV', 1)))
        self.assertEqual(c.const_value('#b1', ('BV', 1)), 1)

    def test_incremental_and_unsupported_sorts_are_not_static_proofs(self):
        for text in ['(push 1) (assert false) (pop 1) (check-sat)',
                     '(declare-const x Int) (assert true)']:
            script = c.Script(text)
            self.assertEqual(script.brute_force()[0], 'unsupported')
            self.assertIsNone(script.eval_model({}))
        with self.assertRaises(ValueError):
            c.parse_sort(['_', 'BitVec', '0'])

    def test_deep_external_input_declines_before_recursive_compilation(self):
        with self.assertRaisesRegex(ValueError, "nesting budget"):
            c.parse_all("(" * 2000 + "true" + ")" * 2000)
        self.assertEqual(c.show(c.parse_all("(and true (not false))")[0]),
                         "(and true (not false))")

    def test_large_domains_decline_before_materializing(self):
        with self.assertRaises(c.TooBig):
            c.domain(('Array', ('BV', 16), ('BV', 1)))
        script = c.Script('(declare-const x (_ BitVec 129))')
        self.assertEqual(script.brute_force()[0], 'too-big')

    def test_parallelism_is_bounded_and_ordered(self):
        self.assertEqual(c.pool_map(lambda x: x * x, [2, 1, 3], 2), [4, 1, 9])
        with self.assertRaises(ValueError):
            c.pool_map(lambda x: x, [], 3)

    def test_unknown_comparator_is_inconclusive(self):
        with patch.object(zjudge, 'z3_run', return_value='unknown'), \
             patch.object(zjudge, 'z3_version', return_value='test comparator'):
            report = zjudge.judge('(assert true) (check-sat)', 'sat', 1)
        self.assertEqual(report['wrong_sat'], 0)
        self.assertEqual(report['wrong_unsat'], 0)
        self.assertEqual(report['z3_unknown'], 1)
        self.assertEqual(report['z3_version'], 'test comparator')

    def test_partial_model_is_not_a_validated_complete_model(self):
        script = '(declare-fun f (Int) Int) (assert (= (f 0) 1)) (check-sat) (get-model)'
        with patch.object(zjudge, 'z3_run', return_value='sat'), \
             patch.object(zjudge, 'z3_version', return_value='test comparator'):
            report = zjudge.judge(script, 'sat (model)', 1)
        self.assertEqual(report['model_ok'], 0)
        self.assertEqual(report['model_partial_consistent'], 1)
        self.assertEqual(report['events'][0][0], 'PARTIAL_MODEL_CONSISTENT')

    def test_seeded_generator_reproduces_the_same_corpus(self):
        generator = pathlib.Path(__file__).with_name('gen_qmbqi.py')
        with tempfile.TemporaryDirectory(prefix='nixie-upstream034-generator-') as root:
            runs = []
            for name in ['a', 'b']:
                output = pathlib.Path(root) / name
                subprocess.run([sys.executable, str(generator), '--seed', '19',
                                '--count', '4', '--widths', '1,2', '--out', str(output)],
                               check=True, capture_output=True, text=True)
                runs.append({p.name: p.read_bytes() for p in output.iterdir()})
            self.assertEqual(runs[0], runs[1])
            self.assertTrue(runs[0])


if __name__ == '__main__':
    unittest.main()
