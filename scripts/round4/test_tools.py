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

    def test_selector_interpretation_is_not_fabricated_by_model_replay(self):
        script = '''(declare-datatype D ((empty) (full (value Bool))))
            (declare-const d D) (assert (value d)) (check-sat) (get-model)'''
        output = 'sat (model (define-fun d () D empty))'
        with patch.object(zjudge, 'z3_run', side_effect=['sat', 'sat']), \
             patch.object(zjudge, 'z3_version', return_value='test comparator'):
            report = zjudge.judge(script, output, 1, check_verdicts=False)
        self.assertEqual(report['falsifying'], 0)
        self.assertEqual(report['model_ok'], 0)
        self.assertEqual(report['model_partial_consistent'], 1)
        self.assertEqual(report['events'][0][0], 'PARTIAL_SELECTOR_INTERPRETATION')
        # A fixed, matching constructor cannot hide a genuinely false read.
        with patch.object(zjudge, 'z3_run', side_effect=['sat', 'unsat']), \
             patch.object(zjudge, 'z3_version', return_value='test comparator'):
            report = zjudge.judge(script, 'sat (model (define-fun d () D (full false)))',
                                 1, check_verdicts=False)
        self.assertEqual(report['falsifying'], 1)
        self.assertEqual(report['model_partial_consistent'], 0)

    def test_partial_selector_value_is_unresolved_and_false_value_still_fails(self):
        script = '''(declare-datatypes ((D 0)) (((empty) (full (value Bool)))))
            (declare-const d D) (assert true) (check-sat) (get-model)
            (get-value ((value d)))'''
        for pinned, expected in [('sat', 0), ('unsat', 1), ('unknown', 0)]:
            with patch.object(zjudge, 'z3_run', side_effect=['unsat', 'sat', pinned]), \
                 patch.object(zjudge, 'z3_version', return_value='test comparator'):
                report = zjudge.judge(script,
                    'sat (model (define-fun d () D empty)) (((value d) true))',
                    1, check_verdicts=False)
            self.assertEqual(report['gv_wrong'], expected)
            self.assertEqual(report['gv_unresolved'], 1 - expected)

    def test_replay_preserves_logic_specific_sort_names(self):
        script = '(set-logic UF)(declare-sort Set 0)(declare-const a Set)(assert (= a a))(check-sat)(get-model)'
        with patch.object(zjudge, 'z3_run', return_value='unsat') as run, \
             patch.object(zjudge, 'z3_version', return_value='test comparator'):
            report = zjudge.judge(script,
                'sat (model (define-fun a () Set @uc_Set_0))', 1, check_verdicts=False)
        self.assertTrue(run.call_args.args[0].startswith('(set-logic UF)\n'))
        self.assertNotIn('(set-logic ALL)', run.call_args.args[0])
        self.assertEqual(report['model_ok'], 1)

    def test_witness_renaming_preserves_user_symbols_strings_and_freshness(self):
        items = [(e[0], e) for e in c.parse_all(
            '(declare-sort U 0)(declare-const @uc_U_0 U)'
            '(declare-const uc__U__1 U)(declare-const s String)')]
        defs = zjudge.model_defs(c.parse_all('(model '
            '(define-fun @uc_U_0 () U @uc_U_1)'
            '(define-fun uc__U__1 () U @uc_U_2)'
            '(define-fun s () String "@uc_U_0"))')[0])
        text, missing, _ = zjudge.replay_text(items, defs, None,
            '(assert (and (distinct @uc_U_0 uc__U__1) (= s "@uc_U_0")))')
        self.assertFalse(missing)
        self.assertIn('(define-fun @uc_U_0 () U uc__U__1__1)', text)
        self.assertIn('(define-fun uc__U__1 () U uc__U__2)', text)
        self.assertIn('(define-fun s () String "@uc_U_0")', text)
        self.assertIn('(distinct @uc_U_0 uc__U__1)', text)
        self.assertNotIn('(declare-const uc__U__0 ', text)

    def test_goal_only_witnesses_are_declared_and_bound_names_are_preserved(self):
        items = [('declare-sort', ['declare-sort', 'U', '0'])]
        text, _, _ = zjudge.replay_text(items, {}, 'UF',
            '(assert (forall ((@uc_U_0 U)) (= @uc_U_0 @uc_U_4)))')
        self.assertIn('(declare-const uc__U__4 U)', text)
        self.assertIn('((@uc_U_0 U)) (= @uc_U_0 uc__U__4)', text)
        self.assertNotIn('(declare-const uc__U__0 ', text)

    def test_witness_spelling_does_not_capture_constructors_or_recursive_names(self):
        items = [(e[0], e) for e in c.parse_all(
            '(declare-datatype D ((@uc_D_0) (other)))'
            '(declare-const d D)'
            '(define-funs-rec ((@uc_D_1 () D)) ((@uc_D_0)))')]
        defs = {'d': ['define-fun', 'd', [], 'D', '@uc_D_0']}
        text, missing, witnesses = zjudge.replay_text(
            items, defs, None, '(assert (= d @uc_D_1))')
        self.assertFalse(missing)
        self.assertFalse(witnesses)
        self.assertIn('(define-fun d () D @uc_D_0)', text)
        self.assertIn('(assert (= d @uc_D_1))', text)


if __name__ == '__main__':
    unittest.main()
