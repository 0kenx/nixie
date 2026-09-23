import unittest
import workload as w


class OracleTests(unittest.TestCase):
    def test_plants_and_tiny_unsat_are_independent(self):
        for case in w.CASES:
            for seed in range(20):
                _, expected = w.generate(case,seed)
                if 'legacy' not in expected and expected['answer']=='sat':
                    w.check_values(expected['plants'],expected)
        case=('tiny-inconsistent','inconsistent',7,1,True)
        _,expected=w.generate(case,0)
        for x in range(4):
            for y in range(4):
                with self.assertRaises(AssertionError):
                    w.check_values({'x':x,'y':y},expected)

    def test_reject_wrong_models_and_keep_unknown_unsolved(self):
        _,expected=w.generate(w.CASES[2],0)
        self.assertEqual(w.verify('unknown\n(error "No model available")\n',expected),('unknown',False))
        with self.assertRaises(AssertionError):
            w.verify('sat\n((x (as ff0 (_ BinaryField 283))) (y (as ff0 (_ BinaryField 283))))\n',expected)
        with self.assertRaises(AssertionError):
            w.verify('sat\n((x #b0) (y #b0))\n',expected,True)

    def test_certified_reference_is_identical_and_budget_requests_model(self):
        self.assertEqual(w.generate(w.CASES[3],0,True)[0],w.generate(w.CASES[4],0,True)[0])
        self.assertIn('(get-value (x y))',w.generate(w.CASES[1],0)[0])
