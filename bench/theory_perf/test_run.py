import unittest
import run


class Validation(unittest.TestCase):
    def test_rejects_unknown_errors_missing_and_false_witnesses(self):
        good = 'sat\n(((= y0 a) true))\nunsat\nsat\n(((= y0 a) true))'
        run.verify(good, True, 'fp16-32', 1)
        for bad in [good.replace('unsat', 'unknown'), good.replace('true', 'false', 1),
                    good + '\n(error broken)', good.replace('(((= y0 a) true))', '()')]:
            with self.assertRaises(ValueError):
                run.verify(bad, True, 'fp16-32', 1)

    def test_exact_rational_distinctness(self):
        good = 'sat ((x0 (- (/ 1.0 3.0))) (x1 0.0)) unsat sat ((x0 1.0) (x1 2.0))'
        run.verify(good, True, 'arrangements', 2)
        with self.assertRaises(ValueError):
            run.verify(good.replace('(x1 0.0)', '(x1 (/ (- 1.0) 3.0))'), True, 'arrangements', 2)

    def test_missing_or_multiplexed_counters_rejected(self):
        self.assertEqual(run.instructions('100,,cpu_core/instructions/u,42,100.00,,'), 100)
        for text in ['', '<not counted>,,instructions:u,0,0.00,,', '100,,instructions:u,42,98.00,,']:
            with self.assertRaises(ValueError):
                run.instructions(text)


if __name__ == '__main__':
    unittest.main()
