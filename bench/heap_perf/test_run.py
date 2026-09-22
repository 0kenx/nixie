"""Independent semantic and measurement checks; no solver installation needed."""
import itertools
import json
from pathlib import Path
import tempfile
import unittest
import run


class HeapBenchTests(unittest.TestCase):
    def test_small_exhaustive_truth(self):
        # All valuations and heaps on two nonzero locations with two values.
        # Compare finite-map semantics with the explicit domain/data encoding.
        heaps = [{}]
        for values in itertools.product((None, 0, 1), repeat=2):
            heaps.append({i+1:v for i,v in enumerate(values) if v is not None})
        for locations in itertools.product((0, 1, 2), repeat=2):
            values = dict(zip(("x0", "x1"), locations))
            for cells in ([], [(0,0)], [(0,0),(1,1)], [(0,0),(0,0)]):
                for heap in heaps:
                    explicit = (all(locations[l] != 0 for l,_ in cells)
                        and len({locations[l] for l,_ in cells}) == len(cells)
                        and set(heap) == {locations[l] for l,_ in cells}
                        and all(heap.get(locations[l]) == v for l,v in cells))
                    self.assertEqual(explicit, run.concrete(cells,values) == heap)

    def test_authenticated_oracle(self):
        for family in run.FAMILIES:
            for size in (2,4,8,16):
                text = run.generate(family,size)
                self.assertEqual(run.oracle(family,size,text),
                                 "sat" if family in ("allocate","negative") else "unsat")
                with self.assertRaises(AssertionError):
                    run.oracle(family,size,text+"assert 0 0\n")

    def test_native_model_and_rejected_overlap(self):
        case = run.parse_case(run.generate("allocate",2))
        model = 'sat\n((x0 1) (x1 2))\n()\n(heap (sep (pto 1 0) (pto 2 1)) (= nil 0))'
        self.assertEqual(run.reference_model(case,model,True),{1:0,2:1})
        with self.assertRaises(AssertionError):
            run.reference_model(case,model.replace('(pto 2 1)','(pto 1 1)'),True)
        with self.assertRaises(AssertionError):
            run.reference_model(case,model.replace('(pto 2 1)','(pto 2 0)'),True)

    def test_negative_array_finite_completion(self):
        case = run.parse_case(run.generate("negative",2))
        model = 'sat\n(' + ' '.join(f'(x{i} 0)' for i in range(8)) + ' (h0 false) (h1 false))'
        self.assertEqual(len(run.reference_model(case,model,False)),5)
        with self.assertRaises(AssertionError):
            run.reference_model(case,model.replace('h0 false','h0 true'),False)

    def test_counter_rejects_multiplexing_and_missing(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'counter'
            text = '<not counted>,,cpu_atom/instructions/u,0,0.00,,\n1234,,cpu_core/instructions/u,1,100.00,,\n'
            path.write_text(text)
            self.assertEqual(run.perf_count(path),1234)
            path.write_text(text.replace('100.00','90.00'))
            with self.assertRaises(AssertionError): run.perf_count(path)
            path.write_text('')
            with self.assertRaises(AssertionError): run.perf_count(path)
            path.write_text('<not counted>,,cpu_core/instructions/u,0,0.00,,\n')
            self.assertIsNone(run.perf_count(path,unreached_region=True))
            with self.assertRaises(AssertionError): run.perf_count(path)

    def test_inconclusive_cost_is_not_a_speedup(self):
        records = [dict(instance=dict(name="case"), config=dict(id="arm"),
                        verdict=dict(answer=answer), metrics=dict(
                            primary=dict(value=cost), secondary=dict(solver_peak_rss_kib=5)))
                   for answer,cost in (("sat",100),("unknown",1),("sat",200))]
        with tempfile.TemporaryDirectory() as directory:
            run.summarize(records,Path(directory))
            row = json.loads((Path(directory)/"summary.json").read_text())[0]
            self.assertEqual(row["solved"],2)
            self.assertEqual(row["instructions_median"],150)
            self.assertEqual(row["instructions_min"],100)

    def test_deep_parser_and_malformed_input(self):
        tree = run.sexprs('('*10000 + 'x' + ')'*10000)
        for _ in range(10000): tree = tree[0]
        self.assertEqual(tree,['x'])
        with self.assertRaises(AssertionError): run.sexprs('(x')
        with self.assertRaises(ValueError): run.sexprs('x)')
        for text in ('vars 1\nassert 2 0\n','vars 1\nheap 1 2 0\n',
                     'vars 1\nbound 1 0 1\n','vars 1\neq 0 2\n'):
            with self.assertRaises(AssertionError): run.parse_case(text)


if __name__ == '__main__': unittest.main()
