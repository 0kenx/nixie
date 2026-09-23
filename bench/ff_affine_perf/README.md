# Binary affine hard cases versus Z3

Protocol, references, acceptance criteria and results:
[study](../../docs/studies/2026-09-23-ff-affine.md).
`workload.py` fixes 13 families and an independent coefficient-array model
oracle. Seeds 0..9 are initial; 10..19 are fresh confirmation. Unknown is
unsolved and is excluded from solved cost ratios.

Run each immutable cell once with a cached standard-release binary:

```sh
python3 bench/ff_affine_perf/run.py precompile/SHA/nixie --sha SHA \
  --role treatment --root precompile
python3 bench/ff_affine_perf/run.py precompile/SHA/nixie --sha SHA \
  --role treatment --root precompile --first-seed 10
python3 bench/ff_affine_perf/report.py precompile SHA --csv report.csv
python3 -m unittest discover -s bench/ff_affine_perf -p 'test_*.py'
```

Baseline is the previous verified source `260c0728`; the reference is
installed Z3 4.16.0 (`ddb49568d3520e99799e364fb22f35fc67d887b1`). Use roles
`baseline` or `reference` to collect missing cells for those binaries.
Z3 uses the existing exact BV encoding with specialized Frobenius squaring.
This is a comparison of full CLI invocations, not native Z3 field support.

The result store retains canonical records, raw inputs/output, manifests
and alias manifests. Exact existing invocations from the earlier FF suite
are reused by source, binary, host, input, seed, CPU, counter and cap;
only off-clock verification/reporting changed. Their original record IDs
and harness identities remain intact. Z3's certified label aliases the
identical ordinary formula. The budget case now requests model values so
newly solved answers can be independently checked. The old frozen benchmark
and its historical Unknown expectations are unchanged.
