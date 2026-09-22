# Native sequences versus Z3: fixed-shape performance

This experiment measures the existing native sequence slice; it changes no
solver code. Nixie is the cached release binary from
`3a42cb2d7e7b3f8612a6b2d9abe760616919d133`. The reference is installed Z3
4.16.0. See the [pre-registered protocol](../../bench/native_sequences/README.md)
and [runner](../../bench/native_sequences/perf.py).

## Method and interpretation

The corpus contains 22 synthetic native SMT obligations, each measured with
ten requested seeds for each solver: 440 cells. Four families grow from
8 to 32, 128 and 512 elements. Three boundary/nesting cases and three probes
outside Nixie's finite-shape fragment complete the corpus. Both solvers read
identical SMT inputs. No string encoding, TLA datatype adapter or translated
update operator is included in this comparison.

The primary metric is retired user instructions for the complete executable,
including parsing, sequence reduction and Nixie's independent SAT model
validation. Measurements use a single pinned P-core (CPU 6) and require a
100%-enabled `cpu_core/instructions/u` counter. Kernel work is excluded.
Small allocator/process variation remains; these are hardware instruction
counts, not identical cross-solver abstract search ticks. Conflict counts and
Z3's `rlimit` count would not cover comparable work and are not used.

The six-second wall limit is an external supervision cap, not a solver policy
or a primary cost metric. Its solved counts describe this host under its
concurrent load. Wall measurements include perf startup. Completed instruction
ratios exclude timeouts and Unknown; a partially counted timeout is never a
cheap solve. Cases that solve for only one solver remain in the coverage
table. No hindsight-selected configuration or extra seed run is used.

The sequence reduction creates its child solver from `self.config.clone()`;
the requested seed was applied to the outer SAT engine, not stored in that
configuration. Thus the ten Nixie seeds repeat its default child search.
They do not establish variance over independently seeded native search.
Z3 receives all ten seed settings. This is a measurement limitation and a
future configuration-propagation issue, not a seed-tuning experiment.

Expected verdicts have direct sequence identities or explicit witnesses,
listed in the protocol. No reference Unknown counts as an agreement and no
solver-produced UNSAT proof is claimed. Raw results therefore preserve their
honest validation status in a dedicated run-once cache instead of asserting
the canonical benchstore schema's mandatory checked-model-or-proof field.

## Results

**Nixie solved 19/22 cases (190/220 runs); Z3 solved 18/22
(180/220 runs).** All cases had the same outcome for all ten requested
seeds. Nixie returned `Unknown` on the three symbolic probes. Z3 reached
the six-second cap on `split-128`, `tail-512`, `split-512`, and
`history-512`. There were **zero wrong verdicts, zero errors and zero
invalid counters among completed runs**. All 150 pairs in the 15
commonly solved cases agree decisively.

Over those 15 cases, equally weighted, the geometric mean
**Nixie/Z3 instruction ratio is 0.0562 (17.8× fewer instructions)**.
This is a conditional microbenchmark work ratio, not a general speedup:
the corpus deliberately exercises shapes available to Nixie’s reduction,
and neither the four reference timeouts nor the three Nixie Unknown cases
enter that ratio. Z3’s broader sequence support matters on those probes.

Instruction counts below are **millions**, shown as median [min–max]
over ten requested seeds. The ratio is the geometric mean of paired
Z3/Nixie counts; values above one mean Nixie used fewer instructions.
No partial timeout counters enter the table.

| Case | Nixie M instructions | Z3 M instructions | Z3/Nixie |
|---|---:|---:|---:|
| append-8 | 2.669 [2.668–2.708] | 8.585 [8.585–8.585] | 3.21× |
| tail-8 | 2.669 [2.666–2.711] | 40.974 [40.974–40.974] | 15.29× |
| split-8 | 2.607 [2.585–2.628] | 45.777 [45.777–45.777] | 17.56× |
| history-8 | 6.133 [6.129–6.153] | 32.925 [32.925–32.926] | 5.37× |
| append-32 | 2.780 [2.746–2.786] | 8.589 [8.589–8.589] | 3.09× |
| tail-32 | 2.744 [2.741–2.784] | 614.546 [614.546–614.547] | 222.78× |
| split-32 | 2.731 [2.692–2.733] | 453.912 [453.911–453.913] | 166.43× |
| history-32 | 22.171 [22.157–22.189] | 452.765 [452.765–452.766] | 20.42× |
| append-128 | 3.011 [3.009–3.013] | 8.590 [8.590–8.590] | 2.85× |
| tail-128 | 3.055 [3.015–3.055] | 44104.587 [44104.558–44104.617] | 14475.75× |
| split-128 | 3.115 [3.080–3.120] | timeout | — |
| history-128 | 255.054 [254.486–255.742] | 31839.852 [31839.850–31839.853] | 124.83× |
| append-512 | 4.159 [4.158–4.165] | 8.590 [8.590–8.590] | 2.07× |
| tail-512 | 4.142 [4.139–4.181] | timeout | — |
| split-512 | 4.663 [4.627–4.669] | timeout | — |
| history-512 | 28860.809 [28694.080–29754.025] | timeout | — |
| empty | 2.538 [2.500–2.540] | 8.491 [8.491–8.491] | 3.36× |
| concat-disequality | 3.195 [3.191–3.198] | 15.283 [15.283–15.284] | 4.78× |
| nested-congruence | 2.759 [2.758–2.800] | 8.557 [8.557–8.558] | 3.09× |
| symbolic-append | unknown | 8.525 [8.525–8.526] | — |
| symbolic-read | unknown | 37.586 [37.586–37.587] | — |
| symbolic-word-equation | unknown | 11.004 [11.004–11.005] | — |

The boundary cases include process startup and mostly trivial simplification;
their roughly 3–5× instruction ratios should not be read as sequence-search
speedups. The append family’s ratio shrinks from 3.21× at length 8 to
2.07× at length 512: eager materialization is real work even when the
reference can rewrite the length identity without expanding elements.

Nixie’s fully constrained history family grows from 6.13M to 22.17M,
255.05M and 28,860.81M instructions. Length 512 costs **113×** length
128 despite only a 4× increase in elements. This is a remaining performance
problem in the supported fragment, even though Z3 times out there.

Source inspection shows that each original assertion invokes `evaluate`
with fresh maps and traverses the complete sequence model again; repeated
reads therefore cannot share that validation work. This identifies one
source of superlinear work, not an attribution of the entire measured
113× increase. The separate sampling profile below narrows that question.

Secondary wall medians (including perf startup):

* `append-512`: Nixie 0.017s; Z3 0.027s.
* `tail-128`: Nixie 0.030s; Z3 5.637s.
* `history-128`: Nixie 0.037s; Z3 3.106s.
* `history-512`: Nixie 1.776s; Z3 6.156s (external timeout).

These times describe this run under concurrent host load; they are not the
primary comparison. No global performance policy was selected from them.

Binary SHA-256 values:

* Nixie: `2951155fb94a15b94125bc175cdfe93b316488368175aa740765594f17ddc428`.
* Z3: `e01bc8bcd4d487be9666873545532ff4cd705ad4cd746f616290fac756f12c46`.

## Diagnostic profile of history-512

After the comparison, a separate instruction-sampling configuration ran
`history-512`, seed 0, on the same pinned core and binary. The initial
one-million-instruction sampling period exceeded the kernel's 2,000 samples/s
limit: 1,783 throttle events, 1,782 unthrottle events. That profile is retained
as an invalid attribution experiment; its apparent 3.568B sampled events
must not replace the full `perf stat` instruction count.

A distinct 20-million-instruction sampling period produced 1,443 samples,
approximately **28.86B instructions**, with **zero throttle/unthrottle/lost
events**. Its sampling estimate agrees with the benchmark's 28.861B median.
`getenv` accounts for 7.00% of samples and `__strncmp_avx2` for 20.10%, with
another 1.73% in `strncmp@plt`. This points to environment lookup and string
comparison work worth investigating. Without call chains, not every string
comparison can be attributed to an environment lookup.

The binary is stripped, so many hot Rust locations remain numeric addresses;
this profile cannot identify their functions reliably. A follow-up should
profile a symbolized equivalent and inspect both repeated sequence-model
validation and environment probes. Do not assume removing one accounts for
the whole scaling problem. No optimization was attempted in this study.

Both profile configurations, inputs, commands, raw data and text reports are
retained beside the benchmark records. They are supplementary diagnostic
runs, not additions to or replacements for the 440 comparison cells.
The runner removes inherited `NIXIE_*` tuning variables but otherwise inherits
the process environment. Environment size was not controlled across hosts;
these results apply to this host and session, particularly for environment
lookup cost. No cross-host reuse or attribution claim follows.

## Reproduction and validation

```sh
python3 -B bench/native_sequences/perf.py
python3 -B bench/native_sequences/perf.py --summarize-only
```

The manifest and raw stdout/stderr, return codes, instruction counters,
elapsed times, binary hashes, host identity and exact generated inputs live
under `precompile/3a42cb2d7e7b3f8612a6b2d9abe760616919d133/benchmark/
native-sequences-z3-perf/`. Existing cells are reused without re-execution;
invalid counters and errors are retained. Summary generation is read-only
with respect to measured cells.

Python syntax and all generated inputs' parenthesis balance are checked.
No Rust source or binary changed, so the full build, test, lint, doc, parity
and performance landing gates recorded in the
[implementation study](2026-09-22-native-sequences.md) apply to the exact
measured binary. A formatting check in the shared checkout also found
formatting differences in another agent's untracked
`nixie-solver/tests/trans_delta_icp.rs`; that file was left untouched and is
excluded from this benchmark commit.
