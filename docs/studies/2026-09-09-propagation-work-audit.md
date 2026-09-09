# Propagation work behind the Kissat wall gap

The qualified residual-cache landing `f9d6714` improves circuit seed-1
wall from 9.63 to 8.81 seconds, with identical Nixie state/output, while
the requested mode-matched Kissat takes 1.88 seconds. Nixie reports
19391470 processed trail literals and 186114 conflicts; Kissat reports
6684415 and 167929. Similar conflicts do not establish similar work.
See [the preceding result](2026-09-09-connected-residual-payloads.md).

## Questions and audited instrumentation

Separate propagation inside scheduled inprocessing from the remaining
work before blaming search/restart replay or elimination. Nixie's default
CaDiCaL preset runs effort-budgeted vivification, whereas the requested
Kissat flags explicitly disable it. Keep those policies and comparison
flags unchanged; this is a diagnostic attribution, not an ablation or a
heuristic enablement claim.

The existing `NIXIE_INPROC_TRACE=1` captures cumulative propagation deltas
around scheduled `inprocess` calls and each of its five passes. Its timers
are output only and do not feed policy. `NIXIE_LOG_ELIM=1` records phase
entry conflicts, original-clause counts, round completion, units and
cumulative resolution counts. The latter does not record all internal
propagations, and neither directly measures replay after restarts or the
final root queue reset. These coverage limits must survive the analysis.
Root rewinds have soundness obligations: pending root implications consumed
under temporary vivify assumptions must be rediscovered after backtracking;
do not remove queue resets based on timing alone.

The initial elimination audit also checked CaDiCaL `src/elim.cpp`: hitting
the round limit leaves a phase incomplete, exactly as Nixie's current
bound-growth rule does. Merely seeing no bound growth after two rounds is
not evidence of a porting bug. Eligibility (raw occurrence limit 100 vs
Kissat's default 2000) and definition extraction differ and deserve a
work-volume audit, rather than a blind threshold/default flip.

## Registration: one cached-binary diagnostic invocation

Use qualified `precompile/f9d6714/stats_solve`, measured binary SHA-256
`d1fbf1afa2c333b27d9ae4ba324878f1772d7043c917ccaa907717148abdd52e`,
source-equivalent to `a64b285`. Original circuit SHA-256
`d3338c04e29f5c8b7e75686fa30fd9927babb7b34b9f7c87785397662f59d8e2`,
seed 1, CPU 15, MAXC=10000000, `NIXIE_SWEEP=0`, printed model and
300-second emergency cap. Clear other study variables. Enable only the
two trace flags above. Capture stdout/stderr in anonymous tmpfs files,
record start and completion immediately, and write the canonical result
once. No automatic retry, new control, new Kissat run or performance claim
from traced elapsed time. Confirm no constrained competing userspace
thread includes CPU 15 before execution.

Require complete stdout identity with candidate record `ee11cd60c342c2fb`
and a model checked against the original CNF. Report all phase counts,
aggregate pass propagations, total eliminated variables and whether each
elimination round completed. Reconcile summed deltas with the terminal
counter; leave unmeasured phase/replay costs unassigned. Prefer existing
source/counter evidence over an additional observation run. The next
implementation, if justified, needs its own costed registration and
correctness argument; this trace cannot establish a policy win.
