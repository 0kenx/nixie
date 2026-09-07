# Specialized ordinary propagation

## Registration

Kissat specializes `proplit.h` for search and probing propagation. Nixie's
single loop carries bounded-propagation, LRAT, lazy-hyper-binary, and reason
diagnostic checks through ordinary search even when all four are disabled.
Dispatch once into one of two instantiations of the same loop: ordinary
propagation with those branches compile-time absent, or the complete loop.
No new propagator, ordering, tick formula, proof rule, or unsafe code.

Eligibility is established on entry. None of the ordinary path's callees
can enable these options during propagation. The extended instantiation
retains all current checks and side effects. Tests must compare full state
after propagation/backtracking and protect fallback eligibility, budgets,
and proof/theory use. Profile instrumentation remains on both paths.

Use cached `0263862` release baseline and the reduced-run scope agreed with
the user: seed-0 break/circuit screen, then seeds 1–3 on break, crn, circuit,
si2 and held-out j3037 seed 1 if promising. No new reference runs. CPU 10,
hardware instructions primary, cycles confirmation, exact output/model
identity. A performance landing requires at least 5% lower confirmation
geomean cycles, non-increasing instructions, and no input above +5% cycles.
Full workspace checks, SAT differentials/models and fresh available-Z3
parity precede any code landing. Report the restricted sample honestly.

## Verdict: rejected at the two-cell screen

Both complete outputs were byte-identical. Break/circuit instructions T/B
were 0.9947 / 0.9950; cycles T/B were 1.0212 / 1.0997. The screen does not
qualify this duplication of machine-code paths for landing. Source removed;
no confirmation sweep started. Patch, binary, raw outputs and PMU records
are retained under `precompile/de17156/benchmark/`. These are single-seed
screen outcomes, not statistical estimates of a regression or its cause.
