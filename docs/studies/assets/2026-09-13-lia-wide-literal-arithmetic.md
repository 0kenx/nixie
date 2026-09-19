
## Continuation 34 (2026-09-18): NDIR2 default-on measured and REFUTED — a flag-new false `unsat` (item 71)

71. **The general narrow direction-2 (`NIXIE_S6_NDIR2=1`) does not default
    on: the measurement refutes it on both correctness and capacity
    grounds.**  A/B on the SAME binary (`precompile/bc5e0b7a/nixie`,
    env-flag only), survey seeds 20261000–02 × 600:

    | arm | gap_sat | unsat | timeouts | decisive |
    |---|---|---|---|---|
    | default (pinned-scoped) | 134 | **576** | 12 | 1626 |
    | `NIXIE_S6_NDIR2=1` | 131 | **570** | **46** | 1587 |

    The general form recovers 3 SAT-side gap members and loses **6 unsat
    verdicts** and +34 timeouts — net −39 decisive.  Canaries: `f1` stays
    `sat` under BOTH arms (its win is already captured by the SCOPED
    pinned default — the general form adds nothing there); `fi1` deflects
    to a timeout (the documented 180 s cost persists); the item-69/70
    false-`unsat` core deflects to a timeout too — a MASK, not a fix (the
    rehome fix in flight is the real one).  Soundness screen: wide 2×300
    and mixed seed 20261120 clean; **mixed seed 20261123: two false
    `unsat`s — one pre-existing at default (the rehome class, bytes at
    `assets/2026-09-18/false-unsat-rehome-class-20261123.smt2`), and one
    FLAG-NEW** (`default=sat, ndir2=unsat`, bytes at
    `assets/2026-09-18/false-unsat-ndir2-only-20261123.smt2`) — the
    general direction-2 derivation path can MANUFACTURE a wrong verdict
    on an instance the default solves correctly.  Verdict: the gate stays
    off; the scoped pinned form (wide-row states only, item 61) remains
    the landed default; any future revisit starts from the ndir2-only
    reproducer's decode (the general solve-through-narrow-rows path —
    distinct from the rehome defect, though both corrupt bound state).
