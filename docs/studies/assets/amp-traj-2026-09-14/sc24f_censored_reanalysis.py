#!/usr/bin/env python3
"""Censoring-aware re-analysis of the stored sc24f amplitude-arm cells.

Question (round-11 item 3): does the 60s cap misjudge elimination-amplitude
arms, or does the recorded "aggregate conflicts favors amplitude" claim
carry survivorship bias (both-decided geomean excludes the arms' timeout
losses)?

No new runs: reads precompile/<sha>/benchmark/runs/sc24f records only.

For each arm vs default (107b7868), joined on (file, seed):
  solved cells      : verdict == sat|unsat at the 60s cap (the gate metric)
  both-decided gm   : conflicts geomean over cells where BOTH decided
                      (reproduces the studies' recorded numbers = pipeline
                      validation, and shows the exclusion count/direction)
  censored score    : mean per-cell cost log-ratio with timeouts censored
                      at L:  both-solved -> ln(arm/def)
                             arm-only    -> -L   (win: default timed out)
                             def-only    -> +L   (loss: arm timed out)
                             both-timeout-> 0    (no evidence at this cap)
                      reported for L in {ln3, ln10, ln30}; negative = arm
                      cheaper.
"""
import json, math, sys
from collections import defaultdict
from pathlib import Path

ROOT = Path("/media/data/proj/nixie/precompile")
DEF = "107b7868"
ARMS = {"281de4c0": "indexed schedule", "93703871": "scaled clock",
        "06011ff4": "combo"}


def load(sha):
    cells = {}
    d = ROOT / sha / "benchmark/runs/sc24f"
    for f in d.glob("*.json"):
        r = json.loads(f.read_text())
        key = (r["instance"]["name"], r["seed"])
        cells[key] = (r["verdict"]["answer"], r["metrics"]["primary"]["value"])
    return cells


def main():
    base = load(DEF)
    print(f"default {DEF}: {len(base)} cells")
    for sha, label in ARMS.items():
        arm = load(sha)
        keys = sorted(set(base) & set(arm))
        d_solved = sum(1 for k in keys if base[k][0] in ("sat", "unsat"))
        a_solved = sum(1 for k in keys if arm[k][0] in ("sat", "unsat"))
        both = [k for k in keys if base[k][0] in ("sat", "unsat")
                and arm[k][0] in ("sat", "unsat")]
        arm_only = [k for k in keys if arm[k][0] in ("sat", "unsat")
                    and base[k][0] not in ("sat", "unsat")]
        def_only = [k for k in keys if base[k][0] in ("sat", "unsat")
                    and arm[k][0] not in ("sat", "unsat")]
        both_to = [k for k in keys if base[k][0] not in ("sat", "unsat")
                   and arm[k][0] not in ("sat", "unsat")]
        if both:
            gm = math.exp(sum(math.log(arm[k][1] / base[k][1])
                              for k in both if arm[k][1] > 0 and base[k][1] > 0)
                          / len(both))
        else:
            gm = float("nan")
        print(f"\n== {label} ({sha}) — {len(keys)} joined cells")
        print(f"   solved cells: default {d_solved} -> arm {a_solved} "
              f"(net {a_solved - d_solved:+d})")
        print(f"   cell classes: both-decided {len(both)}, arm-only {len(arm_only)}, "
              f"def-only {len(def_only)}, both-timeout {len(both_to)}")
        print(f"   both-decided conflicts gm (the recorded aggregate): {gm:.3f} "
              f"[excludes {len(arm_only) + len(def_only)} decided-by-one cells "
              f"({len(def_only)} of them arm LOSSES)]")
        for L, name in [(math.log(3), "ln3"), (math.log(10), "ln10"),
                        (math.log(30), "ln30")]:
            s = 0.0
            for k in keys:
                b, a = base[k], arm[k]
                bs = b[0] in ("sat", "unsat")
                asv = a[0] in ("sat", "unsat")
                if bs and asv and a[1] > 0 and b[1] > 0:
                    s += math.log(a[1] / b[1])
                elif asv and not bs:
                    s -= L
                elif bs and not asv:
                    s += L
            print(f"   censored mean log-ratio @{name}: {s / len(keys):+.4f} "
                  f"({'arm cheaper' if s < 0 else 'arm costlier'})")


if __name__ == "__main__":
    main()
