#!/usr/bin/env python3
"""Multi-seed validation of the amplitude->trajectory decomposition cells.

Cells (Timetable, SEED in {0,1,3}, cap 500s):
  A fresh-default  : plain default solve of the dumped DEFAULT phase-2 formula
  B fresh-onesided : plain default solve of the dumped ONESIDED phase-2 formula
  C def-reset      : default + NIXIE_ELIM_RESET_PHASES=50000 (original CNF)
  D os-reset       : onesided + NIXIE_ELIM_RESET_PHASES=50000 (original CNF)
"""
import os, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path("/media/data/proj/nixie")
BIN = ROOT / "outputs/target-csr/release/examples/cnf_solve"
TT = ROOT / "precompile/corpus-sc24f/2a15a30186afdad41a49c5c5366d01be-Timetable_C_392_E_62_Cl_26_S_28.cnf"
F_DEF = ROOT / "outputs/tt-phase2-default.cnf"
F_OS = ROOT / "outputs/tt-phase2-onesided.cnf"
CAP = 500

def cell(name, seed, cnf, extra):
    env = dict(os.environ, DIAG="1", SEED=str(seed), **extra)
    t0 = time.monotonic()
    try:
        p = subprocess.run([str(BIN), str(cnf)], env=env, capture_output=True, text=True, timeout=CAP)
        out = p.stdout + p.stderr
        wall = time.monotonic() - t0
    except subprocess.TimeoutExpired as e:
        out = (e.stdout or b"").decode() + (e.stderr or b"").decode()
        wall = CAP
    verdict, conflicts = "timeout", -1
    for line in out.splitlines():
        if line.startswith("result="):
            verdict = line[7:]
        elif line.startswith("conflicts="):
            conflicts = int(line.split()[0].split("=")[1])
    return name, seed, verdict, conflicts, wall

jobs = []
for s in [0, 1, 3]:
    jobs.append(("fresh-default", s, F_DEF, {}))
    jobs.append(("fresh-onesided", s, F_OS, {}))
    jobs.append(("def-reset", s, TT, {"NIXIE_ELIM_RESET_PHASES": "50000"}))
    jobs.append(("os-reset", s, TT, {"NIXIE_ELIM_ONESIDED": "1", "NIXIE_ELIM_RESET_PHASES": "50000"}))

results = {}
with ThreadPoolExecutor(max_workers=6) as ex:
    futs = [ex.submit(cell, n, s, c, e) for (n, s, c, e) in jobs]
    for f in as_completed(futs):
        n, s, v, c, w = f.result()
        results.setdefault(n, []).append((s, v, c, round(w, 1)))
for n in sorted(results):
    for s, v, c, w in sorted(results[n]):
        print(f"{n:15s} seed={s} {v:8s} conflicts={c:>9} wall={w:7.1f}")
