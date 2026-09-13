#!/usr/bin/env python3
"""One-sided arm vs default at the 300s cap: are the 60s losses cap artifacts?"""
import os, subprocess, time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
ROOT = Path("/media/data/proj/nixie")
BIN = ROOT / "precompile/3036fe32/stats_solve"
FILES = [
 "2a15a30186afdad41a49c5c5366d01be-Timetable_C_392_E_62_Cl_26_S_28.cnf",
 "7429e380834066c206394139c9e1e17d-af-synthesis_stb_50_100_9_sat.cnf",
 "c2bfe541b7cff948fa3193e9ca0eddee-frb45-21-2.used-as.sat04-884.cnf",
 "79b9e24dd9af185dbec18c9b0a32b1e2-g2-slp-synthesis-aes-top30.cnf",
 "be6411f4784a3c879886dda807cdc607-j3037_10_mdd_b.cnf",
 "0876c518e5653369e20fb1ee0bb8db40-mp1-klieber2017s-0500-023-t12.cnf",
 "adf6dacdd64c93f9de1aa0eadf427faa-circuit_48in64out_with_800gates_4in4out_dist128_seed1.sanitized.cnf",
 "c8e64404361f2426490d39459832c66a-64_25.sanitized.cnf",
 "af750c18578d52e60472315692ad83c0-si2-b03m-m800-03.cnf",
]
CAP = 300
def run(job):
    f, seed, arm = job
    env = dict(os.environ, DIAG="1", SEED=str(seed))
    if arm: env["NIXIE_ELIM_ONESIDED"] = "1"
    t0 = time.monotonic()
    try:
        p = subprocess.run([str(BIN), str(ROOT / "precompile/corpus-sc24f" / f)],
                           env=env, capture_output=True, text=True, timeout=CAP)
    except subprocess.TimeoutExpired:
        return f, seed, arm, "timeout", -1, CAP
    v, c = "unknown", -1
    for line in p.stdout.splitlines():
        if line.startswith("result="): v = line[7:].lower()
        elif line.startswith("conflicts="): c = int(line.split()[0].split("=")[1])
    return f, seed, arm, v, c, round(time.monotonic() - t0, 1)
jobs = [(f, s, a) for f in FILES for s in range(5) for a in (False, True)]
res = {}
with ThreadPoolExecutor(max_workers=3) as ex:
    for fut in as_completed([ex.submit(run, j) for j in jobs]):
        f, seed, arm, v, c, w = fut.result()
        res[(f, seed, arm)] = (v, c, w)
from collections import defaultdict
per = defaultdict(lambda: defaultdict(int))
for (f, s, a), (v, c, w) in res.items():
    per[f][("def" if not a else "arm") + "_solved"] += v != "unknown"
    if v != "unknown":
        per[f][("def" if not a else "arm") + "_conf"] += c
for f in FILES:
    d, a = per[f], per[f]
    print(f"{f.split('-',1)[1][:34]:36s} default {d['def_solved']}/5 (c={d['def_conf']})  arm {a['arm_solved']}/5 (c={a['arm_conf']})")
