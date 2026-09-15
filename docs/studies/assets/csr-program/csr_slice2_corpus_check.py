#!/usr/bin/env python3
"""CSR dual-write slice-2 validation: 54-file corpus, three runs per file.

  A = treatment binary, flag OFF   (must be trajectory-identical to baseline)
  B = treatment binary, NIXIE_CSR_SHADOW=1 (dual-write active)
  C = baseline binary (pre-change HEAD), flag OFF

Checks:
  1. verdict + conflicts identical across A/B/C wherever a verdict was reached
  2. every B drift/rebuild line reports mismatched=0 (order-isomorphism proof)
  3. wall-time A vs C for the perf bar (flag-off branch cost)
"""
import os, subprocess, sys, time, re
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path("/media/data/proj/nixie")
CORPUS = ROOT / "precompile/corpus-sc24f"
TREAT = ROOT / "outputs/target-csr/release/examples/cnf_solve"
BASE = Path(sys.argv[1]) if len(sys.argv) > 1 else None
CAP_S = 60

def run(binpath, cnf, shadow):
    env = dict(os.environ, DIAG="1", SEED="0")
    if shadow:
        env["NIXIE_CSR_SHADOW"] = "1"
    t0 = time.monotonic()
    try:
        p = subprocess.run([str(binpath), str(cnf)], env=env, capture_output=True,
                           text=True, timeout=CAP_S)
        out = p.stdout + p.stderr
        wall = time.monotonic() - t0
    except subprocess.TimeoutExpired:
        return dict(verdict="timeout", conflicts=-1, wall=CAP_S, drift_bad=0, drift_n=0)
    verdict, conflicts = "unknown", -1
    for line in out.splitlines():
        if line.startswith("result="):
            verdict = line[7:]
        elif line.startswith("conflicts="):
            conflicts = int(line.split()[0].split("=")[1])
    drift_bad = sum(int(m) for m in re.findall(r"mismatched=(\d+)", out))
    drift_n = len(re.findall(r"\[csr-shadow\] drift@", out))
    return dict(verdict=verdict, conflicts=conflicts, wall=wall,
                drift_bad=drift_bad, drift_n=drift_n)

files = sorted(CORPUS.glob("*.cnf"))
print(f"{len(files)} files")
results = {}
def cell(f):
    a = run(TREAT, f, False)
    b = run(TREAT, f, True)
    c = run(BASE, f, False) if BASE else None
    return f.name, a, b, c

mismatch_traj, drift_fail, wall_a, wall_c = 0, 0, [], []
with ThreadPoolExecutor(max_workers=10) as ex:
    futs = [ex.submit(cell, f) for f in files]
    for fut in as_completed(futs):
        name, a, b, c = fut.result()
        results[name] = (a, b, c)
for name in sorted(results):
    a, b, c = results[name]
    traj_ok = (a["verdict"], a["conflicts"]) == (b["verdict"], b["conflicts"])
    if c:
        traj_ok = traj_ok and (a["verdict"], a["conflicts"]) == (c["verdict"], c["conflicts"])
    drift_ok = b["drift_bad"] == 0
    mismatch_traj += not traj_ok
    drift_fail += not drift_ok
    wall_a.append(a["wall"]); wall_c.append(c["wall"] if c else a["wall"])
    flag = "" if (traj_ok and drift_ok) else "  <<<< FAIL"
    print(f"{name[:44]:44s} {a['verdict']:8s} c={a['conflicts']:>9} drift={b['drift_bad']:3d}/{b['drift_n']:3d} "
          f"wallA={a['wall']:6.2f} wallC={(c['wall'] if c else a['wall']):6.2f}{flag}")
print(f"\ntrajectory mismatches: {mismatch_traj}   drift-failing files: {drift_fail}")
print(f"total wall A={sum(wall_a):.1f}s  C={sum(wall_c):.1f}s  ratio={sum(wall_a)/max(sum(wall_c),1e-9):.3f}")
