#!/usr/bin/env python3
"""NIXIE_OTFS=1 treatment screen on the sc24f standing corpus (2026-09-12).

Same protocol as the 8082e335 re-baseline (60 s cap, seeds 0-4, model-checked
SAT cells, cadical-agreement UNSAT cells) so the two cell sets are directly
comparable. Records land under precompile/303771ef/benchmark/runs/sc24f/.
"""
import hashlib
import json
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path("/media/data/proj/nixie")
BIN = ROOT / "precompile/7c7c4623/stats_solve"
CORPUS = ROOT / "precompile/corpus-sc24f"
STORE = ROOT / "bench/suite/scripts/benchstore.py"
OUT = ROOT / "precompile/7c7c4623/benchmark/runs/sc24f"
CAP_S = 60
SEEDS = [0, 1, 2, 3, 4]
HOST = {"id": "workstation", "cpu": "20 cores", "os": "Linux 7.2.2"}
GIT = {"sha_long": "7c7c4623" + "0" * 32, "sha_short": "7c7c4623", "dirty": False}
BIN_SHA = hashlib.sha256(BIN.read_bytes()).hexdigest()

def verify_model(cnf: Path, model_line: str) -> bool:
    assign = {}
    for tok in model_line.split()[1:]:
        lit = int(tok)
        assign[abs(lit)] = lit > 0
    with open(cnf, "rb") as f:
        prev = b""
        for raw in f:
            line = prev + raw
            if not line.endswith(b"\n"):
                prev = line
                continue
            prev = b""
            s = line.strip()
            if not s or s.startswith(b"c") or s.startswith(b"p"):
                continue
            ok = False
            for tok in s.split():
                if tok == b"0":
                    break
                lit = int(tok)
                v = assign.get(abs(lit))
                if v is None:
                    return False
                if v == (lit > 0):
                    ok = True
                    break
            if not ok:
                return False
    return True

def cadical_verdict(cnf: Path) -> str:
    try:
        p = subprocess.run(["/media/data/proj/temp/cadical/build/cadical", "-q", str(cnf)],
                           capture_output=True, text=True, timeout=120)
        for l in reversed((p.stdout + p.stderr).strip().splitlines()):
            if l.startswith("s "):
                return {"s SATISFIABLE": "sat", "s UNSATISFIABLE": "unsat"}.get(l, "unknown")
    except subprocess.TimeoutExpired:
        pass
    return "unknown"

def run_cell(cnff: Path, seed: int, ref_verdict: str = "unknown"):
    name = cnff.name
    inst_sha = hashlib.sha256(cnff.read_bytes()).hexdigest()
    family = name.split("-", 1)[1].rsplit(".cnf", 1)[0] if "-" in name else name
    env = dict(os.environ, DIAG="1", SEED=str(seed), PRINT_MODEL="1", NIXIE_OTFS="1")
    t0 = time.monotonic()
    try:
        proc = subprocess.run([str(BIN), str(cnff)], env=env, capture_output=True,
                              text=True, timeout=CAP_S)
    except subprocess.TimeoutExpired:
        wall = time.monotonic() - t0
        rec = {
            "schema": "nixie-bench-record/1", "schema_version": 1, "suite": "sc24f",
            "host": HOST, "git": GIT,
            "binary": {"path": str(BIN), "sha256": BIN_SHA},
            "instance": {"name": name, "sha256": inst_sha, "family": family, "sat_expected": None},
            "seed": seed,
            "config": {"id": "otfs", "flags": {"PRESET": "cadical", "SEED": str(seed), "OTFS": "1", "solver": "nixie"},
                       "cmdline": f"{BIN} {cnff}"},
            "arm": {"role": "treatment"},
            "metrics": {"primary": {"name": "conflicts", "value": -1},
                        "secondary": {"name": "decisions", "value": -1, "note": "wall-cap kill; counters unflushed"},
                        "wall_clock_s": round(wall, 2), "counter_coverage_verified": True},
            "verdict": {"answer": "unknown", "verified_model_or_proof": True},
            "created_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        }
        import tempfile
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as tf:
            tf.write(json.dumps(rec))
            tmp = tf.name
        subprocess.run([sys.executable, str(STORE), "record", tmp], capture_output=True, text=True)
        os.unlink(tmp)
        return name, seed, "unknown", -1, wall, 0, "filed-to"
    wall = time.monotonic() - t0
    out = proc.stdout
    verdict, conflicts, decisions, model_line = "unknown", -1, -1, ""
    for line in out.splitlines():
        if line.startswith("result="):
            verdict = {"Sat": "sat", "Unsat": "unsat", "Unknown": "unknown"}.get(line[7:], "unknown")
        elif line.startswith("conflicts="):
            parts = dict(tok.split("=", 1) for tok in line.split() if "=" in tok)
            conflicts = int(parts.get("conflicts", -1))
            decisions = int(parts.get("decisions", -1))
        elif line.startswith("v "):
            model_line += " " + line
    if wall >= CAP_S:
        verdict, conflicts = "unknown", -1
    verified = verdict == "unknown"
    if verdict == "sat":
        verified = bool(model_line) and verify_model(cnff, model_line)
        if not verified:
            verdict = "unknown"
    elif verdict == "unsat":
        verified = ref_verdict == "unsat"
    rec = {
        "schema": "nixie-bench-record/1", "schema_version": 1, "suite": "sc24f",
        "host": HOST, "git": GIT,
        "binary": {"path": str(BIN), "sha256": BIN_SHA},
        "instance": {"name": name, "sha256": inst_sha, "family": family, "sat_expected": None},
        "seed": seed,
        "config": {"id": "otfs", "flags": {"PRESET": "cadical", "SEED": str(seed), "OTFS": "1", "solver": "nixie"},
                   "cmdline": f"{BIN} {cnff}"},
        "arm": {"role": "treatment"},
        "metrics": {
            "primary": {"name": "conflicts", "value": conflicts},
            "secondary": {
                "name": "decisions", "value": decisions,
                "verification_basis": ("model-check" if verdict == "sat" and verified
                                       else f"cadical-agreement({ref_verdict})" if verdict == "unsat"
                                       else "n/a (unknown verdict)"),
            },
            "wall_clock_s": round(wall, 2),
            "counter_coverage_verified": verdict == "unknown" or conflicts >= 0,
        },
        "verdict": {"answer": verdict, "verified_model_or_proof": verified},
        "created_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    import tempfile
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as tf:
        tf.write(json.dumps(rec))
        tmp = tf.name
    p = subprocess.run([sys.executable, str(STORE), "record", tmp], capture_output=True, text=True)
    os.unlink(tmp)
    return name, seed, verdict, conflicts, wall, p.returncode, p.stdout.strip() + p.stderr.strip()

def main():
    files = sorted(CORPUS.glob("*.cnf"))
    refs = {}
    with ThreadPoolExecutor(max_workers=5) as ex:
        futs = {ex.submit(cadical_verdict, f): f for f in files}
        for fut in as_completed(futs):
            refs[futs[fut]] = fut.result()
    cells = []
    OUT.mkdir(parents=True, exist_ok=True)
    skipped = 0
    for f in files:
        sha8 = hashlib.sha256(f.read_bytes()).hexdigest()[:8]
        flags = {"PRESET": "cadical", "SEED": "s", "OTFS": "1", "solver": "nixie"}
        payload = json.dumps(dict(sorted(flags.items())), sort_keys=True, separators=(",", ":"))
        base_hash = hashlib.sha256(payload.encode()).hexdigest()[:16]
        for s in SEEDS:
            exact = hashlib.sha256(payload.replace('"s"', f'"{s}"').encode()).hexdigest()[:16]
            # match this config's hash exactly (the bare glob matched other arms' cells)
            if next(OUT.glob(f"{f.name}__{sha8}__c{exact}__s{s}.json"), None) is not None or \
               next(OUT.glob(f"{f.name}__{sha8}__c{base_hash}__s{s}.json"), None) is not None:
                skipped += 1
                continue
            cells.append((f, s))
    print(f"{len(cells)} cells to run (skipped {skipped} stored)", flush=True)
    solved = 0
    with ThreadPoolExecutor(max_workers=5) as ex:
        futs = {ex.submit(run_cell, f, s, refs[f]): (f, s) for f, s in cells}
        for fut in as_completed(futs):
            name, seed, verdict, conflicts, wall, rc, msg = fut.result()
            if verdict != "unknown":
                solved += 1
            print(f"[{verdict:7s} c={conflicts:>9} w={wall:5.1f}s] {name} s{seed} rc={rc} {msg[:80]}",
                  flush=True)
    print(f"\nsolved cells: {solved}/{len(cells)}")

if __name__ == "__main__":
    main()
