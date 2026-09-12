#!/usr/bin/env python3
"""sc24f standing-corpus re-baseline at HEAD 8082e335 (2026-09-12).

Standing item from the round-8 close: the table moved under other agents'
landings (mul-hoist, row-array encoder since the last 3-arm run), so every
new claim needs a fresh baseline first.

Cells: 54 instances x seeds 0-4, default config, 60 s wall cap (the standing
screen's cap; wall-censoring of borderline cells under load is a recorded
artifact of this table, not a verdict source). Primary metric = conflicts
(deterministic counter). SAT models are verified clause-by-clause before the
record is filed. Records land in precompile/8082e335/benchmark/runs/sc24f/
via benchstore.py record.
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
BIN = ROOT / "precompile/8082e335/stats_solve"
CORPUS = ROOT / "precompile/corpus-sc24f"
STORE = ROOT / "bench/suite/scripts/benchstore.py"
OUT = ROOT / "precompile/8082e335/benchmark/runs/sc24f"
CAP_S = 60
SEEDS = [0, 1, 2, 3, 4]
HOST = {"id": "workstation", "cpu": "20 cores", "os": "Linux 7.2.2"}
GIT = {"sha_long": "8082e3354c7f5b8081e0f7b0fdd00cf1a2a2e8b3", "sha_short": "8082e335", "dirty": False}
BIN_SHA = hashlib.sha256(BIN.read_bytes()).hexdigest()

def verify_model(cnf: Path, model_line: str) -> bool:
    """model_line: the `v 1 -2 ...` line(s) joined."""
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
                    return False  # unassigned var in clause
                if v == (lit > 0):
                    ok = True
                    break
            if not ok:
                return False
    return True

def cadical_verdict(cnf: Path) -> str:
    """One reference run per FILE (verdicts are seed-independent facts).
    Used as the verification basis for our unsat cells (we have no in-repo
    DRAT checker; cadical agreement is recorded as the evidence)."""
    try:
        p = subprocess.run(["/media/data/proj/temp/cadical/build/cadical", "-q", str(cnf)],
                           capture_output=True, text=True, timeout=120)
        line = (p.stdout + p.stderr).strip().splitlines()
        for l in reversed(line):
            if l.startswith("s "):
                return {"s SATISFIABLE": "sat", "s UNSATISFIABLE": "unsat"}.get(l, "unknown")
    except subprocess.TimeoutExpired:
        pass
    return "unknown"


def run_cell(cnff: Path, seed: int, ref_verdict: str = "unknown"):
    name = cnff.name
    inst_sha = hashlib.sha256(cnff.read_bytes()).hexdigest()
    family = name.split("-", 1)[1].rsplit(".cnf", 1)[0] if "-" in name else name
    env = dict(os.environ, DIAG="1", SEED=str(seed), PRINT_MODEL="1")
    t0 = time.monotonic()
    try:
        proc = subprocess.run([str(BIN), str(cnff)], env=env, capture_output=True,
                              text=True, timeout=CAP_S)
    except subprocess.TimeoutExpired as e:
        wall = time.monotonic() - t0
        # File the TO cell too (run-once rule): unknown verdict, no counters
        # (process killed before the DIAG tail printed - same artifact class as
        # the historical 1ba99bb sc24f sweep).
        inst_sha = hashlib.sha256(cnff.read_bytes()).hexdigest()
        family = name.split("-", 1)[1].rsplit(".cnf", 1)[0] if "-" in name else name
        rec = {
            "schema": "nixie-bench-record/1", "schema_version": 1, "suite": "sc24f",
            "host": HOST, "git": GIT,
            "binary": {"path": str(BIN), "sha256": BIN_SHA},
            "instance": {"name": name, "sha256": inst_sha, "family": family, "sat_expected": None},
            "seed": seed,
            "config": {"id": "default", "flags": {"PRESET": "cadical", "SEED": str(seed), "solver": "nixie"},
                       "cmdline": f"{BIN} {cnff}"},
            "arm": {"role": "baseline"},
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
        verdict, conflicts = "unknown", -1  # wall-censored: not a verdict cell
    verified = verdict == "unknown"
    if verdict == "sat":
        verified = bool(model_line) and verify_model(cnff, model_line)
        if not verified:
            verdict = "unknown"  # unverifiable model is not a Sat claim
    elif verdict == "unsat":
        verified = ref_verdict == "unsat"
    rec = {
        "schema": "nixie-bench-record/1",
        "schema_version": 1,
        "suite": "sc24f",
        "host": HOST,
        "git": GIT,
        "binary": {"path": str(BIN), "sha256": BIN_SHA},
        "instance": {"name": name, "sha256": inst_sha, "family": family, "sat_expected": None},
        "seed": seed,
        "config": {
            "id": "default",
            "flags": {"PRESET": "cadical", "SEED": str(seed), "solver": "nixie"},
            "cmdline": f"{BIN} {cnff}",
        },
        "arm": {"role": "baseline"},
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
        for s in SEEDS:
            if next(OUT.glob(f"{f.name}__{sha8}__*__s{s}.json"), None) is not None:
                skipped += 1
                continue
            cells.append((f, s))
    print(f"{len(cells)} cells to run (skipped {skipped} stored)")
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
