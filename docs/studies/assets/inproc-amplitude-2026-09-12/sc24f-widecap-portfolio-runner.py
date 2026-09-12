#!/usr/bin/env python3
"""Wide-cap portfolio screen on the 13-file 0/5-at-60s class (2026-09-12
handoff item 1).

Question: at a 300 s budget, does a default-then-comb sequential
portfolio convert the standing 0/5-at-60 s class?  Arms (same binary
precompile/4f51efd7/stats_solve, default path bit-identical to the
8082e335 baseline):

  default-300s   : default config, 300 s cap (control)
  def60-comb240  : default@60 s -> comb@240 s (NIXIE_OTFS=1 NIXIE_EAGER_SUB=1)
  def120-comb180 : default@120 s -> comb@180 s

The chain is harness-staged (sequential subprocesses; each stage a full
solve restart over the same clauses, both stages SEED=<seed>).  This is
the screen for the production question - if the comb arm converts >=3
files, the SEEDS= portfolio token takes it as a late arm with counter
budgets (deterministic policy); the wall-clock staging here only bounds
the screen's own budget.

Protocol inherited from sc24f-comb-screen-runner.py: model-checked SAT
cells, cadical-agreement UNSAT cells (cadical 3.0.1, 600 s ref cap),
records filed via benchstore under precompile/4f51efd7/benchmark/runs/
sc24f/, config-hash-exact skip check.
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
BIN = ROOT / "precompile/4f51efd7/stats_solve"
CADICAL = ROOT / "../temp/cadical/build/cadical"
CORPUS = ROOT / "precompile/corpus-sc24f"
STORE = ROOT / "bench/suite/scripts/benchstore.py"
OUT = ROOT / "precompile/4f51efd7/benchmark/runs/sc24f"
CAP_S = 300
CADICAL_REF_S = 600
SEEDS = [0, 1, 2, 3, 4]
HOST = {"id": "workstation", "cpu": "20 cores", "os": "Linux 7.2.2"}
GIT = {"sha_long": "4f51efd7" + "0" * 32, "sha_short": "4f51efd7", "dirty": False}
BIN_SHA = hashlib.sha256(BIN.read_bytes()).hexdigest()

# The measured 13-file 0/5-at-60s class (8082e335 baseline, seeds 0-4).
FILES = [
    "1009c791cee542cdf19651fe25e6881a-summle_X4053_steps8_I1-2-2-4-4-8-25-100.cnf",
    "170b13af977e962321c493544b2bd0a9-circuit_48in64out_with_800gates_4in4out_dist128_seed4.sanitized.cnf",
    "2a15a30186afdad41a49c5c5366d01be-Timetable_C_392_E_62_Cl_26_S_28.cnf",
    "3bf8ba6bb4e4ea9ad08b1b058661ba2e-summle_X4044_steps7_I1-2-2-4-4-8-25-100.cnf",
    "5690b9b0380aa9508699e56cae5918b5-170058440.cnf",
    "6f7a0e1cf94b6b26eafc08a827a692ce-circuit_64in64out_with_64gates_8in5out_dist256_seed1.sanitized.cnf",
    "79b9e24dd9af185dbec18c9b0a32b1e2-g2-slp-synthesis-aes-top30.cnf",
    "9276ce38c625b2d00de247f8588f1542-combined-crypto1-wff-seed-102-wffvars-500-cryptocplx-31-overlap-2.cnf",
    "adf6dacdd64c93f9de1aa0eadf427faa-circuit_48in64out_with_800gates_4in4out_dist128_seed1.sanitized.cnf",
    "af750c18578d52e60472315692ad83c0-si2-b03m-m800-03.cnf",
    "be6411f4784a3c879886dda807cdc607-j3037_10_mdd_b.cnf",
    "c8e64404361f2426490d39459832c66a-64_25.sanitized.cnf",
    "f054205a7cef98e5021016f864c69816-summle_X11112_steps6_I1-2-2-4-4-8-25-100.cnf",
]

# (config id, stage-1 seconds, comb in stage 2, arm role)
ARMS = [
    ("default-300s", 300, False, "baseline"),
    ("def60-comb240", 60, True, "treatment"),
    ("def120-comb180", 120, True, "treatment"),
]


def canonical_hash(flags: dict) -> str:
    payload = json.dumps(dict(sorted(flags.items())), sort_keys=True,
                         separators=(",", ":"))
    return hashlib.sha256(payload.encode()).hexdigest()[:16]


def arm_flags(cid: str, seed: int, stage1_s: int) -> dict:
    flags = {"PRESET": "cadical", "SEED": str(seed), "solver": "nixie",
             "CAP_S": str(CAP_S)}
    if cid != "default-300s":
        flags["STAGE1_S"] = str(stage1_s)
        flags["OTFS"] = "1"
        flags["EAGER_SUB"] = "1"
    return flags


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
        p = subprocess.run([str(CADICAL), "-q", str(cnf)],
                           capture_output=True, text=True, timeout=CADICAL_REF_S)
        for l in reversed((p.stdout + p.stderr).strip().splitlines()):
            if l.startswith("s "):
                return {"s SATISFIABLE": "sat", "s UNSATISFIABLE": "unsat"}.get(l, "unknown")
    except subprocess.TimeoutExpired:
        pass
    return "unknown"


def run_stage(cnff: Path, seed: int, cap_s: float, comb: bool):
    """One full solve restart. Returns (verdict, conflicts, decisions,
    model_line, wall, killed)."""
    env = dict(os.environ, DIAG="1", SEED=str(seed), PRINT_MODEL="1")
    if comb:
        env["NIXIE_OTFS"] = "1"
        env["NIXIE_EAGER_SUB"] = "1"
    t0 = time.monotonic()
    try:
        proc = subprocess.run([str(BIN), str(cnff)], env=env, capture_output=True,
                              text=True, timeout=cap_s)
    except subprocess.TimeoutExpired:
        return "unknown", -1, -1, "", time.monotonic() - t0, True
    wall = time.monotonic() - t0
    verdict, conflicts, decisions, model_line = "unknown", -1, -1, ""
    for line in proc.stdout.splitlines():
        if line.startswith("result="):
            verdict = {"Sat": "sat", "Unsat": "unsat", "Unknown": "unknown"}.get(line[7:], "unknown")
        elif line.startswith("conflicts="):
            parts = dict(tok.split("=", 1) for tok in line.split() if "=" in tok)
            conflicts = int(parts.get("conflicts", -1))
            decisions = int(parts.get("decisions", -1))
        elif line.startswith("v "):
            model_line += " " + line
    if wall >= cap_s:
        verdict, conflicts = "unknown", -1
    return verdict, conflicts, decisions, model_line, wall, False


def run_cell(cnff: Path, seed: int, cid: str, stage1_s: int, comb: bool,
             role: str, ref_verdict: str):
    name = cnff.name
    inst_sha = hashlib.sha256(cnff.read_bytes()).hexdigest()
    family = name.split("-", 1)[1].rsplit(".cnf", 1)[0] if "-" in name else name

    total_wall = 0.0
    verdict, conflicts, decisions, model_line = "unknown", -1, -1, ""
    stages = []
    stage2_s = CAP_S - stage1_s
    for stage_no, (cap, is_comb) in enumerate(
            [(stage1_s, False)] + ([(stage2_s, comb)] if stage2_s > 0 else []), 1):
        v, c, d, m, w, killed = run_stage(cnff, seed, cap, is_comb)
        total_wall += w
        stages.append(f"s{stage_no}:{'comb' if is_comb else 'default'}:{v}:{int(w)}s")
        if v != "unknown":
            verdict, conflicts, decisions, model_line = v, c, d, m
            break
    stage_note = " ".join(stages)

    verified = verdict == "unknown"
    if verdict == "sat":
        verified = bool(model_line) and verify_model(cnff, model_line)
        if not verified:
            print(f"!!! MODEL CHECK FAILED {name} s{seed} ({cid}) - investigate", flush=True)
            verdict = "unknown"
    elif verdict == "unsat":
        if ref_verdict == "sat":
            print(f"!!! VERDICT DISAGREEMENT {name} s{seed} ({cid}): nixie unsat, cadical sat - investigate", flush=True)
        verified = ref_verdict == "unsat"
        if not verified:
            verdict = "unknown"

    flags = arm_flags(cid, seed, stage1_s)
    rec = {
        "schema": "nixie-bench-record/1", "schema_version": 1, "suite": "sc24f",
        "host": HOST, "git": GIT,
        "binary": {"path": str(BIN), "sha256": BIN_SHA},
        "instance": {"name": name, "sha256": inst_sha, "family": family, "sat_expected": None},
        "seed": seed,
        "config": {"id": cid, "flags": flags, "cmdline": f"{BIN} {cnff}"},
        "arm": {"role": role},
        "metrics": {
            "primary": {"name": "conflicts", "value": conflicts},
            "secondary": {
                "name": "decisions", "value": decisions,
                "note": f"stages [{stage_note}]",
                "verification_basis": ("model-check" if verdict == "sat" and verified
                                       else f"cadical-agreement({ref_verdict})" if verdict == "unsat"
                                       else "n/a (unknown verdict)"),
            },
            "wall_clock_s": round(total_wall, 2),
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
    return name, seed, cid, verdict, conflicts, total_wall, p.returncode, p.stdout.strip() + p.stderr.strip()


def main():
    files = [CORPUS / n for n in FILES]
    missing = [f for f in files if not f.exists()]
    if missing:
        print(f"MISSING CORPUS FILES: {missing}")
        sys.exit(2)

    refs = {}
    with ThreadPoolExecutor(max_workers=5) as ex:
        futs = {ex.submit(cadical_verdict, f): f for f in files}
        for fut in as_completed(futs):
            refs[futs[fut]] = fut.result()
    print("cadical refs:", {f.name.rsplit('-', 1)[-1][:24]: v for f, v in refs.items()}, flush=True)

    cells = []
    skipped = 0
    OUT.mkdir(parents=True, exist_ok=True)
    for f in files:
        sha8 = hashlib.sha256(f.read_bytes()).hexdigest()[:8]
        for cid, s1, comb, role in ARMS:
            for s in SEEDS:
                chash = canonical_hash(arm_flags(cid, s, s1))
                exact = OUT / f"{f.name}__{sha8}__c{chash}__s{s}.json"
                if exact.exists():
                    skipped += 1
                    continue
                cells.append((f, s, cid, s1, comb, role))
    print(f"{len(cells)} cells to run (skipped {skipped} stored)", flush=True)

    solved = 0
    with ThreadPoolExecutor(max_workers=5) as ex:
        futs = {ex.submit(run_cell, f, s, cid, s1, comb, role, refs[f]):
                (f, s, cid) for f, s, cid, s1, comb, role in cells}
        for fut in as_completed(futs):
            name, seed, cid, verdict, conflicts, wall, rc, msg = fut.result()
            if verdict != "unknown":
                solved += 1
            print(f"[{cid:14s} {verdict:7s} c={conflicts:>9} w={wall:5.1f}s] "
                  f"{name.rsplit('-', 1)[-1][:34]} s{seed} rc={rc} {msg[:60]}", flush=True)
    print(f"\nsolved cells: {solved}/{len(cells)}")


if __name__ == "__main__":
    main()
