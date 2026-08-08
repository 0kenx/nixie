#!/usr/bin/env python3
"""Screen SMT-LIB with Z3 (τ=5s). Keep instances Z3 solves (sat/unsat) within timeout."""
from __future__ import annotations
import json, os, signal, subprocess, sys, time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

Z3 = os.environ.get("Z3", "z3")
TIMEOUT = float(os.environ.get("Z3_TIMEOUT", "5"))
JOBS = int(os.environ.get("JOBS", "16"))
LIST = Path(os.environ.get("LIST", "bench/differential/sample/all_smt2.txt"))
OUT = Path(os.environ.get("OUT", "bench/differential/results/z3_screen.jsonl"))
PROGRESS_EVERY = 200

def logic_of(p: str) -> str:
    parts = Path(p).parts
    for x in parts:
        if x.startswith("QF_") or x in ("UF", "UFLIA", "AUFLIA", "LIA", "NIA", "BV", "IDL"):
            return x
    return "UNKNOWN"

def run_z3(path: str):
    t0 = time.perf_counter()
    try:
        p = subprocess.Popen(
            [Z3, "-T:" + str(int(TIMEOUT)), path],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
            start_new_session=True,
        )
        try:
            # hard wall slightly above -T
            out, err = p.communicate(timeout=TIMEOUT + 2.0)
        except subprocess.TimeoutExpired:
            try: os.killpg(p.pid, signal.SIGKILL)
            except ProcessLookupError: pass
            try: p.communicate(timeout=1)
            except Exception: pass
            return {"path": path, "logic": logic_of(path), "s": TIMEOUT, "res": "TIMEOUT", "rc": 124}
        dt = time.perf_counter() - t0
        text = ((out or "") + "\n" + (err or "")).strip().lower()
        # last status line wins
        res = "UNKNOWN"
        for line in text.splitlines():
            s = line.strip()
            if s == "sat": res = "sat"
            elif s == "unsat": res = "unsat"
            elif s == "unknown": res = "unknown"
            elif "timeout" in s: res = "TIMEOUT"
        if res == "UNKNOWN" and dt >= TIMEOUT - 0.05:
            res = "TIMEOUT"
        return {"path": path, "logic": logic_of(path), "s": round(dt, 6), "res": res, "rc": p.returncode}
    except Exception as e:
        return {"path": path, "logic": logic_of(path), "s": 0.0, "res": f"ERR:{e}", "rc": -1}

def main():
    files = [ln.strip() for ln in LIST.read_text().splitlines() if ln.strip()]
    OUT.parent.mkdir(parents=True, exist_ok=True)
    # resume support
    done = set()
    if OUT.exists():
        with OUT.open() as f:
            for line in f:
                try:
                    done.add(json.loads(line)["path"])
                except Exception:
                    pass
    todo = [p for p in files if p not in done]
    print(f"# total={len(files)} done={len(done)} todo={len(todo)} jobs={JOBS} timeout={TIMEOUT}s", flush=True)
    n_ok = n_to = n_other = 0
    t_start = time.perf_counter()
    with OUT.open("a") as outf, ProcessPoolExecutor(max_workers=JOBS) as ex:
        futs = {ex.submit(run_z3, p): p for p in todo}
        for i, fut in enumerate(as_completed(futs), 1):
            r = fut.result()
            outf.write(json.dumps(r) + "\n")
            if i % 50 == 0:
                outf.flush()
            if r["res"] in ("sat", "unsat"):
                n_ok += 1
            elif r["res"] == "TIMEOUT":
                n_to += 1
            else:
                n_other += 1
            if i % PROGRESS_EVERY == 0 or i == len(todo):
                elapsed = time.perf_counter() - t_start
                rate = i / max(elapsed, 1e-9)
                eta = (len(todo) - i) / max(rate, 1e-9)
                print(
                    f"[{i}/{len(todo)}] ok={n_ok} to={n_to} other={n_other} "
                    f"rate={rate:.1f}/s eta={eta/60:.1f}m",
                    flush=True,
                )
    print("# screen complete", flush=True)

if __name__ == "__main__":
    main()
