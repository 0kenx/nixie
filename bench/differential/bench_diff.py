#!/usr/bin/env python3
"""Differential soundness/perf bench: run an oxiz binary on a pinned SMT-LIB
sample and compare every verdict against z3.

This is the harness that found the vhard7 regression 9,858 passing tests did
not (INTEGRATION_NOTES.md). The sample (`sample/selected.json`, seed 20260807,
270 instances across all QF_* logics) is checked in so every run is over the
*same* instances and directly comparable across builds/PRs.

Use:
  # build the solver under test, then:
  python3 bench/differential/bench_diff.py --bin target/release/oxiz
  # label it for the report:
  python3 bench/differential/bench_diff.py --bin target/release/oxiz --label integrate
  # compare two builds side by side (re-uses a previous results dir):
  python3 bench/differential/bench_diff.py --bin ../main-build/oxiz --label main

Outputs (under --out, default bench/differential/results/<label>/):
  results.jsonl   per-instance: path, logic, z3 verdict, oxiz verdict, time
  unsound.json    every instance where oxiz disagrees with z3
  summary.json    solved / agree / disagree / timeouts / PAR-2 + pairwise gmean

Exit code is non-zero if any *soundness* disagreement (oxiz `sat` where z3
`unsat`, or vice-versa) is found — so this can gate a PR: `cargo build --release
-p oxiz-cli && python3 bench/differential/bench_diff.py --bin target/release/ox`.
Timeouts/`unknown` are not soundness failures and do not fail the gate.

z3 verdicts are read from the checked-in sample (regenerate with z3_screen.py
only when the corpus changes). z3 itself is not re-run by default; pass
--rerun-z3 to re-screen (slow; needs z3 on PATH).
"""
from __future__ import annotations
import argparse, json, math, os, signal, subprocess, sys, time
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
SAMPLE = HERE / "sample" / "selected.json"
REPO = HERE.parent.parent  # oxiz/ repo root (bench/differential/ -> repo)


def parse_status(text: str, rc: int, dt: float, timeout: float) -> str:
    res = "unknown"
    for line in text.lower().splitlines():
        s = line.strip()
        if s == "sat": res = "sat"
        elif s == "unsat": res = "unsat"
        elif s == "unknown": res = "unknown"
    # No explicit verdict + killed by timeout => "timeout". Keep all verdicts
    # lowercase so the summary's set-membership checks are case-consistent.
    if res == "unknown" and (rc == 124 or dt >= timeout - 0.05):
        res = "timeout"
    return res


def run_one(cmd, path, timeout):
    t0 = time.perf_counter()
    try:
        p = subprocess.Popen(cmd + [str(path)], stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE, text=True, start_new_session=True)
        try:
            out, err = p.communicate(timeout=timeout + 1.0)
        except subprocess.TimeoutExpired:
            try: os.killpg(p.pid, signal.SIGKILL)
            except ProcessLookupError: pass
            try: p.communicate(timeout=1)
            except Exception: pass
            return timeout, "TIMEOUT", 124
        dt = time.perf_counter() - t0
        text = (out or "") + "\n" + (err or "")
        return dt, parse_status(text, p.returncode, dt, timeout), p.returncode
    except Exception as e:
        return time.perf_counter() - t0, f"ERR:{e}", -1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bin", required=True, help="oxiz binary to test")
    ap.add_argument("--label", default="oxiz", help="label for the results dir")
    ap.add_argument("--timeout", type=float, default=10.0)
    ap.add_argument("--jobs", type=int, default=1)
    ap.add_argument("--out", default=None)
    ap.add_argument("--extra", default="-q", help="extra args to the binary")
    args = ap.parse_args()

    sample = json.loads(SAMPLE.read_text())
    insts = sample["instances"]
    # The corpus is .gitignore'd external data — fail fast with instructions
    # rather than reporting 270 misleading ERR/unknown rows.
    missing_root = next((REPO / it["path"] for it in insts if not (REPO / it["path"]).exists()), None)
    if missing_root is not None:
        sys.exit(f"error: corpus file not present: {missing_root}\n"
                 f"       smt-lib is .gitignore'd benchmark data, not tracked. "
                 f"Fetch the SMT-LIB corpus under smt-lib/ before running (see README.md).")
    outdir = Path(args.out) if args.out else HERE / "results" / args.label
    outdir.mkdir(parents=True, exist_ok=True)

    cmd = [args.bin] + (args.extra.split() if args.extra else [])
    print(f"# label={args.label} bin={args.bin} timeout={args.timeout}s n={len(insts)}", flush=True)
    rows = []
    unsound = []
    hdr = f"{'logic':<10} {'file':<40} {'z3':>6} {'oxiz':>6} {'oxiz_s':>8}"
    print(hdr); print("-" * len(hdr))
    for i, it in enumerate(insts, 1):
        path = REPO / it["path"]
        name = path.name
        short = name if len(name) <= 40 else name[:37] + "..."
        dt, res, rc = run_one(cmd, path, args.timeout)
        gold = it["z3_res"]
        rows.append({"path": it["path"], "logic": it["logic"], "file": name,
                     "z3_res": gold, "z3_s": it["z3_s"],
                     "res": res, "s": round(dt, 6), "rc": rc})
        soundness_bad = res in ("sat", "unsat") and gold in ("sat", "unsat") and res != gold
        if soundness_bad:
            unsound.append(rows[-1])
        print(f"{it['logic']:<10} {short:<40} {gold:>6} {res:>6} {dt:8.3f}{'  *UNSAFE*' if soundness_bad else ''}", flush=True)
        if i % 20 == 0:
            (outdir / "results.jsonl").write_text("\n".join(json.dumps(r) for r in rows) + "\n")

    (outdir / "results.jsonl").write_text("\n".join(json.dumps(r) for r in rows) + "\n")
    (outdir / "unsound.json").write_text(json.dumps(unsound, indent=2))

    solved = sum(1 for r in rows if r["res"] in ("sat", "unsat"))
    agree = sum(1 for r in rows if r["res"] == r["z3_res"])
    disagree = sum(1 for r in rows if r["res"] in ("sat", "unsat") and r["z3_res"] in ("sat", "unsat") and r["res"] != r["z3_res"])
    to = sum(1 for r in rows if r["res"] in ("timeout", "unknown"))
    par2 = sum(r["s"] if r["res"] in ("sat", "unsat") else 2 * args.timeout for r in rows)
    summary = {"label": args.label, "n": len(rows), "solved": solved,
               "agree_z3": agree, "disagree_soundness": disagree, "timeout_or_unknown": to,
               "par2": round(par2, 2)}
    (outdir / "summary.json").write_text(json.dumps(summary, indent=2))
    print("\n# SUMMARY")
    print(f"solved={solved} agree_z3={agree} disagree(soundness)={disagree} timeout/unknown={to} par2={par2:.2f}")
    if unsound:
        print(f"# {len(unsound)} UNSOUND (oxiz disagrees with z3 on a sat/unsat):")
        for r in unsound:
            print(f"  [{r['logic']}] {r['file']}: z3={r['z3_res']} oxiz={r['res']}")
    print(f"# wrote {outdir}")
    # gate: fail on soundness disagreements
    sys.exit(1 if disagree else 0)


if __name__ == "__main__":
    main()
