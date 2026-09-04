#!/usr/bin/env python3
"""Offline re-validation: recompute model_status for every `sat` in a saved
results.jsonl using the FIXED (declaration-accurate) validator, then rewrite
results.jsonl / summary.json / families.json / unsound.json.

Reuses the saved verdicts (the quoting bug only touched model_status, never
the verdict). Only the sat rows are re-run (binary + z3); everything else is
recomputed from the corrected rows.
"""
import json, sys
from pathlib import Path
import importlib.util
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("bd", HERE / "bench_diff.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
REPO = HERE.parent.parent

BINS = {
    "main-validated": "target/release/nixie",
    "oz-v032": "/media/data/proj/nixie-v032/target/release/nixie",
}

class A:  # minimal args for _summary
    label = ""; timeout = 10.0; validate_models = True

for label, binpath in BINS.items():
    resdir = HERE / "results" / label
    rl = resdir / "results.jsonl"
    if not rl.exists():
        print(f"skip {label}: no results.jsonl"); continue
    rows = [json.loads(l) for l in rl.read_text().splitlines() if l.strip()]
    for r in rows: r["res"] = r["res"].lower()
    sat = [r for r in rows if r["res"] == "sat"]
    print(f"\n=== {label}: {len(rows)} rows, re-validating {len(sat)} sat ===", flush=True)
    done = 0
    for r in sat:
        path = REPO / r["path"]
        orig = path.read_text()
        ms, detail = m.validate_model("z3", binpath, "-q", path, orig, 10.0)
        r["model_status"] = ms
        r["model_detail"] = detail
        done += 1
        if done % 25 == 0:
            print(f"  {done}/{len(sat)}", flush=True)
    # recompute family-suspect + summary (mirrors bench_diff.main)
    from collections import defaultdict
    fam_counts = defaultdict(lambda: {"n":0,"disagree":0,"sat":0,"sat_valid":0,"sat_invalid":0})
    fam_bad = defaultdict(bool)
    for r in rows:
        f = r["family"]; fc = fam_counts[f]; fc["n"] += 1
        if r["res"] in ("sat","unsat"): fc[r["res"]] = fc.get(r["res"],0)+1
        if r.get("soundness_bad"): fc["disagree"] += 1
        if r["model_status"]=="invalid": fc["sat_invalid"] += 1
        if r["model_status"]=="valid": fc["sat_valid"] += 1
        if r.get("soundness_bad") or r["model_status"]=="invalid": fam_bad[f]=True
    for r in rows: r["family_suspect"] = fam_bad.get(r["family"], False)
    a = A(); a.label = label; a.timeout = 10.0
    summary = m._summary(rows, a, fam_counts)
    m._flush(resdir, rows)
    (resdir/"unsound.json").write_text(json.dumps([r for r in rows if r.get("soundness_bad")], indent=2))
    (resdir/"families.json").write_text(json.dumps(fam_counts, indent=2, default=dict))
    (resdir/"summary.json").write_text(json.dumps(summary, indent=2))
    print(f"  {label} CORRECTED: {json.dumps({k:summary[k] for k in ('solved','agree_z3','disagree_soundness','sat_total','sat_model_valid','sat_model_invalid','sat_trusted','unsat_trusted','trusted_total') if k in summary})}")
