#!/usr/bin/env python3
"""Differential soundness/perf bench: run an oxiz binary on a pinned SMT-LIB
sample and compare every verdict against z3, with optional **model
validation** and a **family-neighbour** trust analysis.

This is the harness that found the `vhard7` regression 9,858 passing tests did
not (INTEGRATION_NOTES.md). The sample (`sample/selected.json`, seed 20260807,
270 instances across all QF_* logics) is checked in so every run is over the
*same* instances and directly comparable across builds/PRs.

Use:
  # build the solver under test, then:
  python3 bench/differential/bench_diff.py --bin target/release/oxiz
  # label it for the report:
  python3 bench/differential/bench_diff.py --bin target/release/oxiz --label integrate
  # PR soundness gate (verdict-only; no z3 needed):
  python3 bench/differential/bench_diff.py --bin target/release/oxiz --label pr
  # re-score a build WITH model validation + family check (needs z3 on PATH):
  python3 bench/differential/bench_diff.py --bin target/release/oxiz --label oz --validate-models
  # regress against a committed baseline summary.json (fails on completeness loss / new unsoundness):
  python3 bench/differential/bench_diff.py --bin ... --label pr --baseline bench/differential/results/main/summary.json

Outputs (under --out, default bench/differential/results/<label>/):
  results.jsonl   per-instance: path, logic, family, z3 verdict, oxiz verdict,
                  time, and (with --validate-models) model_status.
  unsound.json    every instance where oxiz disagrees with z3 on a sat/unsat.
  summary.json    solved / agree / disagree / timeouts / PAR-2 + (with
                  --validate-models) model-validity, family-suspect and trusted
                  counts (see TRUST MODEL below).
  families.json   per-family rollup (disagreements, sat model status) — the
                  family-neighbour view.

Exit codes:
  1  if any *soundness* disagreement (oxiz sat where z3 unsat, or vice-versa)
     is found — this gates a PR. Timeouts/unknown are not soundness failures.
  2  if --baseline is given and a regression is detected relative to it
     (agree_z3 down, or disagree_soundness up, or a previously-agreeing
     instance now disagrees). Reported in addition to the soundness exit.
  Note: the 4 known-unsound instances pinned in
  oxiz-solver/tests/known_unsound_regressions.rs will trip exit 1 on every run;
  that is expected and documented (see README.md). The completeness signal is
  in summary.json, not the exit code.

TRUST MODEL (what "solved" means under model validation)
--------------------------------------------------------
z3's embedded verdict is the satisfiability oracle: an oxiz `sat` that agrees
with z3 IS a correct answer (the instance genuinely is satisfiable). But
"correct" and "trustworthy-as-evidence-to-port" differ. We report:

  sat_model_valid    oxiz sat, z3 sat, and oziz's emitted model is *consistent*
                     with the assertions (z3: asserts∧model = sat). Real solve.
  sat_model_invalid  oxiz sat but its model contradicts the assertions (z3:
                     asserts∧model = unsat). The sat is bogus OR the model
                     emitter is broken — either way, not trustworthy evidence.
  sat_family_suspect an agreeing sat that lives in a family containing ANY
                     disagreement (verdict or model_invalid) for this solver.
                     The QF_ANIA pattern: one over-eager-sat mechanism scores
                     on the satisfiable half and errs on the unsatisfiable
                     half. Family flag = "don't credit this as a real capability."
  sat_trusted        agreeing sat AND model_valid AND not family_suspect.
                     The number to plan ports against.

The completeness count stays `agree_z3` (a correct verdict is a correct
verdict); `sat_trusted` is the *portable* subset. Reporting both keeps a model
*emission* bug (cheap fix) from being conflated with a missing capability.

z3 verdicts are read from the checked-in sample (regenerate with z3_screen.py
only when the corpus changes). z3 itself is re-run ONLY under
--validate-models (to evaluate oziz's models); the bare gate never calls z3.
"""
from __future__ import annotations
import argparse, json, os, re, signal, subprocess, sys, tempfile, time
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
SAMPLE = HERE / "sample" / "selected.json"
REPO = HERE.parent.parent  # oxiz/ repo root (bench/differential/ -> repo)

VERDICTS = ("sat", "unsat", "unknown")


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


def run_one(cmd, path, timeout, stdin_text=None):
    """Run cmd[+path] (or cmd with stdin_text if given). Returns (dt, status, rc)."""
    t0 = time.perf_counter()
    try:
        if stdin_text is not None:
            p = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, text=True, start_new_session=True)
        else:
            p = subprocess.Popen(cmd + [str(path)], stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, text=True, start_new_session=True)
        try:
            out, err = p.communicate(input=stdin_text, timeout=timeout + 1.0)
        except subprocess.TimeoutExpired:
            try: os.killpg(p.pid, signal.SIGKILL)
            except ProcessLookupError: pass
            try: p.communicate(timeout=1)
            except Exception: pass
            return timeout, "timeout", 124
        dt = time.perf_counter() - t0
        text = (out or "") + "\n" + (err or "")
        return dt, parse_status(text, p.returncode, dt, timeout), p.returncode
    except Exception as e:
        return time.perf_counter() - t0, f"ERR:{e}", -1


# ───────────────────────── family key ──────────────────────────────────────
# SMT-LIB layout: smt-lib/non-incremental/<LOGIC>/<FAMILY>/.../<file>.smt2
# The "family" is the benchmark series right under the logic dir, so e.g.
# QF_ANIA/20211213-GrandProduct-Ozdemir/{sound,unsound}/* collapse to one
# family — which is exactly what lets the neighbour check catch the ANIA
# over-eager-sat pattern (err on sound/*, score on unsound/*).
def family_key(logic: str, path: str) -> str:
    needle = "/" + logic + "/"
    i = path.find(needle)
    if i < 0:
        # fall back: parent directory
        return f"{logic}/{Path(path).parent.name}"
    after = path[i + len(needle):]
    return f"{logic}/{after.split('/')[0]}"


# ─────────────────────── model validation (z3-based) ───────────────────────
def build_model_probe_script(orig_text: str) -> str:
    """Strip trailing (check-sat)/(exit) so our appended (check-sat)(get-model)
    are actually parsed (execute_script breaks on Command::Exit). Returns a
    script that re-checks then requests the model."""
    t = orig_text
    i = t.rfind("(check-sat)")
    if i != -1:
        t = t[:i]
    return t + "\n(check-sat)\n(get-model)\n"


_DEF_RE = re.compile(
    r"\(define-fun\s+(\S+)\s*\(([^)]*)\)\s+(\S+)\s+(.*?)\)\s*(?=\(define-fun|\Z)",
    re.S,
)


def parse_define_funs(model_text: str):
    """Return list of (name, args, sort, val) for each define-fun in the model."""
    return [(m.group(1), m.group(2).strip(), m.group(3), m.group(4).strip())
            for m in _DEF_RE.finditer(model_text)]


def build_z3_consistency_script(orig_text: str, defs) -> str:
    """Build (asserts ∧ model) for z3. For each nullary define-fun we pin the
    constant to its value via (assert (= name val)); unknown idents in val
    (e.g. oziz's @uc_I_N uninterpreted witnesses) are declared. Function
    models are SKIPPED — this can only make the check *lenient* (more 'sat'),
    never a false 'unsat', because (G_constants ∧ F) unsat already implies no
    function extension rescues F, hence oziz's claimed model can't satisfy F.
    """
    head = orig_text
    i = head.rfind("(check-sat)")
    if i != -1:
        head = head[:i]
    # also drop a trailing (exit) if it survived (no (check-sat) after it)
    declared = set(re.findall(r"declare-(?:const|fun)\s+(\S+)", orig_text))
    extra_decl = set()
    pins = []
    skipped_fn = 0
    for name, args, sort, val in defs:
        if args:
            skipped_fn += 1
            continue
        for ident in re.findall(r"[@!][A-Za-z0-9_]+", val):
            if ident not in declared and ident not in extra_decl:
                extra_decl.add(ident)
                head += f"\n(declare-const {ident} {sort})"
        pins.append(f"(assert (= {name} {val}))")
    body = head + "\n" + "\n".join(pins) + f"\n; skipped {skipped_fn} function model(s)\n(check-sat)\n"
    return body


def z3_eval_model(z3_bin, script, timeout):
    """Return 'sat' | 'unsat' | 'unknown' | 'ERR:...' from z3 -in."""
    try:
        r = subprocess.run([z3_bin, "-in"], input=script, capture_output=True,
                           text=True, timeout=timeout + 1.0)
    except subprocess.TimeoutExpired:
        return "unknown"   # subprocess.run already reaped the child
    except Exception as e:
        return f"ERR:{e}"
    for line in reversed((r.stdout or "").splitlines()):
        s = line.strip().lower()
        if s in VERDICTS:
            return s
    return "ERR:" + (r.stdout or r.stderr or "").strip().replace("\n", " ")[:160]


def validate_model(z3_bin, oxiz_bin, oxiz_extra, path, orig_text, timeout):
    """Re-run oziz to emit a model, then ask z3 if asserts∧model is consistent.
    Returns (model_status, detail):
      model_status ∈ {valid, invalid, emit_failed, z3_err}
    """
    probe = build_model_probe_script(orig_text)
    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as tf:
        tf.write(probe)
        tmp = tf.name
    cmd = [oxiz_bin] + (oxiz_extra.split() if oxiz_extra else [])
    t0 = time.perf_counter()
    try:
        r = subprocess.run(cmd + [tmp], capture_output=True, text=True,
                           timeout=timeout + 1.0)
        out = r.stdout or ""
        dt2 = time.perf_counter() - t0
        st2 = parse_status(out + "\n" + (r.stderr or ""), r.returncode, dt2, timeout)
    except subprocess.TimeoutExpired:
        try: os.unlink(tmp)
        except OSError: pass
        return "emit_failed", f"model-run timeout (>{timeout:.0f}s)"
    except Exception as e:
        try: os.unlink(tmp)
        except OSError: pass
        return "emit_failed", f"model-run err: {e}"
    try: os.unlink(tmp)
    except OSError: pass
    # The model-run's own verdict (should be sat; non-determinism → emit_failed)
    if st2 != "sat":
        return "emit_failed", f"model-run verdict={st2} (dt={dt2:.2f}s)"
    # model text = everything after the last standalone 'sat' verdict line
    parts = out.split("\n")
    last_sat = max((idx for idx, ln in enumerate(parts) if ln.strip() == "sat"),
                   default=-1)
    model_text = "\n".join(parts[last_sat + 1:])
    defs = parse_define_funs(model_text)
    if not defs:
        return "emit_failed", "no define-fun in emitted model"
    script = build_z3_consistency_script(orig_text, defs)
    zr = z3_eval_model(z3_bin, script, timeout)
    if zr == "unsat":
        return "invalid", "z3: asserts∧model unsat (model contradicts assertions)"
    if zr == "sat":
        return "valid", f"z3: consistent ({len(defs)} define-fun(s) pinned)"
    if zr == "unknown":
        return "valid", "z3: unknown (treated as consistent — not a bad-model signal)"
    return "z3_err", zr


# ────────────────────────────── main ────────────────────────────────────────
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bin", required=True, help="oxiz binary to test")
    ap.add_argument("--label", default="oxiz", help="label for the results dir")
    ap.add_argument("--timeout", type=float, default=10.0)
    ap.add_argument("--jobs", type=int, default=1)
    ap.add_argument("--out", default=None)
    ap.add_argument("--extra", default="-q", help="extra args to the oxiz binary")
    ap.add_argument("--validate-models", action="store_true",
                    help="z3-based model validation for every sat (needs z3)")
    ap.add_argument("--z3", default="z3", help="z3 binary for --validate-models")
    ap.add_argument("--baseline", default=None,
                    help="path to a baseline summary.json; exit 2 on regression")
    ap.add_argument("--limit", type=int, default=0,
                    help="run only the first N instances (0 = all; for fast slicing)")
    ap.add_argument("--logic", default="",
                    help="comma-separated logic filter, e.g. QF_ANIA,QF_BV (empty = all)")
    args = ap.parse_args()

    sample = json.loads(SAMPLE.read_text())
    insts = sample["instances"]
    if args.logic:
        want = {x.strip().upper() for x in args.logic.split(",") if x.strip()}
        insts = [it for it in insts if it["logic"].upper() in want]
    if args.limit > 0:
        insts = insts[:args.limit]
    missing_root = next((REPO / it["path"] for it in insts if not (REPO / it["path"]).exists()), None)
    if missing_root is not None:
        sys.exit(f"error: corpus file not present: {missing_root}\n"
                 f"       smt-lib is .gitignore'd benchmark data, not tracked. "
                 f"Fetch the SMT-LIB corpus under smt-lib/ before running (see README.md).")
    outdir = Path(args.out) if args.out else HERE / "results" / args.label
    outdir.mkdir(parents=True, exist_ok=True)

    if args.validate_models:
        z3chk = subprocess.run([args.z3, "--version"], capture_output=True, text=True)
        if z3chk.returncode != 0:
            sys.exit(f"error: --validate-models needs z3 on PATH (--z3={args.z3}), "
                     f"not found: {z3chk.stderr.strip()}")

    cmd = [args.bin] + (args.extra.split() if args.extra else [])
    print(f"# label={args.label} bin={args.bin} timeout={args.timeout}s "
          f"n={len(insts)} validate_models={args.validate_models}", flush=True)
    rows = []
    hdr = f"{'logic':<10} {'file':<40} {'z3':>5} {'oxiz':>6} {'oxiz_s':>8}  model"
    print(hdr); print("-" * len(hdr))
    for i, it in enumerate(insts, 1):
        path = REPO / it["path"]
        name = path.name
        short = name if len(name) <= 40 else name[:37] + "..."
        orig = path.read_text()
        dt, res, rc = run_one(cmd, path, args.timeout)
        gold = it["z3_res"]
        row = {"path": it["path"], "logic": it["logic"],
               "family": family_key(it["logic"], it["path"]),
               "file": name, "z3_res": gold, "z3_s": it["z3_s"],
               "res": res, "s": round(dt, 6), "rc": rc, "model_status": None}
        soundness_bad = res in ("sat", "unsat") and gold in ("sat", "unsat") and res != gold
        row["soundness_bad"] = soundness_bad
        mtag = ""
        if args.validate_models and res == "sat":
            ms, detail = validate_model(args.z3, args.bin, args.extra, path, orig,
                                        min(args.timeout, 10.0))
            row["model_status"] = ms
            row["model_detail"] = detail
            mtag = {"valid": "ok", "invalid": "BAD-MODEL",
                    "emit_failed": "no-model", "z3_err": "z3-err"}.get(ms, ms)
        rows.append(row)
        flag = "  *UNSAFE*" if soundness_bad else ""
        print(f"{it['logic']:<10} {short:<40} {gold:>5} {res:>6} {dt:8.3f}{flag}  {mtag}", flush=True)
        if i % 20 == 0:
            _flush(outdir, rows)

    # family-neighbour analysis (needs all rows)
    fam_bad = defaultdict(bool)   # family -> has any disagreement or invalid-model sat?
    fam_counts = defaultdict(lambda: {"n": 0, "disagree": 0, "sat": 0,
                                      "sat_valid": 0, "sat_invalid": 0})
    for r in rows:
        f = r["family"]; fc = fam_counts[f]; fc["n"] += 1
        if r["res"] in ("sat", "unsat"): fc[r["res"]] = fc.get(r["res"], 0) + 1
        if r["soundness_bad"]: fc["disagree"] += 1
        if r["model_status"] == "invalid": fc["sat_invalid"] += 1
        if r["model_status"] == "valid": fc["sat_valid"] += 1
        if r["soundness_bad"] or r["model_status"] == "invalid":
            fam_bad[f] = True
    for r in rows:
        r["family_suspect"] = fam_bad.get(r["family"], False)

    _flush(outdir, rows)
    unsound = [r for r in rows if r["soundness_bad"]]
    (outdir / "unsound.json").write_text(json.dumps(unsound, indent=2))
    (outdir / "families.json").write_text(json.dumps(fam_counts, indent=2, default=dict))

    summary = _summary(rows, args, fam_counts)
    (outdir / "summary.json").write_text(json.dumps(summary, indent=2))

    _print_summary(summary, unsound, fam_counts, outdir)

    exit_code = 1 if summary["disagree_soundness"] else 0
    if args.baseline:
        reg = _regression(args.baseline, summary, rows)
        if reg:
            print("\n# REGRESSION vs baseline:")
            for line in reg:
                print(f"  {line}")
            exit_code = max(exit_code, 2)
    sys.exit(exit_code)


def _flush(outdir, rows):
    (outdir / "results.jsonl").write_text(
        "\n".join(json.dumps(r, default=str) for r in rows) + "\n")


def _summary(rows, args, fam_counts):
    solved = sum(1 for r in rows if r["res"] in ("sat", "unsat"))
    agree = sum(1 for r in rows if r["res"] == r["z3_res"])
    disagree = sum(1 for r in rows if r["soundness_bad"])
    to = sum(1 for r in rows if r["res"] in ("timeout", "unknown"))
    par2 = sum(r["s"] if r["res"] in ("sat", "unsat") else 2 * args.timeout for r in rows)
    s = {"label": args.label, "n": len(rows), "solved": solved,
         "agree_z3": agree, "disagree_soundness": disagree,
         "timeout_or_unknown": to, "par2": round(par2, 2)}
    # sat-direction trust breakdown (only meaningful with model validation)
    sat_rows = [r for r in rows if r["res"] == "sat"]
    s["sat_total"] = len(sat_rows)
    if args.validate_models:
        sv = sum(1 for r in sat_rows if r["model_status"] == "valid")
        si = sum(1 for r in sat_rows if r["model_status"] == "invalid")
        se = sum(1 for r in sat_rows if r["model_status"] in ("emit_failed", "z3_err"))
        s["sat_model_valid"] = sv
        s["sat_model_invalid"] = si
        s["sat_model_emit_failed"] = se
        # trusted sat = agreeing sat, model valid, and no family disagreement
        trusted = sum(1 for r in sat_rows
                      if r["res"] == r["z3_res"] and r["model_status"] == "valid"
                      and not r["family_suspect"])
        s["sat_family_suspect"] = sum(1 for r in sat_rows if r["family_suspect"])
        s["sat_trusted"] = trusted
        # unsat can never be faked by an over-eager-sat mechanism, so an
        # agreeing unsat is trusted by construction.
        s["unsat_trusted"] = sum(1 for r in rows if r["res"] == "unsat" and r["res"] == r["z3_res"])
        s["trusted_total"] = s["sat_trusted"] + s["unsat_trusted"]
    return s


def _regression(baseline_path, summary, rows):
    bl = json.loads(Path(baseline_path).read_text())
    msgs = []
    if summary["agree_z3"] < bl.get("agree_z3", summary["agree_z3"]):
        msgs.append(f"agree_z3 regressed: {bl.get('agree_z3')} -> {summary['agree_z3']}")
    if summary["disagree_soundness"] > bl.get("disagree_soundness", 0):
        msgs.append(f"disagree_soundness increased: {bl.get('disagree_soundness')} -> {summary['disagree_soundness']}")
    return msgs


def _print_summary(summary, unsound, fam_counts, outdir):
    print("\n# SUMMARY")
    print(f"solved={summary['solved']} agree_z3={summary['agree_z3']} "
          f"disagree(soundness)={summary['disagree_soundness']} "
          f"timeout/unknown={summary['timeout_or_unknown']} par2={summary['par2']:.2f}")
    if "sat_model_valid" in summary:
        print(f"  sat: total={summary['sat_total']} model_valid={summary['sat_model_valid']} "
              f"model_invalid={summary['sat_model_invalid']} emit_failed={summary['sat_model_emit_failed']} "
              f"family_suspect={summary['sat_family_suspect']} sat_trusted={summary['sat_trusted']}")
        print(f"  trusted_total (sat_trusted + unsat_trusted)={summary['trusted_total']}  "
              f"<-- the number to plan ports against")
    if unsound:
        print(f"# {len(unsound)} UNSOUND (oxiz disagrees with z3 on a sat/unsat):")
        for r in unsound:
            print(f"  [{r['logic']}] {r['family']}: {r['file']}: z3={r['z3_res']} oxiz={r['res']}")
    suspect = {f: c for f, c in fam_counts.items() if c["disagree"] or c["sat_invalid"]}
    if suspect:
        print(f"# {len(suspect)} family(ies) with a disagreement or invalid-model sat:")
        for f, c in sorted(suspect.items(), key=lambda kv: -kv[1]["disagree"]):
            print(f"  {f}: n={c['n']} disagree={c['disagree']} "
                  f"sat_invalid={c['sat_invalid']} sat_valid={c['sat_valid']}")
    print(f"# wrote {outdir}")


if __name__ == "__main__":
    main()
