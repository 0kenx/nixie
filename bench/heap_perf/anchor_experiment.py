#!/usr/bin/env python3
"""Heap anchor experiment; see the heap anchor reduction preregistration.

The original run.py worker remains unchanged so measured Python work and the
independent validator are identical between driver revisions. Existing cells
are reused; interrupted cells fail closed rather than being rerun.
"""
import argparse
import datetime
import json
import os
from pathlib import Path
import platform
import signal
import subprocess
import sys
import time

from run import ROOT, benchstore, digest, perf_count, summarize
from anchor_cases import CASES, generate, oracle

SUITE = "heap-anchor-reduction-v1"
BASELINE_SHA = "6925082367c2d34390616dd7b6efa4ed5f1f87a3"
ARMS = ("baseline", "redundant", "reduced")
SEEDS = list(range(10)) + [102]
WORKER = Path(__file__).resolve().with_name("anchor_worker.py")

def run(args):
    sha = subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip()
    assert not subprocess.check_output(["git","status","--porcelain","--untracked-files=no"],cwd=ROOT,text=True), "commit the harness before measuring"
    cache = args.store / sha[:8]
    directory = cache / "benchmark" / SUITE
    directory.mkdir(parents=True,exist_ok=True)
    versions = {"rustc":subprocess.check_output(["rustc","--version"],text=True).strip(),"python":platform.python_version(),"perf":subprocess.check_output(["perf","--version"],text=True).strip(),"z3":subprocess.check_output([args.z3,"--version"],text=True).strip(),
                "cvc5":subprocess.check_output([args.cvc5,"--version"],text=True).splitlines()[0]}
    cases = []
    for family, n in CASES:
        path = directory / f"{family}-{n}.heap"
        text = generate(family,n)
        if path.exists(): assert path.read_text() == text
        else: path.write_text(text)
        cases.append((path,family,n,oracle(family,n,text)))
    manifest = dict(suite=SUITE,sha=sha,versions=versions,seeds=SEEDS,
                    cases=[p.name for p,_,_,_ in cases],arms=list(ARMS),phases=["total"],baseline_sha=BASELINE_SHA,worker_sha256=digest(WORKER),
                    drivers={a: dict(path=args.baseline if a == "baseline" else args.driver,
                        sha256=digest(args.baseline if a == "baseline" else args.driver)) for a in ARMS})
    mp = directory / "manifest.json"
    if mp.exists(): assert json.loads(mp.read_text()) == manifest
    else: mp.write_text(json.dumps(manifest,indent=2)+"\n")
    all_records = []
    for case,family,n,expected in cases:
        arms = [(a,"total") for a in ARMS]
        for seed in SEEDS:
            # Rotate arm order independently of outcomes; no hindsight choice.
            ordered = arms[seed % len(arms):] + arms[:seed % len(arms)]
            for arm,phase in ordered:
                binary = args.baseline if arm == "baseline" else args.driver
                flags = dict(arm=arm,phase=phase,cpu=args.cpu,cap_s=20,pythonhashseed=0,nixie_environment="cleared",pmu="instructions:u",harness_sha256=digest(__file__),
                             driver_sha256=digest(binary),solver_sha256=digest(binary),worker_sha256=digest(WORKER),
                             anchor_redundancy=arm == "redundant",baseline_sha=BASELINE_SHA,
                             checker_sha256=digest(WORKER.with_name("run.py")),cases_sha256=digest(WORKER.with_name("anchor_cases.py")),
                             build_profile="release",build_strip="none",build_incremental=False,
                             definition_simplification=True,nixie_conflicts=10000,nixie_decisions=100000)
                rec = dict(schema=benchstore.SCHEMA,created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),suite=SUITE,
                    host=dict(id=platform.node(),cpu=next(line.split(":",1)[1].strip() for line in Path("/proc/cpuinfo").read_text().splitlines() if line.startswith("model name"))+f" cpu{args.cpu}",os=platform.platform()),
                    git=dict(sha_long=sha,sha_short=sha[:8],dirty=False),binary=dict(path=binary,sha256=digest(binary)),
                    instance=dict(name=case.stem,sha256=digest(case),family=family,sat_expected=expected == "sat"),
                    config=dict(id=arm+"-"+phase,flags=flags,features=["default"],cmdline=[]),seed=seed,
                    arm=dict(role="treatment" if arm == "reduced" else "null" if arm == "redundant" else "baseline"))
                rec["config_hash"] = benchstore.canonical_flags(flags)
                destination = benchstore.record_path(args.store,rec)
                if destination.exists():
                    prior = benchstore.validate(json.loads(destination.read_text()))
                    assert benchstore.canonical_join_key(prior) == benchstore.canonical_join_key(rec)
                    all_records.append(prior)
                    continue
                raw = directory / f"{case.stem}-{arm}-{phase}-{seed}-{benchstore.record_id(rec)}"
                result_file = raw.with_suffix(".result.json")
                if result_file.exists():
                    result = json.loads(result_file.read_text())
                else:
                    assert not raw.with_suffix(".command.json").exists(), f"interrupted cell retained at {raw}; investigate, do not rerun"
                    env = {k:v for k,v in os.environ.items() if not k.startswith(("NIXIE_","HEAP_PERF_"))}
                    env["PYTHONHASHSEED"] = "0"
                    env["HEAP_PERF_ANCHOR_REDUNDANCY"] = "1" if arm == "redundant" else "0"
                    perf = ["taskset","-c",str(args.cpu),"perf","stat","-x,","-o",str(raw.with_suffix(".perf")),"-e","instructions:u"]
                    fifos = []
                    if phase != "total":
                        fifos = [raw.with_suffix(".ctl"),raw.with_suffix(".ack")]
                        for fifo in fifos: os.mkfifo(fifo)
                        env.update(HEAP_PERF_CONTROL=str(fifos[0]),HEAP_PERF_ACK=str(fifos[1]))
                        perf += ["-D","-1","--control",f"fifo:{fifos[0]},{fifos[1]}"]
                    command = perf + ["--",sys.executable,str(WORKER),"worker","--case",str(case),"--arm","nixie",
                        "--phase",phase,"--seed",str(seed),"--driver",binary,"--cvc5",args.cvc5,"--z3",args.z3]
                    raw.with_suffix(".command.json").write_text(json.dumps(dict(command=command,
                        environment={k:env[k] for k in ("PYTHONHASHSEED", "HEAP_PERF_ANCHOR_REDUNDANCY")})))
                    load_before = os.getloadavg()
                    start = time.monotonic()
                    with raw.with_suffix(".stdout").open("x") as out, raw.with_suffix(".stderr").open("x") as err:
                        process = subprocess.Popen(command,stdout=out,stderr=err,env=env,start_new_session=True)
                        timeout = False
                        try: status = process.wait(timeout=20)
                        except subprocess.TimeoutExpired:
                            timeout = True
                            os.killpg(process.pid,signal.SIGINT)
                            try: status = process.wait(timeout=3)
                            except subprocess.TimeoutExpired:
                                os.killpg(process.pid,signal.SIGKILL); status = process.wait()
                    for fifo in fifos: fifo.unlink()
                    elapsed = time.monotonic()-start
                    if timeout:
                        payload = dict(answer="unknown",verified=False,timeout=True)
                    else:
                        assert status == 0, raw.with_suffix(".stderr").read_text()
                        payload = json.loads(raw.with_suffix(".stdout").read_text())
                    payload["system_loadavg_before"] = load_before
                    payload["system_loadavg_after"] = os.getloadavg()
                    count = perf_count(raw.with_suffix(".perf"),timeout and phase in ("solve","validate"))
                    if count is None: payload["region_unmeasured"] = True
                    result = dict(instructions=count if count is not None else 0,wall_clock_s=elapsed,payload=payload,command=command)
                    result_file.write_text(json.dumps(result,indent=2)+"\n")
                payload = result["payload"]
                rec["config"]["cmdline"] = result["command"]
                rec["metrics"] = dict(primary=dict(name="unmeasured_region" if payload.get("region_unmeasured") else "instructions:u" if phase == "total" else "region_instructions:u",value=result["instructions"]),
                    secondary={k:v for k,v in payload.items() if k not in ("stdout","stderr")},wall_clock_s=result["wall_clock_s"],counter_coverage_verified=True)
                rec["verdict"] = dict(answer=payload["answer"],verified_model_or_proof=payload["verified"])
                rec["reference_versions"] = versions
                benchstore.validate(rec)
                rec["record_id"] = benchstore.record_id(rec)
                pending = raw.with_suffix(".record.json")
                pending.write_text(json.dumps(rec,indent=2)+"\n")
                benchstore.cmd_record(argparse.Namespace(record=str(pending),root=str(args.store)))
                pending.unlink()
                all_records.append(rec)
                print(f"{case.stem} {arm} {phase} seed={seed} {payload['answer']} {result['instructions']}",flush=True)
    summarize(all_records,directory)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--driver", required=True)
    parser.add_argument("--baseline", required=True)
    parser.add_argument("--cvc5", required=True)
    parser.add_argument("--z3", required=True)
    parser.add_argument("--store", type=Path, default=ROOT / "precompile")
    parser.add_argument("--cpu", type=int, default=2)
    run(parser.parse_args())


if __name__ == "__main__":
    main()
