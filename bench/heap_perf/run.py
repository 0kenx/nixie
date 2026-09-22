#!/usr/bin/env python3
"""Heap performance suite, independent model checker, and immutable result-store runner."""
import argparse
import collections
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import resource
import signal
import statistics
import subprocess
import sys
import time

if not __debug__:
    raise RuntimeError("heap benchmark validation requires Python assertions (no -O/PYTHONOPTIMIZE)")

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
spec = importlib.util.spec_from_file_location("benchstore", ROOT / "bench/suite/scripts/benchstore.py")
benchstore = importlib.util.module_from_spec(spec)
spec.loader.exec_module(benchstore)
SUITE = "heap-exact-v1"
FAMILIES = ("allocate", "alias", "values", "permutation", "negative")
ARMS = ("nixie", "cvc5-sl", "cvc5-array", "z3-array")


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def generate(family, n):
    assert family in FAMILIES and n >= 2
    if family == "negative":
        heaps = [[(4*j+i, 0) for i in range(4)] for j in range(n)]
        count, literals = 4*n, [(i, False) for i in range(n)]
    else:
        heaps = [[(i, i) for i in range(n)]]
        count, literals = n, [(0, True)]
        if family == "values":
            heaps.append([(i, i + int(i == n-1)) for i in range(n)])
            literals.append((1, True))
        elif family == "permutation":
            heaps.append(list(reversed(heaps[0])))
            literals.append((1, False))
    lines = [f"vars {count}"]
    for heap in heaps:
        lines.append("heap " + str(len(heap)) + " " + " ".join(f"{l} {v}" for l,v in heap))
    if family != "negative":
        lines += [f"bound {i} 1 {n}" for i in range(n)]
    if family == "alias":
        lines.append(f"eq 0 {n-1}")
    lines += [f"assert {i} {int(p)}" for i,p in literals]
    return "\n".join(lines) + "\n"


def parse_case(text):
    lines = text.splitlines()
    head = lines.pop(0).split()
    assert len(head) == 2 and head[0] == "vars"
    case = dict(count=int(head[1]), heaps=[], bounds=[], equalities=[], literals=[])
    for line in lines:
        words = line.split()
        op, nums = words[0], list(map(int, words[1:]))
        if op == "heap":
            assert len(nums) == 1 + 2*nums[0]
            case["heaps"].append(list(zip(nums[1::2],nums[2::2])))
        elif op == "bound":
            assert len(nums) == 3
            case["bounds"].append(nums)
        elif op == "eq":
            assert len(nums) == 2
            case["equalities"].append(nums)
        elif op == "assert":
            assert len(nums) == 2 and nums[1] in (0,1)
            case["literals"].append((nums[0],bool(nums[1])))
        else:
            raise ValueError(f"unsupported instruction {op}")
    assert case["count"] >= 0
    assert all(0 <= i < case["count"] and lo <= hi for i,lo,hi in case["bounds"])
    assert all(0 <= i < case["count"] and 0 <= j < case["count"] for i,j in case["equalities"])
    assert all(0 <= i < len(case["heaps"]) for i,_ in case["literals"])
    for heap in case["heaps"]:
        assert all(0 <= l < case["count"] for l,_ in heap)
    return case


def concrete(heap, values):
    result = {}
    for loc,val in heap:
        loc = values[f"x{loc}"]
        if loc == 0 or loc in result:
            return None
        result[loc] = val
    return result


def validate(case, values, heap):
    assert 0 not in heap
    assert all(f"x{i}" in values for i in range(case["count"]))
    assert all(lo <= values[f"x{i}"] <= hi for i,lo,hi in case["bounds"])
    assert all(values[f"x{i}"] == values[f"x{j}"] for i,j in case["equalities"])
    assert all((concrete(case["heaps"][i],values) == heap) == polarity for i,polarity in case["literals"])


def oracle(family, n, text):
    # Authenticate the complete instance before using the closed-form proof.
    assert text == generate(family,n)
    case = parse_case(text)
    sat = family in ("allocate","negative")
    if sat:
        values = {f"x{i}": i+1 for i in range(case["count"])}
        heap = concrete(case["heaps"][0],values) if family == "allocate" else {i: 0 for i in range(1,6)}
        validate(case,values,heap)
    # alias: two owned cells share an address. values: same heap/function
    # stores both n-1 and n at its last address. permutation: H and not H.
    return "sat" if sat else "unsat"


def smt(case, native, sat):
    lines = ["(set-logic ALL)","(set-option :produce-models true)"]
    if native:
        lines += ["(declare-heap (Int Int))","(assert (= (as sep.nil Int) 0))"]
    else:
        lines += ["(declare-const domain (Array Int Bool))", "(declare-fun data (Int) Int)", "(assert (not (select domain 0)))"]
    lines += [f"(declare-const x{i} Int)" for i in range(case["count"])]
    for i,heap in enumerate(case["heaps"]):
        if native:
            parts = [f"(pto x{l} {v})" for l,v in heap]
            body = "sep.emp" if not parts else parts[0] if len(parts) == 1 else "(sep " + " ".join(parts) + ")"
        else:
            dom = "((as const (Array Int Bool)) false)"
            for l,_ in heap:
                dom = f"(store {dom} x{l} true)"
            parts = [f"(= domain {dom})"]
            parts += [f"(not (= x{l} 0))" for l,_ in heap]
            parts += [f"(not (= x{l} x{r}))" for j,(l,_) in enumerate(heap) for r,_ in heap[:j]]
            parts += [f"(= (data x{l}) {v})" for l,v in heap]
            body = "(and " + " ".join(parts) + ")"
        lines.append(f"(define-fun h{i} () Bool {body})")
    lines += [f"(assert (and (<= {lo} x{i}) (<= x{i} {hi})))" for i,lo,hi in case["bounds"]]
    lines += [f"(assert (= x{i} x{j}))" for i,j in case["equalities"]]
    lines += [f"(assert {'h'+str(i) if p else '(not h'+str(i)+')'})" for i,p in case["literals"]]
    lines += ["(check-sat)"]
    if sat:
        names = [f"x{i}" for i in range(case["count"])]
        if not native:
            names += [f"h{i}" for i in range(len(case["heaps"]))]
        lines += ["(get-value (" + " ".join(names) + "))"]
        if native:
            lines += ["(get-model)"]
    return "\n".join(lines) + "\n"


def sexprs(text):
    roots, stack = [], []
    for token in re.findall(r'\(|\)|"(?:[^"\\]|\\.)*"|[^\s()]+',text):
        if token == "(":
            stack.append([])
        elif token == ")":
            if not stack:
                raise ValueError("unbalanced reference output")
            node = stack.pop()
            (stack[-1] if stack else roots).append(node)
        else:
            (stack[-1] if stack else roots).append(token)
    assert not stack
    return roots


def integer(node):
    if isinstance(node,str):
        return int(node)
    assert len(node) == 2 and node[0] == "-" and isinstance(node[1],str)
    return -int(node[1])


def reference_model(case, output, native):
    roots = sexprs(output)
    pairs = roots[1]
    assert isinstance(pairs,list)
    values = {name: integer(value) for name,value in pairs if name.startswith("x")}
    if native:
        models = [r for r in roots if isinstance(r,list) and r and r[0] == "heap"]
        assert len(models) == 1
        heap, stack = {}, [models[0][1]]
        while stack:
            cell = stack.pop()
            if cell == "sep.emp":
                continue
            assert isinstance(cell,list) and cell
            if cell[0] == "sep":
                stack.extend(cell[1:])
            else:
                assert cell[0] == "pto" and len(cell) == 3
                loc,val = integer(cell[1]),integer(cell[2])
                assert loc not in heap
                heap[loc] = val
    else:
        phases = {int(name[1:]): value == "true" for name,value in pairs if name.startswith("h")}
        assert all(value in ("true","false") for name,value in pairs if name.startswith("h"))
        assert len(phases) == len(case["heaps"])
        selected = next((i for i,p in phases.items() if p),None)
        heap = concrete(case["heaps"][selected],values) if selected is not None else {i+1:0 for i in range(max(map(len,case["heaps"]),default=0)+1)}
        assert heap is not None
        assert all((concrete(h,values) == heap) == phases[i] for i,h in enumerate(case["heaps"]))
    validate(case,values,heap)
    return heap


def worker(args):
    text = args.case.read_text()
    family,n = args.case.stem.rsplit("-",1)
    expected = oracle(family,int(n),text)
    case = parse_case(text)
    if args.arm == "nixie":
        cmd = [args.driver,str(args.case),str(args.seed),args.phase]
        payload = None
    else:
        payload = smt(case,args.arm == "cvc5-sl",expected == "sat")
        cmd = ([args.z3,"-in",f"smt.random_seed={args.seed}","rlimit=2000000"] if args.arm == "z3-array" else
               [args.cvc5,"--lang=smt2","--arrays-exp",f"--seed={args.seed}",f"--sat-random-seed={args.seed}","--rlimit=2000000"])
    process = subprocess.run(cmd,input=payload,text=True,capture_output=True)
    result = dict(returncode=process.returncode, stdout=process.stdout, stderr=process.stderr,
                  solver_peak_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                  encoded_bytes=len(payload.encode()) if payload else len(text.encode()))
    answers = re.findall(r"^(sat|unsat|unknown)$",process.stdout,re.M)
    if len(answers) != 1:
        raise ValueError(f"missing/extra solver verdict: {result}")
    answer = answers[0]
    result.update(answer=answer,verified=False)
    if answer != "unknown":
        assert process.returncode == 0, result
        assert answer == expected, f"WRONG ANSWER: {args.case}: {result}"
        if answer == "sat":
            if args.arm == "nixie":
                values,heap = {},{}
                for line in process.stdout.splitlines():
                    parts = line.split()
                    if parts[0] == "var": values[parts[1]] = int(parts[2])
                    elif parts[0] == "cell":
                        assert int(parts[1]) not in heap
                        heap[int(parts[1])] = int(parts[2])
                validate(case,values,heap)
            else:
                reference_model(case,process.stdout,args.arm == "cvc5-sl")
        result["verified"] = True
    if args.arm == "nixie":
        reason = re.search(r"^reason (.*)$",process.stdout,re.M)
        if reason: result["reason_unknown"] = reason.group(1)
        for label,keys in [("sizes",("heaplets","original_nodes","backend_terms")),("search",("conflicts","decisions","propagations"))]:
            match = re.search(rf"^{label} (\d+) (\d+) (\d+)$",process.stdout,re.M)
            assert match
            result.update(zip(keys,map(int,match.groups())))
    print(json.dumps(result))


def perf_count(path, unreached_region=False):
    values = []
    for line in path.read_text().splitlines():
        parts = line.split(",")
        if len(parts) > 4 and "instructions" in parts[2] and parts[0].strip().isdigit():
            assert float(parts[4].strip().rstrip("%")) >= 99.9, "multiplexed PMU counter"
            values.append(int(parts[0]))
    if not values and unreached_region and "<not counted>" in path.read_text():
        return None
    assert len(values) == 1 and values[0] > 0, path.read_text()
    return values[0]


def run(args):
    sha = subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip()
    assert not subprocess.check_output(["git","status","--porcelain","--untracked-files=no"],cwd=ROOT,text=True), "commit the harness before measuring"
    cache = args.store / sha[:8]
    directory = cache / "benchmark" / SUITE
    directory.mkdir(parents=True,exist_ok=True)
    versions = {"python":platform.python_version(),"perf":subprocess.check_output(["perf","--version"],text=True).strip(),"z3":subprocess.check_output([args.z3,"--version"],text=True).strip(),
                "cvc5":subprocess.check_output([args.cvc5,"--version"],text=True).splitlines()[0]}
    cases = []
    for family in FAMILIES:
        for n in (2,4,8,16):
            path = directory / f"{family}-{n}.heap"
            text = generate(family,n)
            if path.exists(): assert path.read_text() == text
            else: path.write_text(text)
            cases.append((path,family,n,oracle(family,n,text)))
    manifest = dict(suite=SUITE,sha=sha,versions=versions,seeds=list(range(10)),
                    cases=[p.name for p,_,_,_ in cases],arms=list(ARMS),phases=["encode","solve","validate"],phase_sizes=[2,16])
    mp = directory / "manifest.json"
    if mp.exists(): assert json.loads(mp.read_text()) == manifest
    else: mp.write_text(json.dumps(manifest,indent=2)+"\n")
    all_records = []
    for case,family,n,expected in cases:
        arms = [(a,"total") for a in ARMS]
        if n in (2,16): arms += [("nixie",p) for p in ("encode","solve","validate") if p != "validate" or expected == "sat"]
        for seed in range(10):
            # Rotate arm order independently of outcomes; no hindsight choice.
            ordered = arms[seed % len(arms):] + arms[:seed % len(arms)]
            for arm,phase in ordered:
                binary = args.driver if arm == "nixie" else args.z3 if arm == "z3-array" else args.cvc5
                flags = dict(arm=arm,phase=phase,cpu=args.cpu,cap_s=20,pythonhashseed=0,nixie_environment="cleared",pmu="instructions:u",harness_sha256=digest(__file__),
                             driver_sha256=digest(args.driver),solver_sha256=digest(binary),
                             cvc5_arrays_exp=True,cvc5_rlimit=2000000,z3_rlimit=2000000,nixie_conflicts=10000,nixie_decisions=100000)
                rec = dict(schema=benchstore.SCHEMA,created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),suite=SUITE,
                    host=dict(id=platform.node(),cpu=next(line.split(":",1)[1].strip() for line in Path("/proc/cpuinfo").read_text().splitlines() if line.startswith("model name"))+f" cpu{args.cpu}",os=platform.platform()),
                    git=dict(sha_long=sha,sha_short=sha[:8],dirty=False),binary=dict(path=binary,sha256=digest(binary)),
                    instance=dict(name=case.stem,sha256=digest(case),family=family,sat_expected=expected == "sat"),
                    config=dict(id=arm+"-"+phase,flags=flags,features=["default"],cmdline=[]),seed=seed,
                    arm=dict(role="treatment" if arm == "nixie" else "reference"))
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
                    perf = ["taskset","-c",str(args.cpu),"perf","stat","-x,","-o",str(raw.with_suffix(".perf")),"-e","instructions:u"]
                    fifos = []
                    if phase != "total":
                        fifos = [raw.with_suffix(".ctl"),raw.with_suffix(".ack")]
                        for fifo in fifos: os.mkfifo(fifo)
                        env.update(HEAP_PERF_CONTROL=str(fifos[0]),HEAP_PERF_ACK=str(fifos[1]))
                        perf += ["-D","-1","--control",f"fifo:{fifos[0]},{fifos[1]}"]
                    command = perf + ["--",sys.executable,str(Path(__file__).resolve()),"worker","--case",str(case),"--arm",arm,
                        "--phase",phase,"--seed",str(seed),"--driver",args.driver,"--cvc5",args.cvc5,"--z3",args.z3]
                    raw.with_suffix(".command.json").write_text(json.dumps(command))
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


def summarize(records,directory):
    groups = collections.defaultdict(list)
    for rec in records: groups[(rec["instance"]["name"],rec["config"]["id"])].append(rec)
    rows = []
    for (case,arm), group in sorted(groups.items()):
        solved = [r for r in group if r["verdict"]["answer"] != "unknown"]
        costs = [r["metrics"]["primary"]["value"] for r in solved]
        rss = [r["metrics"]["secondary"]["solver_peak_rss_kib"] for r in solved]
        rows.append(dict(case=case,arm=arm,runs=len(group),solved=len(solved),instructions_median=statistics.median(costs) if costs else None,
            instructions_min=min(costs) if costs else None,instructions_max=max(costs) if costs else None,rss_kib_median=statistics.median(rss) if rss else None,
            backend_terms=solved[0]["metrics"]["secondary"].get("backend_terms") if solved else None))
    (directory/"summary.json").write_text(json.dumps(rows,indent=2)+"\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode",choices=("run","worker"))
    parser.add_argument("--driver",required=True)
    parser.add_argument("--cvc5",required=True)
    parser.add_argument("--z3",required=True)
    parser.add_argument("--store",type=Path,default=ROOT/"precompile")
    parser.add_argument("--cpu",type=int,default=2)
    parser.add_argument("--case",type=Path)
    parser.add_argument("--arm",choices=ARMS)
    parser.add_argument("--seed",type=int,default=0)
    parser.add_argument("--phase",choices=("total","encode","solve","validate"),default="total")
    args = parser.parse_args()
    if args.mode == "worker": worker(args)
    else: run(args)


if __name__ == "__main__":
    main()
