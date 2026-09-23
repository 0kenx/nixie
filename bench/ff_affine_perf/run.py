#!/usr/bin/env python3
"""Immutable instruction measurements, including reuse of exact legacy invocations."""
import argparse
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import subprocess
import tempfile
import time
import workload

HERE = Path(__file__).resolve().parent
sha256 = lambda data: hashlib.sha256(data).hexdigest()
spec = importlib.util.spec_from_file_location('benchstore', HERE.parent/'suite/scripts/benchstore.py')
store = importlib.util.module_from_spec(spec)
spec.loader.exec_module(store)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('binary', type=Path)
    p.add_argument('--sha', required=True)
    p.add_argument('--role', choices=['baseline','treatment','reference'], required=True)
    p.add_argument('--root', type=Path, required=True)
    p.add_argument('--first-seed', type=int, default=0)
    p.add_argument('--seeds', type=int, default=10)
    a = p.parse_args()
    z3 = a.role == 'reference'
    binary = a.binary.resolve()
    binary_hash = sha256(binary.read_bytes())
    flags = {'harness_sha256': sha256(Path(__file__).read_bytes()),
             'workload_sha256': sha256((HERE/'workload.py').read_bytes()),
             'legacy_sha256': sha256(Path(workload.legacy.__file__).read_bytes()),
             'encoding_sha256': sha256(Path(workload.reference.__file__).read_bytes()),
             'cpu': 0, 'counter': 'instructions:u', 'cap_seconds':120,
             'build': 'reference-z3' if z3 else 'workspace-release-default'}
    if z3:
        version = subprocess.check_output([str(binary),'--version'],text=True).strip()
        assert version == workload.reference.VERSION, version
        flags['z3_version'] = version
        flags['seed_parameters'] = ['sat.random_seed','smt.random_seed']
    host = platform.node()
    outdir = a.root/a.sha/'benchmark'/('ff-affine-reference-raw' if z3 else 'ff-affine-raw')
    outdir.mkdir(parents=True,exist_ok=True)
    tasks = [(case,seed,*workload.generate(case,seed,z3)) for case in workload.CASES for seed in range(a.first_seed,a.first_seed+a.seeds)]
    manifest = {'source':a.sha,'binary_sha256':binary_hash,'flags':flags,'host':host,
                'cells':[{'name':c[0],'seed':s,'sha256':sha256(script.encode())} for c,s,script,_ in tasks]}
    manifest_path = outdir/f'manifest-s{a.first_seed}-{a.seeds}.json'
    encoded = json.dumps(manifest,indent=2)+'\n'
    if manifest_path.exists(): assert manifest_path.read_text()==encoded
    else: manifest_path.write_text(encoded)
    existing = list(store.iter_records(a.root))
    aliases = []
    for case,seed,script,expected in tasks:
        input_hash = sha256(script.encode())
        matches = []
        for path,r in existing:
            f = r['config']['flags']
            if (r['git']['sha_long']==a.sha and r['binary']['sha256']==binary_hash
                and r['host']['id']==host and r['instance']['sha256']==input_hash
                and r['seed']==seed and f.get('cpu')==0 and f.get('counter')=='instructions:u'
                and f.get('cap_seconds')==120 and r['suite'] in ['ff-extension','ff-extension-z3','ff-affine','ff-affine-z3']):
                # Exact legacy CLI invocations are reusable: only off-clock
                # model verification/reporting changed. Preserve their identity.
                matches.append((path,r))
        if len(matches)>1: raise RuntimeError(f'ambiguous existing cell: {case[0]} {seed}')
        if matches:
            path,r = matches[0]
            aliases.append({'name':case[0],'seed':seed,'record':str(path.resolve())})
            print('reuse',case[0],seed,r['record_id'],flush=True)
            continue
        stem = outdir/f'{case[0]}-s{seed}'
        assert not stem.with_suffix('.smt2').exists(), f'unrecorded previous attempt: {stem}'
        stem.with_suffix('.smt2').write_text(script)
        options = [f'sat.random_seed={seed}',f'smt.random_seed={seed}'] if z3 else ['--no-color']
        cmd = ['taskset','-c','0','perf','stat','-x,','-e','instructions:u','--',str(binary),*options,str(stem.with_suffix('.smt2'))]
        start=time.monotonic()
        try:
            result=subprocess.run(cmd,capture_output=True,timeout=120,env={**os.environ, **({} if z3 else {'NIXIE_SAT_SEED':str(seed)})})
        except subprocess.TimeoutExpired as e:
            stem.with_suffix('.out').write_bytes(e.stdout or b'');stem.with_suffix('.err').write_bytes(e.stderr or b'')
            raise RuntimeError(f'censored cell: {stem}') from e
        elapsed=time.monotonic()-start
        stem.with_suffix('.out').write_bytes(result.stdout);stem.with_suffix('.err').write_bytes(result.stderr)
        assert result.returncode==0,result.stderr
        instructions=0
        for line in result.stderr.decode().splitlines():
            parts=line.split(',')
            if len(parts)>4 and 'instructions' in parts[2] and parts[0].isdigit():
                assert float(parts[4])>=99,line
                instructions+=int(parts[0])
        assert instructions>0
        answer,verified=workload.verify(result.stdout.decode(),expected,z3)
        rec={'schema':store.SCHEMA,'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
             'suite':'ff-affine-z3' if z3 else 'ff-affine',
             'host':{'id':host,'cpu':platform.machine(),'os':platform.platform()},
             'git':{'sha_long':a.sha,'sha_short':a.sha,'dirty':False},
             'binary':{'path':str(binary),'sha256':binary_hash},
             'instance':{'name':case[0],'sha256':input_hash,'family':'hard' if case[4] else 'control','sat_expected':(expected.get('legacy',expected)['answer']=='sat')},
             'config':{'id':a.role,'flags':flags,'features':[] if z3 else ['default'],'cmdline':cmd},
             'seed':seed,'arm':{'role':a.role},
             'metrics':{'primary':{'name':'instructions:u','value':instructions},'secondary':{'stdout_sha256':sha256(result.stdout)},'wall_clock_s':elapsed,'counter_coverage_verified':True},
             'verdict':{'answer':answer,'verified_model_or_proof':verified}}
        store.validate(rec)
        with tempfile.NamedTemporaryFile(mode='w',suffix='.json') as f:
            json.dump(rec,f);f.flush();store.cmd_record(argparse.Namespace(record=f.name,root=a.root))
        rec['record_id']=store.record_id(rec)
        path=store.record_path(a.root,rec)
        existing.append((path,rec))
        aliases.append({'name':case[0],'seed':seed,'record':str(path.resolve())})
        print(case[0],seed,answer,instructions,flush=True)
    (outdir/f'aliases-s{a.first_seed}-{a.seeds}.json').write_text(json.dumps(aliases,indent=2)+'\n')


if __name__=='__main__': main()
