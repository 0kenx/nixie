#!/usr/bin/env python3
"""Join immutable baseline/candidate/Z3 cells; Unknown is never a solved match."""
import argparse
from collections import Counter
import csv
import json
import math
from pathlib import Path
import statistics
import workload

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('root',type=Path)
p.add_argument('candidate')
p.add_argument('--baseline',default='260c0728b00fe13f012e8f067e8167392718aa43')
p.add_argument('--csv',type=Path,required=True)
a=p.parse_args()


def load(sha,reference=False):
    folder=a.root/sha/'benchmark'/('ff-affine-reference-raw' if reference else 'ff-affine-raw')
    result={}
    for first in [0,10]:
        for alias in json.loads((folder/f'aliases-s{first}-10.json').read_text()):
            key=(alias['name'],alias['seed'])
            assert key not in result
            record=json.loads(Path(alias['record']).read_text())
            case=next(c for c in workload.CASES if c[0]==key[0])
            script,_=workload.generate(case,key[1],reference)
            assert workload.legacy.sha256(script.encode())==record['instance']['sha256']
            assert record['seed']==key[1] and record['git']['sha_long']==sha
            assert record['metrics']['counter_coverage_verified']
            result[key]=record
    return result


base=load(a.baseline);candidate=load(a.candidate);z3=load(workload.reference.Z3_SHA,True)
assert base.keys()==candidate.keys()==z3.keys() and len(base)==20*len(workload.CASES)
geo=lambda values: math.exp(statistics.mean(map(math.log,values)))
rows=[];passed=True
for label,first in [('initial',0),('fresh',10)]:
    hard_baseline=[];hard_z3=[]
    for case in workload.CASES:
        name=case[0]
        triples=[(base[name,s],candidate[name,s],z3[name,s]) for s in range(first,first+10)]
        costs=[[],[],[]];answers=[[],[],[]];paired=[];reference=[]
        for b,t,z in triples:
            assert b['host']==t['host']==z['host']
            assert b['instance']['sha256']==t['instance']['sha256']
            bv,tv,zv=[r['verdict']['answer'] for r in [b,t,z]]
            assert bv=='unknown' or tv==bv, f'lost/changed decisive answer: {name}'
            assert tv=='unknown' or zv=='unknown' or tv==zv, f'wrong answer: {name}'
            for i,r in enumerate([b,t,z]):
                costs[i].append(r['metrics']['primary']['value']);answers[i].append(r['verdict']['answer'])
            if bv!='unknown' and tv!='unknown': paired.append(costs[1][-1]/costs[0][-1])
            if tv!='unknown' and zv!='unknown': reference.append(costs[1][-1]/costs[2][-1])
        row={'seed_set':label,'instance':name,'hard':case[4]}
        for i,arm in enumerate(['baseline','candidate','z3']):
            row.update({arm+'_min':min(costs[i]),arm+'_median':statistics.median(costs[i]),arm+'_max':max(costs[i]),arm+'_verdicts':str(dict(Counter(answers[i])))})
        row['candidate_over_baseline_solved']=geo(paired) if paired else ''
        row['candidate_over_z3_solved']=geo(reference) if reference else ''
        rows.append(row)
        print(label,name,row['candidate_over_baseline_solved'],row['candidate_over_z3_solved'],row['candidate_verdicts'])
        if case[4]:
            hard_baseline.extend(paired);hard_z3.extend(reference)
            passed &= 'unknown' not in answers[1]
        else:
            passed &= len(paired)==10 and geo(paired)<=1.05
    print(label,'hard solved ratios:',geo(hard_baseline),geo(hard_z3))
    passed &= geo(hard_baseline)<=0.25 and geo(hard_z3)<=1
with a.csv.open('w') as f:
    writer=csv.DictWriter(f,fieldnames=rows[0].keys(),lineterminator='\n');writer.writeheader();writer.writerows(rows)
for arm,records in [('baseline',base),('candidate',candidate),('z3',z3)]:
    print(arm,dict(Counter(r['verdict']['answer'] for r in records.values())))
print('PREREGISTERED GATE:', 'PASS' if passed else 'FAIL')
if not passed: raise SystemExit(1)
