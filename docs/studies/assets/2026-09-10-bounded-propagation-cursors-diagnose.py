"""Offline attribution only. No solver invocation or cost-cell replacement."""
from pathlib import Path
import collections, hashlib, json, math, re, subprocess
ROOT=Path('/media/data/proj/nixie'); CACHE=ROOT/'precompile/f5e75a7'
RAW=CACHE/'benchmark/bounded-propagation-cursors-profile'
identity=json.loads((CACHE/'build-identity.json').read_text())
binary=CACHE/'stats_solve-perf'
assert hashlib.sha256(binary.read_bytes()).hexdigest()==identity['perf_sha256']
d=json.loads((RAW/'profile-diagnosis.json').read_text());q=d['quality']
ranges={'prefix':(0x64100,620),'suffix':(0x64ec0,577),'assignment':(0x640b0,68),'driver':(0x4aff0,5125)}
asm={};listings=[]
for name,(start,size) in ranges.items():
    text=subprocess.check_output(['objdump','-d','-C','-M','intel',f'--start-address={start}',f'--stop-address={start+size}',str(binary)],text=True)
    listings.append('=== '+name+' ===\n'+text)
    for line in text.splitlines():
        m=re.match(r'\s*([0-9a-f]+):\s+(.+)',line)
        if m:asm[int(m[1],16)]=m[2]
(CACHE/'preflight/selected-codegen.txt').write_text('\n'.join(listings))
def label(ip,symbol):
    for name,(start,size) in ranges.items():
        if start<=ip<start+size:return 'BCP '+name
    return symbol
hot=collections.Counter();selfs=collections.Counter();folded=collections.Counter();samples=0
for block in (RAW/'profile-samples.txt').read_text().strip().split('\n\n'):
    lines=block.splitlines();m=re.fullmatch(r'\s*(\d+)\s+(cpu_atom/(?:cycles/uS|instructions/u)):\s*',lines[0]);assert m
    if m[2]!='cpu_atom/cycles/uS':continue
    weight=int(m[1]);frames=[]
    for line in lines[1:]:
        f=re.fullmatch(r'\s*([0-9a-f]+)\s+(.+)',line);assert f
        frames.append((int(f[1],16)-d['load_bias'],f[2]))
    ip,sym=frames[0];hot[ip]+=weight;selfs[label(ip,sym)]+=weight;samples+=1
    root='Captured caller chain' if frames[-1][1]=='_start' else 'Truncated caller chain'
    folded[root+';'+';'.join(label(ip,sym).replace(';',':') for ip,sym in reversed(frames))]+=weight
full=d['sampled_prefix_counters']['cpu_atom/cycles/uS']
assert sum(hot.values())==full and samples==q['samples']
with (RAW/'phases.folded').open('w') as f:
    for stack,weight in sorted(folded.items()):f.write(f'{stack} {weight}\n')
groups={
 'blocker_load_and_exit':[(0x64150,0x6415b),(0x64f07,0x64f12)],
 'deleted_header_load_and_branch':[(0x6416a,0x64170),(0x64f1a,0x64f20)],
 'normalization_and_first_truth':[(0x64184,0x641a3),(0x64f30,0x64f57)],
 'tail_scan':[(0x641a5,0x641de),(0x64f59,0x64f92)],
 'true_tail_publication':[(0x6423e,0x6424e),(0x65046,0x6504d)],
 'unit_call_and_publication':[(0x641f4,0x6423c),(0x64ffc,0x65041)],
 'empty_suffix_copy_call':[(0x65093,0x650a5)],
}
ips={name:[ip for lo,hi in spans for ip in asm if lo<=ip<=hi] for name,spans in groups.items()}
assert len([ip for v in ips.values() for ip in v])==len(set(ip for v in ips.values() for ip in v))
registered=(q['minimum_read_coverage']>=.999 and set(q['sample_cpus'])=={'15'} and q['samples']-q['sample_modes'].get('1',0)>=1000 and q['lost_records']==q['lost_sample_records']==q['throttle_records']==q['unthrottle_records']==q['cumulative_read_lost_sum']==0 and d['unresolved_self_share']<.01)
report={'record_id':'89ad311a4c7c5334','registered_quality_passed':registered,'original_helper_quality_passed':d['quality_passed'],
 'quality_note':'Copied helper additionally requires >=99.9% user-mode sample IPs; this was not a registered gate. Keep original false status; assess the declared <1% unresolved bound separately.',
 'samples':q['samples'],'user_mode_samples':q['sample_modes'].get('2',0),'kernel_mode_samples':q['sample_modes'].get('1',0),'unresolved_self_share':d['unresolved_self_share'],'raw_quality':q,
 'interpretation':'Sampled-IP shares are subject to skid, not isolated miss rates, stall cycles or removable time. There is no paired baseline profile.',
 'source':identity,'self_shares':{k:v/full for k,v in selfs.most_common()},
 'groups':{name:{'self_share':sum(hot[ip] for ip in v)/full,'ips':[hex(ip) for ip in v]} for name,v in ips.items()},
 'hot_bcp_ips':[{'ip':hex(ip),'self_share':v/full,'instruction':asm[ip]} for ip,v in hot.most_common() if ip in asm][:40]}
(RAW/'registered-attribution.json').write_text(json.dumps(report,indent=2)+'\n')
print('REGISTERED QUALITY',registered,'ORIGINAL HELPER',d['quality_passed'])
for name,value in list(report['self_shares'].items())[:14]:print(name,round(100*value,3))
print('GROUPS',json.dumps({k:round(100*v['self_share'],3) for k,v in report['groups'].items()}))
for row in report['hot_bcp_ips'][:12]:print(row)
