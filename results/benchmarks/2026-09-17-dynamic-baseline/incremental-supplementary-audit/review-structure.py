import json, hashlib
from pathlib import Path
from collections import Counter
p=Path('.work/artifacts/incremental-supplementary-final-audit/main-audit.json')
x=json.loads(p.read_text())
assert set(x['cases'])=={f'{o}-n{n}' for o in ('zfa','mro') for n in (1,10,100)}
expected={f'{r}/{a}' for r in ('km','hermit','jfact','openllet') for a in ('session','fresh')}|{'konclude/fresh'}
counts=Counter(); measured=Counter(); mismatches=[]; comparisons=0; evidence=Counter()
for case,c in x['cases'].items():
 assert c['expected_states']==251
 assert set(c['repetitions'])=={'warmup','0','1','2','3','4'}
 for rep,r in c['repetitions'].items():
  assert set(r['arms'])==expected
  for arm,a in r['arms'].items():
   m=a['measurement']; counts[a['status']]+=1
   if rep!='warmup': measured[a['status']]+=1
   assert m['manifest_sha256']==c['manifest_sha256']
   assert (m['history_timeout_s'],m['state_timeout_s'],m['memcap_mib'])==(7200,240,20480)
   assert m['slurm_array_job']=='51982375'
   assert m['completed_states']==len(a['states'])
   if a['complete']: assert set(a['states'])==set(map(str,range(251))) and not a['issues']
   for s in a['states'].values(): evidence[s['evidence']]+=1
  for arm,a in r['arms'].items():
   for ref in ('hermit/fresh','jfact/fresh'):
    b=r['arms'][ref]
    for rev in a['states'].keys() & b['states'].keys():
     comparisons+=1
     if a['states'][rev]['sha256']!=b['states'][rev]['sha256']:
      mismatches.append([case,rep,arm,ref,rev])
assert dict(counts)==x['summary']['measurement_statuses']
out=dict(audit_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),arms=sum(counts.values()),statuses=dict(counts),measured_statuses=dict(measured),available_state_comparisons=comparisons,mismatches=mismatches,state_evidence=dict(evidence),scope='Structural coverage and digest comparisons only. Raw input/runtime bindings and full-output verification remain pending.')
p.with_name('parent-structural-review.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
