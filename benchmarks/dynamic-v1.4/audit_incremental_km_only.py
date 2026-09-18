#!/usr/bin/env python3
"""Audit KM-only measured reruns using the common immutable audit contract.

Independent correctness is established when the comparison renderer joins the
original fresh HermiT/JFact audits by exact manifest, not by this audit alone.
"""
import argparse
from collections import Counter
import csv
from datetime import datetime,timezone
import json
import os
from pathlib import Path
from audit_incremental import inspect_arm,compare,sha

p=argparse.ArgumentParser();p.add_argument('root',type=Path);p.add_argument('--out',type=Path,required=True);p.add_argument('--repetitions',type=int,default=5)
a=p.parse_args();root=a.root.resolve();panel=list(csv.DictReader((root/'incremental-panel.tsv').open(),delimiter='\t'))
report=dict(schema=1,root=str(root),phase='measured',scope='panel',generated_utc=datetime.now(timezone.utc).isoformat(),
 auditor_sha256=sha(Path(__file__)),common_auditor_sha256=sha(root/'audit_incremental.py'),slurm_job=os.environ.get('SLURM_JOB_ID'),
 panel_sha256=sha(root/'incremental-panel.tsv'),deployment_sha256=sha(root/'deployment.json'),
 scope_note='KM-only integrity and own-session/fresh audit; independent correctness requires exact-manifest joins to unchanged peer audits.',cases={})
statuses=Counter();problems=[];complete=0
for row in panel:
 for n in (1,10,100):
  case=row['id']+'-n'+str(n);manifest=root/'inputs'/case/'states.txt'
  if not manifest.exists():report['cases'][case]={'issue':'missing_manifest'};problems.append(case+':missing_manifest');continue
  expected=len(manifest.read_text().splitlines());c=dict(expected_states=expected,manifest_sha256=sha(manifest),repetitions={});report['cases'][case]=c
  for rep in ['warmup']+[str(i) for i in range(a.repetitions)]:
   r=dict(arms={},own_session_fresh={},cross_reference={});c['repetitions'][rep]=r
   for arm in ('session','fresh'):
    directory=root/'measured'/case/'km'/('warmup' if rep=='warmup' else 'rep-'+rep)/arm
    item=inspect_arm(directory,manifest,expected,'km',arm,None);r['arms']['km/'+arm]=item
    statuses[item['status']]+=1;complete+=int(item['complete'])
    if item['issues']:problems.append(case+'/'+rep+'/'+arm+':'+','.join(item['issues']))
   r['own_session_fresh']['km']=compare(r['arms']['km/session'],r['arms']['km/fresh'],expected)
   if r['own_session_fresh']['km']['mismatch_revisions']:problems.append(case+'/'+rep+':own_session_fresh_mismatch')
report['summary']=dict(expected_arms=len(panel)*3*2*(a.repetitions+1),complete_arms=complete,measurement_statuses=dict(statuses),issues=problems,full_scope_verified=False)
a.out.with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
a.out.with_suffix('.md').write_text('# KM-only measured audit\n\nIndependent correctness requires unchanged peer audits.\n\n'+json.dumps(report['summary'],indent=2)+'\n')
print(json.dumps(report['summary'],sort_keys=True))
