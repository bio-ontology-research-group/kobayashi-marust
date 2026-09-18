#!/usr/bin/env python3
"""Isolated full-history check for one completed case, not a matrix result."""
import argparse
from datetime import datetime,timezone
import json
import os
from pathlib import Path
from audit_incremental import inspect_arm,compare,sha

p=argparse.ArgumentParser();p.add_argument('--baseline',type=Path,required=True);p.add_argument('--candidate',type=Path,required=True);p.add_argument('--case',required=True);p.add_argument('--out',type=Path,required=True)
a=p.parse_args();manifest=a.baseline/'inputs'/a.case/'states.txt'
assert sha(manifest)==sha(a.candidate/'inputs'/a.case/'states.txt')
expected=len(manifest.read_text().splitlines());assert expected==251
report=dict(schema=1,scope='one completed real case, all warmup plus five measured repetitions; not fullmatrix or release completion',
 generated_utc=datetime.now(timezone.utc).isoformat(),slurm_job=os.environ.get('SLURM_JOB_ID'),host=os.uname().nodename,
 auditor_sha256=sha(Path(__file__)),common_auditor_sha256=sha(Path(__file__).with_name('audit_incremental.py')),
 input_manifest_sha256=sha(manifest),snapshot_manifest_sha256=sha(a.baseline/'inputs'/a.case/'SHA256SUMS'),
 snapshot_verification_log_sha256=sha(Path('input-verified.log')),
 case=a.case,expected_states=expected,repetitions={},pass_all=True)
for rep in ['warmup']+[str(i) for i in range(5)]:
 folder='warmup' if rep=='warmup' else 'rep-'+rep
 r=dict(arms={},comparisons={});report['repetitions'][rep]=r
 for label,root,reasoner,arm in [('hermit/fresh',a.baseline,'hermit','fresh'),('jfact/fresh',a.baseline,'jfact','fresh'),('km/session',a.candidate,'km','session'),('km/fresh',a.candidate,'km','fresh')]:
  directory=root/'measured'/a.case/reasoner/folder/arm
  r['arms'][label]=inspect_arm(directory,manifest,expected,reasoner,arm,None)
  report['pass_all']=report['pass_all'] and r['arms'][label]['complete']
 for left,right in [('hermit/fresh','jfact/fresh'),('km/session','hermit/fresh'),('km/fresh','hermit/fresh'),('km/session','km/fresh')]:
  result=compare(r['arms'][left],r['arms'][right],expected);r['comparisons'][left+' vs '+right]=result
  report['pass_all']=report['pass_all'] and result['full_agreement']
 a.out.with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
summary=dict(case=a.case,pass_all=report['pass_all'],histories=24,states_per_history=251,
 repetitions_including_warmup=6,comparisons=24,reference_pair='fresh HermiT and JFact',scope=report['scope'])
a.out.with_suffix('.md').write_text('# Completed-case incremental audit\n\n'+json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,sort_keys=True))
if report['pass_all']:Path('PASS').write_text(json.dumps(summary,sort_keys=True)+'\n')
else:raise SystemExit(1)
