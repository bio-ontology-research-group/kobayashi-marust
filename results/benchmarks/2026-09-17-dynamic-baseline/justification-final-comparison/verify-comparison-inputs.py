from pathlib import Path
import csv,json,hashlib,tarfile
root=Path('.work/worktrees/benchmark-v1.4.1/results/benchmarks/2026-09-17-dynamic-baseline/justification-final-comparison')
code=Path('.work/worktrees/benchmark-v1.4.1/benchmarks/dynamic-v1.4')
sha=lambda b:hashlib.sha256(b).hexdigest()
summary=json.loads((root/'summary.json').read_text())
for name,key in [('render_justification_comparison.py','renderer_sha256'),('audit_justification_main.py','raw_auditor_sha256'),('justification_corrections.py','correction_validator_sha256')]:assert sha((code/name).read_bytes())==summary[key]
assert sha((root/'config.snapshot.json').read_bytes())==summary['config_sha256']
mapping={'baseline-original':'justification-baseline-original-audit','baseline-pure-dl':'justification-baseline-pure-dl-audit','v142-original':'dynamic-v142-original-audit','v142-pure-dl':'dynamic-v142-pure-dl-audit'}
for suffix in ['baseline-original','baseline-pure-dl','final-original','final-pure-dl']:mapping['stream-v4-'+suffix]='justification-stream-v4-'+suffix
for suffix in ['original','pure-dl']:mapping['stream-v4-konclude-'+suffix]='justification-konclude-stream-v4-'+suffix
counts={};pending=[]
for source,folder in mapping.items():
 local=Path('.work/artifacts')/folder
 archives=list(local.glob('tasks*.tar.gz'));members={}
 if archives:
  with tarfile.open(archives[0]) as t:
   for m in t.getmembers():
    if m.isfile():members[m.name]=t.extractfile(m).read()
 for row in csv.DictReader((root/'artifacts.tsv').open(),delimiter='\t'):
  if row['source']!=source:continue
  assert row['present']=='True'
  kind=row['kind'];name=Path(row['path']).name
  if kind in ['independent_audit','logical_normalization']:data=(local/name).read_bytes()
  else:
   key='tasks/'+name if kind=='frozen_task' else name
   candidates=[v for k,v in members.items() if k==key or k.endswith('/'+key)]
   if not candidates and (local/key).is_file():candidates=[(local/key).read_bytes()]
   if not candidates:pending.append(dict(source=source,kind=kind,path=row['path']));continue
   assert all(v==candidates[0] for v in candidates);data=candidates[0]
  assert sha(data)==row['sha256'],row
  counts[kind]=counts.get(kind,0)+1
result=dict(renderer_and_validator_match=True,config_snapshot_match=True,verified_artifact_counts=counts,remaining_local_binding_checks=pending)
(root/'parent-input-binding-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(counts,'remaining',len(pending))
