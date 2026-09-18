import json,csv,tarfile,hashlib,gzip,shutil,datetime
from collections import Counter,defaultdict
import sys
sys.path.insert(0,".work/worktrees/benchmark-v1.4.1/benchmarks/dynamic-v1.4")
from justification_corrections import arms
from pathlib import Path
sha=lambda b:hashlib.sha256(b).hexdigest()
for label,job in [('baseline-original',51982402)]:
 root=Path('.work/artifacts/justification-baseline-original-audit')
 rows=json.loads((root/'audit.json').read_text())['rows'];expected={};tasks={}
 with tarfile.open(root/'tasks-and-receipts.tar.gz') as ar:
  read=lambda n:ar.extractfile(n).read()
  manifest=read('driver-manifest.json')
  for m in ar.getmembers():
   if not m.name.startswith('tasks/') or not m.name.endswith('.json'):continue
   tid=Path(m.name).stem;b=read(m.name);t=json.loads(b);tasks[tid]=t
   assert read('results/'+tid+'/task.json')==b
   assert json.loads(read('results/'+tid+'/driver-manifest.json'))==json.loads(manifest)
   assert sha(manifest)==t['driver_manifest_sha256']
   assert read('results/'+tid+'/source.sha256').decode().strip()==t['sha256']
   assert read('results/'+tid+'/COMPLETE').strip()
   for limit in t['limits']:
    for arm in arms(t):
     k=tuple(t[x] for x in ['ontology','query_id','track','repetition'])+(limit,arm)
     assert k not in expected;expected[k]=tid
 assert len(tasks)==240 and len(expected)==7560
 keys=[tuple(r[x] for x in ['ontology','query_id','track','repetition','limit','arm']) for r in rows]
 assert len(keys)==len(set(keys)) and set(keys)==set(expected)
 normalized=defaultdict(list)
 with (root/'normalized-supports.tsv').open() as f:
  for n in csv.DictReader(f,delimiter='\t'):
   bits=n['support'].split('/');normalized[tuple(bits[:3])].append(n['sha256'])
 for k,r in zip(keys,rows):
  assert r['warmup']==(r['repetition']==0)
  if r['status']=='correct':
   values=normalized[(expected[k],str(r['limit']),r['arm'])]
   assert len(values)==r['supports'] and len(set(values))==r['distinct_logical_supports'] and len(values)-len(set(values))==r['duplicate_logical_supports']==0
 assert sha((root/'audit-hashes.txt').read_bytes())=='411b1366db2b3ade6040be8d0587df31b65395668460a4ab4b74401f69ad1004'
 measured=[r for r in rows if not r['warmup']];assert len(measured)==6300
 result=dict(observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),audit_job=job,audit_exit='COMPLETED 0:0',task_count=240,attempts=7560,exact_manifest_coverage=True,correct_support_normalization_verified=True,receipts=dict(tasks=240,problems=[]),measured_attempts=6300,measured_statuses=dict(Counter(r['status'] for r in measured)),all_statuses=dict(Counter(r['status'] for r in rows)),files={p.name:sha(p.read_bytes()) for p in root.iterdir() if p.is_file()})
 out=Path('.work/worktrees/benchmark-v1.4.1/results/benchmarks/2026-09-17-dynamic-baseline/justification-original-peer-audit');out.mkdir(exist_ok=True)
 for name in ['audit.json','normalized-supports.tsv']:(out/(name+'.gz')).write_bytes(gzip.compress((root/name).read_bytes(),mtime=0))
 for name in ['audit-hashes.txt','tasks-and-receipts.tar.gz']:shutil.copy2(root/name,out/name)
 (out/'parent-verification.json').write_text(json.dumps(result,indent=2)+'\n')
 print(label,json.dumps(result['measured_statuses']))
