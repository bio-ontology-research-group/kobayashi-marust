"""Audit completed finite-role-index pairs without promoting unfinished measurements."""
import argparse,hashlib,json,subprocess,sys
from pathlib import Path
from compare_taxonomies import compare
import tree_watchdog as watchdog
watchdog.protect_supervisor()
p=argparse.ArgumentParser()
for name in ['measurements','references','output']: p.add_argument('--'+name,type=Path,required=True)
a=p.parse_args(); root=Path(__file__).resolve().parent
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
inputs={r['ontology']:r for r in json.loads((root/'role-index-regression-inputs.json').read_text())['inputs']}
inventories={arm:json.loads((root/name).read_text()) for arm,name in [('baseline','single-worker-candidate-artifact.json'),('indexed','finite-role-index-full-artifact.json')]}
artifacts={arm:inventory['artifacts'][0]['sha256'] for arm,inventory in inventories.items()}
rows=[];seen=set()
for receipt in sorted(a.measurements.glob('*/*/receipt.json')):
 d=json.loads(receipt.read_text()); source=d['input']; name=source['ontology'];assert source==inputs[name]
 refs=a.references/name;assert digest(refs/'audit.json')==source['reference_audit_sha256']
 audit=json.loads((refs/'audit.json').read_text()); assert audit['source_sha256']==source['sha256']
 for item in d['records']:
  arm=item['arm'];key=(name,d['repetition'],arm);assert key not in seen;seen.add(key)
  assert item['flags']==dict(inventories[arm]['flags'],KM_TIMING='1')
  folder=receipt.parent/arm;assert digest(folder/'record.json')==item['record_sha256']
  record=json.loads((folder/'record.json').read_text());assert record==item['record']
  assert record['artifact_sha256']==artifacts[arm] and record['source_sha256']==source['sha256']
  assert record['timeout_s']==240 and record['memory_mib']==20480 and record['cpu_threads']==1
  assert record['runner_sha256']==digest(root/'measure_classification.py')
  assert record['watchdog_sha256']==digest(root/'tree_watchdog.py')
  result=dict(ontology=name,repetition=d['repetition'],arm=arm,status=record['status'],wall_s=record.get('wall_s'),verified=False,record_sha256=item['record_sha256'],comparisons={})
  if record['status']=='executed_unvalidated':
   assert digest(folder/'taxonomy.raw')==record['files']['taxonomy.raw']['sha256']
   command=[sys.executable,str(root/'canonicalize.py'),'--input',str(folder/'taxonomy.raw'),'--format','km-json','--signature',str(refs/'signature.tsv'),'--output-prefix',str(folder/'canonical'),'--fingerprint-script',str(root/'full_iri_fingerprint.py')]
   with (folder/'audit.stdout').open('wb') as out, (folder/'audit.stderr').open('wb') as err:
    proc=subprocess.Popen(command,stdout=out,stderr=err,stdin=subprocess.DEVNULL,preexec_fn=watchdog.child_preexec)
    watched=watchdog.monitor(proc,timeout=240,memcap_bytes=20*1024**3)
   assert watched.status=='ok' and proc.returncode==0, (name,arm,'canonicalization failed')
   answer=json.loads((folder/'canonical.validated.json').read_text())
   for method in ['konclude','hermit','openllet','jfact']:
    prev=audit['outcomes'].get(method,{})
    if prev.get('status')!='canonicalized_requires_comparison':continue
    f=refs/(method+'.validated.json');assert digest(f)==prev['canonical_sha256']
    result['comparisons'][method]=compare(answer,json.loads(f.read_text()))
   result['verified']=any(c.get('agreement') is True for c in result['comparisons'].values())
   result['canonical_sha256']=digest(folder/'canonical.validated.json')
  rows.append(result)
expected={(name,rep,w) for name in inputs for rep in range(2) for w in ['baseline','indexed']}
assert seen<=expected
report=dict(job_id=53333094,diagnostic_only=True,complete=seen==expected,records=rows,release_approved=False,audit_script_sha256=digest(Path(__file__)))
a.output.write_text(json.dumps(report,indent=2)+'\n')
print([(r['ontology'],r['repetition'],r['arm'],r['verified']) for r in rows],flush=True)
