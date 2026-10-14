"""Audit completed scheduling pairs without promoting unfinished measurements."""
import argparse,hashlib,json,subprocess,sys
from pathlib import Path
from compare_taxonomies import compare
p=argparse.ArgumentParser()
for name in ['measurements','references','output']: p.add_argument('--'+name,type=Path,required=True)
a=p.parse_args(); root=Path(__file__).resolve().parent
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
inputs={r['ontology']:r for r in json.loads((root/'dense-slow-profile-inputs.json').read_text())['inputs']}
artifact=json.loads((root/'dense-data-candidate-artifact.json').read_text())['artifacts'][0]['sha256']
rows=[];seen=set()
for receipt in sorted(a.measurements.glob('*/*/receipt.json')):
 d=json.loads(receipt.read_text()); source=d['input']; name=source['ontology'];assert source==inputs[name]
 refs=a.references/name;assert digest(refs/'audit.json')==source['reference_audit_sha256']
 audit=json.loads((refs/'audit.json').read_text()); assert audit['source_sha256']==source['sha256']
 for item in d['records']:
  workers=item['workers'];key=(name,d['repetition'],workers);assert key not in seen;seen.add(key)
  folder=receipt.parent/('workers-'+str(workers));assert digest(folder/'record.json')==item['record_sha256']
  record=json.loads((folder/'record.json').read_text());assert record==item['record']
  assert record['artifact_sha256']==artifact and record['source_sha256']==source['sha256']
  assert record['timeout_s']==240 and record['memory_mib']==20480
  result=dict(ontology=name,repetition=d['repetition'],workers=workers,status=record['status'],wall_s=record.get('wall_s'),verified=False,record_sha256=item['record_sha256'],comparisons={})
  if record['status']=='executed_unvalidated':
   assert digest(folder/'taxonomy.raw')==record['files']['taxonomy.raw']['sha256']
   subprocess.run([sys.executable,str(root/'canonicalize.py'),'--input',str(folder/'taxonomy.raw'),'--format','km-json','--signature',str(refs/'signature.tsv'),'--output-prefix',str(folder/'canonical'),'--fingerprint-script',str(root/'full_iri_fingerprint.py')],check=True,capture_output=True,timeout=240)
   answer=json.loads((folder/'canonical.validated.json').read_text())
   for method in ['konclude','hermit']:
    prev=audit['outcomes'].get(method,{})
    if prev.get('status')!='canonicalized_requires_comparison':continue
    f=refs/(method+'.validated.json');assert digest(f)==prev['canonical_sha256']
    result['comparisons'][method]=compare(answer,json.loads(f.read_text()))
   result['verified']=any(c.get('agreement') is True for c in result['comparisons'].values())
   result['canonical_sha256']=digest(folder/'canonical.validated.json')
  rows.append(result)
expected={(name,rep,w) for name in ['ore_ont_14572','ore_ont_7361','ore_ont_9724'] for rep in range(2) for w in [1,2]}
assert seen<=expected
report=dict(job_id=53321214,diagnostic_only=True,complete=seen==expected,records=rows,release_approved=False,audit_script_sha256=digest(Path(__file__)))
a.output.write_text(json.dumps(report,indent=2)+'\n')
print([(r['ontology'],r['repetition'],r['workers'],r['verified']) for r in rows],flush=True)
