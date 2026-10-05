"""Verify terminal update audits and retain all comparison failures; metadata only."""
from pathlib import Path
from collections import Counter
import datetime,hashlib,json,subprocess
root=Path('/ibex/scratch/projects/c2014/hohndor/km/v145-comparative-20261004')
accounting=subprocess.check_output(['sacct','-n','-X','-j','53234886','--format=JobID,State,ExitCode','-P'],text=True)
rows=[x.split('|') for x in accounting.splitlines() if x.strip()]
if {x[0] for x in rows}!={f'53234886_{i}' for i in range(20)} or any(x[1:]!=['COMPLETED','0:0'] for x in rows):
 print(json.dumps({'status':'audits not all successfully terminal','accounting':accounting}));raise SystemExit(0)
hashes={};states=Counter();counts=Counter();disagreements=[];errors=[];audits=0
runs=json.loads((root/'run-set-global-dependency.json').read_text())
def read(p):
 raw=p.read_bytes();hashes[str(p.relative_to(root))]=hashlib.sha256(raw).hexdigest();return json.loads(raw)
sources=read(root/'workload-selection.json')['selected']
assert len(sources)==80 and len({s['ontology'] for s in sources})==80
for source in sources:
 ont=source['ontology'];sp=root/'update-audit-53234886'/ont/'summary.json';summary=read(sp)
 assert summary['source_sha256']==source['sha256'] and summary['run_set']==runs
 states[summary['status']]+=1
 pp=root/('prepared-updates-'+runs['updates_preparation'])/ont/'receipt.json';prep=read(pp)
 assert prep['source_sha256']==source['sha256']
 if prep['status']!='prepared':
  assert ont=='ore_ont_16744' and prep['status']=='preparation_timeout'
  assert summary['status']=='preparation_or_audit_error' and summary['error']=='source preparation failed' and not summary['revisions']
  continue
 assert summary['status']=='audit_finished' and len(summary['revisions'])==5
 assert summary['preparation_receipt_sha256']==hashes[str(pp.relative_to(root))]
 for revision in range(5):
  ap=sp.parent/f'{revision:03}'/'audit.json';a=read(ap);audits+=1
  assert a['status']=='audited_available_outputs' and a['source_sha256']==prep['files'][f'{revision:03}.ofn']
  assert len(a['outcomes'])==51
  for key,value in a['outcomes'].items():
   if key.startswith('km-') and value['status'] in ('validation_error','missing_measurement'):errors.append({'ontology':ont,'revision':revision,'key':key,'outcome':value})
  for c in a['comparisons']:
   if any(c[k].startswith('km-') for k in ('left','right')):
    counts[c['status']]+=1
    if c.get('agreement') is False or c.get('taxonomy_agreement') is False:disagreements.append({'ontology':ont,'revision':revision,'comparison':c})
assert audits==395 and states=={'audit_finished':79,'preparation_or_audit_error':1}
result={'observed_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'all update audits terminal and source-bound; report review and discrepancy adjudication separate','slurm_accounting':accounting,'sources':80,'revision_audits':audits,'summary_states':dict(states),'km_comparisons':dict(counts),'km_disagreements':disagreements,'km_validation_or_missing_errors':errors,'receipt_hashes':hashes}
with (root/'globaldep-update-audit-completion.json').open('x') as f:json.dump(result,f,indent=2)
print(json.dumps({k:v for k,v in result.items() if k not in ('receipt_hashes','slurm_accounting')}))
