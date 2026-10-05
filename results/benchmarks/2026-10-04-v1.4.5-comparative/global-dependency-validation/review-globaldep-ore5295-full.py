"""Bind the fixed global-dependency regression to all full-benchmark revisions."""
from pathlib import Path
import hashlib,json,datetime
root=Path('/ibex/scratch/projects/c2014/hohndor/km/v145-comparative-20261004');base=root/'update-audit-53234886/ore_ont_5295'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
paths=[base/f'{n:03}'/'audit.json' for n in range(5)]
if any(not p.exists() or read(p)['status']!='audited_available_outputs' for p in paths):
 print('ore5295 full five-revision audit still in progress');raise SystemExit(0)
prep=root/'prepared-updates-53201177/ore_ont_5295/receipt.json';prepared=read(prep);rows=[]
for n,p in enumerate(paths):
 audit=read(p);assert audit['source_sha256']==prepared['files'][f'{n:03}.ofn']
 canonical={}
 for key,out in audit['outcomes'].items():
  if out['status']!='canonicalized_requires_comparison':continue
  cp=p.parent/(key+'.validated.json');assert sha(cp)==out['canonical_sha256'];v=read(cp)
  assert v['source_sha256']==audit['source_sha256'] and v['raw_sha256']==out['extracted_sha256'];canonical[key]=v
 keys=[f'km-{mode}-{rep}' for mode in ('cold','retained') for rep in range(3)]
 assert all(k in canonical for k in keys)
 first=canonical[keys[0]]
 assert first['reported_consistency'] is True
 for key in keys:
  v=canonical[key];assert all(v[k]==first[k] for k in ('source_sha256','source_signature_sha256','relation_sha256','reported_consistency','algorithm','fingerprint_script_sha256'))
 matches=[]
 for key,v in canonical.items():
  if key.split('-')[0] in ('hermit','konclude','openllet','jfact') and all(v[k]==first[k] for k in ('source_sha256','source_signature_sha256','relation_sha256','reported_consistency','algorithm','fingerprint_script_sha256')):matches.append(key)
 assert matches,('no independent full-DL comparison agreement',n)
 rows.append({'revision':n,'audit_sha256':sha(p),'km_cold_and_retained_all_three_repetitions_agree':True,'independent_agreeing_outputs':matches,'relation_sha256':first['relation_sha256'],'km_comparisons':[c for c in audit['comparisons'] if any(c[k].startswith('km-') for k in ('left','right'))]})
result={'observed_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'all five revisions agree across three cold and retained repetitions with independent baseline corroboration','source_sha256':prepared['source_sha256'],'preparation_sha256':sha(prep),'revisions':rows,'reuse_scope':'exact rebuild is preserved as fallback; this does not establish internal reuse'}
with (root/'globaldep-ore5295-full-benchmark-review.json').open('x') as f:json.dump(result,f,indent=2)
print(json.dumps({'status':result['status'],'revisions':len(rows)}))
