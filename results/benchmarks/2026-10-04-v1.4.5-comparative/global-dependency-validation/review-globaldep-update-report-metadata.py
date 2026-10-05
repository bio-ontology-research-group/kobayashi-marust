"""Review completed update report bindings and denominators; metadata only.
Recomputes comparisons from bound canonical fingerprints and paired costs.
"""
from pathlib import Path
from collections import Counter
from itertools import combinations
import hashlib,json,datetime,math
from statistics import median
root=Path('/ibex/scratch/projects/c2014/hohndor/km/v145-comparative-20261004')
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
p=root/'updates-report-v5-full-global-dependency-53234889.json'
if not p.exists():
 print('Final incremental report is not available yet');raise SystemExit(0)
r=read(p);runs=read(root/'run-set-global-dependency.json');selection=read(root/'workload-selection.json')['selected']
assert r['run_set']==runs and r['audit_job']=='53234886'
assert r['selection_sha256']==sha(root/'workload-selection.json')
assert r['selected_ontologies']==len(selection)==80 and r['revisions_per_ontology']==5 and r['repetitions']==3
assert len(r['sources'])==80 and len({s['ontology'] for s in r['sources']})==80
inventory=read(root/runs['inventory'])['artifacts'];names=sorted(x['id'] for x in inventory)
assert len(names)==10
methods=[b+'-'+m for b in names for m in (['cold'] if b in ('rustdl','more','sequoia') else ['cold','retained'])]
assert len(methods)==17
coverage={n:Counter() for n in methods};hashes={};prepared_count=0;km_errors=[]
allpairs=list(combinations(methods,2))
counts={(phase,*pair):Counter() for phase in ('initialization','updates') for pair in allpairs}
costs={key:[] for key in counts}
issues=[];km_discrepancies=[]
def comparison(a,b):
 assert all(a[k]==b[k] for k in ('source_sha256','source_signature_sha256','algorithm','fingerprint_script_sha256'))
 x,y=a['reported_consistency'],b['reported_consistency']
 if x is not None and y is not None and x!=y:return 'consistency_disagreement'
 if x is False and y is False:return 'inconsistent_agreement'
 if x is False or y is False:return 'incomparable_unknown_consistency'
 same=a['relation_sha256']==b['relation_sha256']
 if x is None or y is None:return 'conditional_taxonomy_agreement' if same else 'conditional_taxonomy_disagreement'
 return 'agreement' if same else 'taxonomy_disagreement'

for source,row in zip(selection,r['sources']):
 ont=source['ontology'];assert row['ontology']==ont and row['source_sha256']==source['sha256']
 pp=root/('prepared-updates-'+runs['updates_preparation'])/ont/'receipt.json';prep=read(pp)
 assert prep['source_sha256']==source['sha256'] and row['preparation_status']==prep['status']
 prepared_count+=prep['status']=='prepared'
 sp=root/'update-audit-53234886'/ont/'summary.json';summary=read(sp)
 assert summary['run_set']==runs and summary['source_sha256']==source['sha256']
 if 'preparation_receipt_sha256' in summary:assert summary['preparation_receipt_sha256']==sha(pp)
 hashes[str(sp.relative_to(root))]=sha(sp)
 assert len(row['revisions'])==5
 for rev,rr in enumerate(row['revisions']):
  assert rr['revision']==rev
  ap=sp.parent/f'{rev:03}'/'audit.json'
  if prep['status']!='prepared':
   assert ont=='ore_ont_16744' and prep['status']=='preparation_timeout' and rr['status']=='preparation_failed'
   issues.append({'ontology':ont,'revision':rev,'status':'preparation_failed'})
   for name in methods:coverage[name]['preparation_failed']+=3
   for pair in allpairs:counts[('initialization' if rev==0 else 'updates',*pair)]['comparison_unavailable']+=3
   continue
  audit=read(ap);hashes[str(ap.relative_to(root))]=sha(ap)
  assert audit['status']==rr['status']=='audited_available_outputs'
  assert audit['source_sha256']==prep['files'][f'{rev:03}.ofn']
  canonical={}
  for name in methods:
   for rep in range(3):
    key=f'{name}-{rep}';out=audit['outcomes'][key];coverage[name][out['status']]+=1
    if out['status']=='canonicalized_requires_comparison':
     cp=ap.parent/(key+'.validated.json');assert sha(cp)==out['canonical_sha256']
     value=read(cp);assert value['status']=='ok' and value['source_sha256']==audit['source_sha256']
     assert value['raw_sha256']==out['extracted_sha256']
     canonical[key]=value
    if name.startswith('km-') and out['status'] in ('validation_error','missing_measurement'):km_errors.append((ont,rev,key,out))
  for rep in range(3):
   for left,right in allpairs:
    key=('initialization' if rev==0 else 'updates',left,right)
    lk,rk=f'{left}-{rep}',f'{right}-{rep}'
    status=comparison(canonical[lk],canonical[rk]) if lk in canonical and rk in canonical else 'comparison_unavailable'
    counts[key][status]+=1
    if status.endswith('disagreement'):
     issue={'ontology':ont,'revision':rev,'repetition':rep,'pair':[left,right],'status':status};issues.append(issue)
     if left.startswith('km-') or right.startswith('km-'):
      kmkey=lk if left.startswith('km-') else rk
      matches=[other for other,v in canonical.items() if other.split('-')[0] in ('hermit','konclude','openllet','jfact') and other.endswith('-'+str(rep)) and comparison(canonical[kmkey],v) in ('agreement','inconsistent_agreement')]
      km_discrepancies.append(dict(issue,km_output=kmkey,independent_agreeing_outputs=matches,audit_sha256=hashes[str(ap.relative_to(root))]))
    if status in ('agreement','inconsistent_agreement'):costs[key].append((audit['outcomes'][lk],audit['outcomes'][rk]))
assert prepared_count==79 and not km_errors
assert issues==r['issues'], 'report issue list differs'
assert {n:dict(c) for n,c in coverage.items()}==r['coverage_per_revision_repetition']
pairs=set(combinations(methods,2));assert len(r['pairwise'])==2*len(pairs)==272
assert {(x['phase'],x['left'],x['right']) for x in r['pairwise']}=={(phase,*pair) for phase in ('initialization','updates') for pair in pairs}
for row in r['pairwise']:
 key=(row['phase'],row['left'],row['right'])
 assert row['outcomes']==dict(counts[key]),key
 expected={'cases':len(costs[key]),'ratio_direction':'right / left'}
 for field in ('wall_s','peak_bytes'):
  values=[(a.get(field),b.get(field)) for a,b in costs[key]]
  values=[(a,b) for a,b in values if all(isinstance(v,(int,float)) and math.isfinite(v) and v>0 for v in (a,b))]
  stats={'measured_pairs':len(values)}
  if values:stats.update(left_median=median(a for a,b in values),right_median=median(b for a,b in values),median_paired_ratio=median(b/a for a,b in values))
  expected[field]=stats
 assert row['costs_on_fully_agreeing_cases']==expected,key
 assert sum(row['outcomes'].values())== (240 if row['phase']=='initialization' else 960)
 assert row['costs_on_fully_agreeing_cases']['cases']==sum(row['outcomes'].get(k,0) for k in ('agreement','inconsistent_agreement'))
previous_path=root/'updates-report-v5-full-cachefix-53229141.json'
if previous_path.exists():
 old=read(previous_path);oldpairs={(x['phase'],x['left'],x['right']):x for x in old['pairwise']}
 for row in r['pairwise']:
  if not any(row[k].startswith('km-') for k in ('left','right')):assert row==oldpairs[row['phase'],row['left'],row['right']]
 for name in methods:
  if not name.startswith('km-'):assert r['coverage_per_revision_repetition'][name]==old['coverage_per_revision_repetition'][name]
result={'observed_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'report_sha256':sha(p),'status':'metadata bindings, denominators, canonical comparisons and paired costs verified; semantic discrepancy adjudication remains separate','selected_sources':80,'prepared_sources':79,'revision_audits':395,'methods':17,'phase_pair_reports':272,'baseline_only_comparison_performed':previous_path.exists(),'audit_hashes':hashes,'km_validation_errors':km_errors,'verified_report_issue_count':len(issues),'km_discrepancies':km_discrepancies,'uncorroborated_km_discrepancies':[x for x in km_discrepancies if not x['independent_agreeing_outputs']]}
with (root/'globaldep-update-report-metadata-review.json').open('x') as f:json.dump(result,f,indent=2)
print(json.dumps({k:v for k,v in result.items() if k not in ('audit_hashes','km_discrepancies')}))
