"""Review all completed incremental comparisons from bound canonical metadata."""
from pathlib import Path
from collections import Counter
import datetime,hashlib,json
root=Path('/ibex/scratch/projects/c2014/hohndor/km/v145-comparative-20261004')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def compare(a,b):
 assert all(a[k]==b[k] for k in ('source_sha256','source_signature_sha256','algorithm','fingerprint_script_sha256'))
 x,y=a['reported_consistency'],b['reported_consistency']
 if x is not None and y is not None and x!=y:return 'consistency_disagreement'
 if x is False and y is False:return 'inconsistent_agreement'
 if x is False or y is False:return 'incomparable_unknown_consistency'
 same=a['relation_sha256']==b['relation_sha256']
 if x is None or y is None:return 'conditional_taxonomy_agreement' if same else 'conditional_taxonomy_disagreement'
 return 'agreement' if same else 'taxonomy_disagreement'
completion=read(root/'globaldep-update-audit-completion.json')
paths=sorted(root.glob('update-audit-53234886/*/*/audit.json'))
assert len(paths)==completion['revision_audits']==395
counts={};disagreements=[];gaps=[];canonical_count=0;km_count=0
for path in paths:
 digest=sha(path);assert digest==completion['receipt_hashes'][str(path.relative_to(root))]
 audit=read(path);canonical={}
 for key,out in audit['outcomes'].items():
  if out['status']!='canonicalized_requires_comparison':continue
  cp=path.parent/(key+'.validated.json');assert sha(cp)==out['canonical_sha256']
  value=read(cp);assert value['status']=='ok' and value['source_sha256']==audit['source_sha256'] and value['raw_sha256']==out['extracted_sha256']
  canonical[key]=value;canonical_count+=1
 for kmkey,value in canonical.items():
  if not kmkey.startswith('km-'):continue
  km_count+=1;rep=kmkey.rsplit('-',1)[1]
  reference_status={k:compare(value,v) for k,v in canonical.items() if k.split('-')[0] in ('hermit','konclude','openllet','jfact')}
  agreeing=[k for k,status in reference_status.items() if status in ('agreement','inconsistent_agreement')]
  context={'ontology':path.parent.parent.name,'revision':audit['revision'],'km_output':kmkey,'source_sha256':audit['source_sha256'],'audit_sha256':digest}
  if not agreeing:gaps.append(dict(context,available_full_dl_reference_comparisons=reference_status))
  same_rep_agreeing=[k for k in agreeing if k.rsplit('-',1)[1]==rep]
  for key,out in audit['outcomes'].items():
   if key.startswith('km-') or key.rsplit('-',1)[1]!=rep:continue
   status=compare(value,canonical[key]) if key in canonical else 'comparison_unavailable'
   pair=kmkey.rsplit('-',1)[0]+' / '+key.rsplit('-',1)[0]
   counts.setdefault(pair,Counter())[status]+=1
   if status.endswith('disagreement'):
    disagreements.append(dict(context,baseline_output=key,status=status,independent_agreeing_outputs=same_rep_agreeing))
result={'observed_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'All 395 prepared revisions and all available cold/retained KM outputs, with all baseline modes in the same repetition. Missing KM outputs are counted in measurement coverage, not these conditional comparisons. Agreement corroborates an output; it does not independently prove every entailment.','completion_receipt_sha256':sha(root/'globaldep-update-audit-completion.json'),'revision_audits':len(paths),'canonical_outputs':canonical_count,'km_outputs':km_count,'comparison_counts':{k:dict(v) for k,v in counts.items()},'disagreements':disagreements,'uncorroborated_disagreements':[x for x in disagreements if not x['independent_agreeing_outputs']],'km_independent_evidence_gaps':gaps}
f=root/'globaldep-incremental-all-baseline-review-final.json'
with f.open('x') as stream:json.dump(result,stream,indent=2)
print(json.dumps({'revision_audits':len(paths),'canonical_outputs':canonical_count,'km_outputs':km_count,'disagreement_counts':dict(Counter(x['baseline_output'].rsplit('-',1)[0]+':'+x['status'] for x in disagreements)),'uncorroborated_disagreements':len(result['uncorroborated_disagreements']),'independent_evidence_gaps':dict(Counter(x['ontology'] for x in gaps))}))
