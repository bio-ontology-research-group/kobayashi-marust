from pathlib import Path
import json,hashlib,datetime,collections
root=Path('/ibex/scratch/projects/c2014/hohndor/km/v145-comparative-20261004');cases=[];counts=collections.Counter()
completion=json.loads((root/'globaldep-update-audit-completion.json').read_text())
paths=sorted(root.glob('update-audit-53234886/*/*/audit.json'));assert len(paths)==completion['revision_audits']==395
for p in paths:
 assert hashlib.sha256(p.read_bytes()).hexdigest()==completion['receipt_hashes'][str(p.relative_to(root))]
 d=json.loads(p.read_text());missing=[c for c in d['comparisons'] if (c['left'].startswith('km-') or c['right'].startswith('km-')) and c['status']=='comparison_unavailable']
 if not missing:continue
 keys=set(k for c in missing for k in [c['left'],c['right']]);out={k:v for k,v in d['outcomes'].items() if k in keys and v['status']!='canonicalized_requires_comparison'}
 cases.append({'path':str(p.relative_to(root)),'audit_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'comparisons':missing,'outcomes':out})
 for k,v in out.items():counts[k+':'+v['status']]+=1
result={'observed_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'All 395 completed audit receipts verified against the completion inventory; unavailable comparisons remain excluded from verified paired costs','comparisons':sum(len(c['comparisons']) for c in cases),'outcome_counts':dict(counts),'cases':cases}
p=root/'globaldep-update-unavailable-review-final.json'
with p.open('x') as f:json.dump(result,f,indent=2)
print(json.dumps({'comparisons':result['comparisons'],'outcome_counts':dict(counts),'cases':[c['path'] for c in cases]}))
