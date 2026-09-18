import csv,json,statistics,hashlib
from collections import defaultdict,Counter
from pathlib import Path
root=Path('.work/worktrees/benchmark-v1.4.1/results/benchmarks/2026-09-17-dynamic-baseline/justification-final-comparison')
rows=[r for r in csv.DictReader((root/'attempts.tsv').open(),delimiter='\t') if r['comparison_selected']=='True' and r['warmup']=='False' and (not r['arm'].startswith('km-') or r['final_km']=='True')]
assert len(rows)==7650
groups=defaultdict(list)
keys=['source','ontology','query_hash','track','limit','arm']
for r in rows:groups[tuple(r[k] for k in keys)].append(r)
out=[]
for key,group in sorted(groups.items()):
 assert len(group)==5 and {r['repetition'] for r in group}==set('12345')
 observed=[float(r['peak_tree_rss_bytes'])/1048576 for r in group if r['peak_tree_rss_bytes'] and float(r['peak_tree_rss_bytes'])>0]
 good=[float(r['peak_tree_rss_bytes'])/1048576 for r in group if r['performance_eligible']=='True' and r['peak_tree_rss_bytes'] and float(r['peak_tree_rss_bytes'])>0]
 entry=dict(zip(keys,key),scheduled=5,positive_rss_samples=len(observed),zero_or_missing_samples=5-len(observed),verified_positive_samples=len(good),complete_verified_five_repetitions=len(good)==5,execution_counts=json.dumps(dict(Counter(r['execution'] for r in group)),sort_keys=True))
 for prefix,vals in [('all_observed',observed),('verified',good)]:
  med=statistics.median(vals) if vals else None
  q=statistics.quantiles(vals,n=4,method='inclusive') if len(vals)>1 else None
  entry.update({prefix+'_rss_mib_'+k:v for k,v in dict(median=med,minimum=min(vals) if vals else None,maximum=max(vals) if vals else None,iqr=q[2]-q[0] if q else (0 if vals else None),mad=statistics.median(abs(x-med) for x in vals) if vals else None).items()})
 out.append(entry)
with (root/'selected-memory-cases.tsv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=list(out[0]),delimiter='\t');w.writeheader();w.writerows(out)
receipt=dict(attempts_sha256=hashlib.sha256((root/'attempts.tsv').read_bytes()).hexdigest(),selected_measured=len(rows),cases=len(out),zero_or_missing_samples=sum(r['zero_or_missing_samples'] for r in out),complete_verified_five_rep_cases=sum(r['complete_verified_five_repetitions'] for r in out),summary_sha256=hashlib.sha256((root/'selected-memory-cases.tsv').read_bytes()).hexdigest())
(root/'memory-summary-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
