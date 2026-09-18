import csv,json,math,statistics,hashlib
from pathlib import Path
from collections import Counter,defaultdict
root=Path('.work/worktrees/benchmark-v1.4.1/results/benchmarks/2026-09-17-dynamic-baseline/justification-final-comparison')
read=lambda name:list(csv.DictReader((root/name).open(),delimiter='\t'))
rows=read('attempts.tsv'); selected=[r for r in rows if r['comparison_selected']=='True' and r['warmup']=='False']
assert len(rows)==13680 and len(selected)==9150
index={}
for r in selected:
 if r['arm'].startswith('km-') and r['final_km']!='True':continue
 key=tuple(r[k] for k in ['ontology','query_hash','track','repetition','limit','arm'])
 assert key not in index
 index[key]=r
 if r['performance_eligible']=='True':
  assert r['semantic_status']=='verified' and r['raw_audit_status']=='correct' and r['binding_issues']=='[]'
  assert int(r['duplicate_occurrences'])==0 and float(r['wall_s'])>0
pairs=read('paired-wall.tsv');groups=defaultdict(list)
for p in pairs:
 key=tuple(p[k] for k in ['ontology','query_hash','track','repetition','limit'])
 a=index[key+(p['km_arm'],)];b=index[key+(p['peer_arm'],)]
 assert a['input_sha256']==b['input_sha256']
 assert p['km_source']==a['source'] and p['peer_source']==b['source']
 assert p['km_harness_revision']==a['harness_revision'] and p['peer_harness_revision']==b['harness_revision']
 eligible=a['performance_eligible']==b['performance_eligible']=='True' and (a['mechanism']==b['mechanism'] or a['arm']=='km-native') and (a['limit']=='1' or (a['enumeration']==b['enumeration']=='complete' and a['distinct_logical_supports']==b['distinct_logical_supports'] and a['logical_support_family_sha256']==b['logical_support_family_sha256']) or a['distinct_logical_supports']==a['limit']==b['distinct_logical_supports'])
 assert eligible==(p['paired_eligible']=='True')
 if eligible:assert math.isclose(float(p['peer_over_km_wall_ratio']),float(b['wall_s'])/float(a['wall_s']),rel_tol=1e-12)
 else:assert not p['peer_over_km_wall_ratio']
 groups[tuple(p[k] for k in ['ontology','query_hash','track','limit','km_arm','peer_arm'])].append(p)
summary=defaultdict(list)
for k,g in groups.items():
 assert len(g)==5 and {p['repetition'] for p in g}==set('12345')
 summary[k[2:]].append(statistics.median(float(p['peer_over_km_wall_ratio']) for p in g) if all(p['paired_eligible']=='True' for p in g) else None)
for s in read('paired-summary.tsv'):
 values=summary[tuple(s[k] for k in ['track','limit','km_arm','peer_arm'])];good=[x for x in values if x is not None]
 assert int(s['expected_cases'])==len(values) and int(s['complete_five_rep_cases'])==len(good)
 if good:assert math.isclose(float(s['case_ratio_median']),statistics.median(good),rel_tol=1e-12)
coverage=[]
for arm in sorted({r['arm'] for r in index.values()}):
 g=[r for r in index.values() if r['arm']==arm]
 coverage.append(dict(arm=arm,measured=len(g),statuses=dict(Counter(r['raw_audit_status'] for r in g))))
result=dict(archive_attempts=len(rows),selected_measured_including_baseline_km=len(selected),final_comparison_measured=len(index),paired_rows=len(pairs),eligible_pairs=sum(p['paired_eligible']=='True' for p in pairs),checks='unique selected keys; final KM only; matching input hashes; selected cohort provenance; eligibility; every ratio; complete five-repetition case denominators and median ratios',coverage=coverage)
(root/'parent-comparison-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
