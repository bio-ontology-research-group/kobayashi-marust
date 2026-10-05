"""Summarize immutable v1.4.5 audit metadata as counts and wall-clock times.
No reasoner execution and no raw taxonomy parsing.
"""
from pathlib import Path
from collections import defaultdict,Counter
import json,hashlib,statistics,math,datetime,sys
root=Path(sys.argv[1]);output=Path(sys.argv[2]);FULL={'km','hermit','konclude','openllet','jfact'}
def read(p):return json.loads(p.read_text())
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def agree(a,b):
 assert all(a[k]==b[k] for k in ('source_sha256','source_signature_sha256','algorithm','fingerprint_script_sha256'))
 x,y=a['reported_consistency'],b['reported_consistency']
 return (x is False and y is False) or (x is True and y is True and a['relation_sha256']==b['relation_sha256'])
def summarize(cases,attempts):
 out={}
 for name,rows in sorted(cases.items()):
  solved=[r for r in rows if r['solved']];times=[r['wall_s'] for r in solved]
  assert all(isinstance(t,(int,float)) and math.isfinite(t) and t>0 for t in times)
  out[name]={'attempts':attempts,'complete_outputs':len(rows),'solved':len(solved),'mean_wall_s':statistics.mean(times) if times else None,'median_wall_s':statistics.median(times) if times else None}
 return out
cn='classification-report-v4-full-global-dependency-53234888.json';un='updates-report-v5-full-global-dependency-53234889.json';jn='justification-report-v4-full-global-dependency-53234890.json'
c,u,j=[read(root/n) for n in (cn,un,jn)];cases=defaultdict(list);classification_admissions=Counter()
for idx,row in enumerate(c['cases']):
 classification_admissions[row['input_admission']]+=1
 if row['input_admission']!='checks_passed':continue
 ap=root/('classification-audit-'+c['audit_job'])/str(idx//32)/row['ontology']/'audit.json';assert digest(ap)==row['audit_sha256'];a=read(ap);assert a['source_sha256']==row['source_sha256']
 for name,out in row['outcomes'].items():
  cases[name]
  if out.get('audit_status')!='canonicalized_requires_comparison':continue
  refs=[]
  for pair in a['comparisons']:
   if name not in (pair['left'],pair['right']) or pair.get('agreement') is not True:continue
   other=pair['right'] if pair['left']==name else pair['left']
   if other in FULL:refs.append(other)
  rp=root.joinpath(*Path(out['record']).parts[-4:]);assert digest(rp)==a['outcomes'][name]['measurement_receipt_sha256'];record=read(rp)
  assert record['source_sha256']==row['source_sha256'] and record['timeout_s']==240 and record['memory_mib']==20480 and record['cpu_threads']==1
  cases[name].append({'ontology':row['ontology'],'solved':bool(refs),'agreeing_references':refs,'wall_s':record['wall_s'],'measurement_sha256':digest(rp),'audit_sha256':row['audit_sha256']})
classification={'input_admission_counts':dict(classification_admissions),'summary':summarize(cases,classification_admissions['checks_passed']),'cases':dict(cases)}
phases={'initialization':defaultdict(list),'updates':defaultdict(list)};binding=read(root/'globaldep-update-audit-completion.json')['receipt_hashes']
for source in u['sources']:
 if source['preparation_status']!='prepared':continue
 for revision in range(5):
  phase='initialization' if revision==0 else 'updates';ap=root/('update-audit-'+u['audit_job'])/source['ontology']/f'{revision:03}'/'audit.json';assert digest(ap)==binding[str(ap.relative_to(root))];a=read(ap);canonical={}
  for key,out in a['outcomes'].items():
   phases[phase][key.rsplit('-',1)[0]]
   if out['status']!='canonicalized_requires_comparison':continue
   cp=ap.parent/(key+'.validated.json');assert digest(cp)==out['canonical_sha256'];v=read(cp);assert v['source_sha256']==a['source_sha256'] and v['raw_sha256']==out['extracted_sha256'];canonical[key]=v
  for key,v in canonical.items():
   name,rep=key.rsplit('-',1);baseline=name.split('-')[0]
   refs=[k for k,w in canonical.items() if k.rsplit('-',1)[1]==rep and k.split('-')[0] in FULL and k.split('-')[0]!=baseline and agree(v,w)]
   phases[phase][name].append({'ontology':source['ontology'],'revision':revision,'repetition':int(rep),'solved':bool(refs),'agreeing_references':refs,'wall_s':a['outcomes'][key]['wall_s'],'measurement_sha256':a['outcomes'][key]['measurement_receipt_sha256'],'audit_sha256':digest(ap)})
updates={phase:{'summary':summarize(rows,240 if phase=='initialization' else 960),'cases':dict(rows)} for phase,rows in phases.items()}
proofs=defaultdict(list)
for source in j['sources']:
 for row in source['cases']:
  name=row['baseline'];proofs[name]
  if row['status']=='verified_evidence_intact':proofs[name].append({'ontology':source['ontology'],'query':row['query'],'repetition':row['repetition'],'solved':True,'wall_s':row['generation_wall_s'],'measurement_sha256':row['measurement_receipt_sha256']})
result={'generated_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'limits':{'wall_seconds_per_attempt':240,'memory_gib':20,'cpus':1},'definition':'Classification and update solved counts require a complete audited output with known consistency agreeing with at least one different full-DL reasoner (KM, HermiT, Konclude, Openllet, JFact). Updates require the same revision and repetition. This is corroboration, not formal adjudication. Unknown consistency and uncorroborated outputs are excluded even when a separate case-specific proof exists. Justification solved counts require independent source-membership, entailment and subset-minimality verification. Means and medians use the solved attempts only; each method may solve a different subset. Repetitions count as separate attempts. Timeouts and failures remain in denominators; means do not substitute 240 seconds for failures.','source_reports':{n:digest(root/n) for n in (cn,un,jn)},'classification':classification,'incremental':updates,'justifications':{'summary':summarize(proofs,372),'cases':dict(proofs)}}
with output.open('x') as f:json.dump(result,f,indent=2)
print(json.dumps({p:result[p]['summary'] for p in ('classification','justifications')}));print(json.dumps({'updates':updates['updates']['summary'],'initialization':updates['initialization']['summary']}))
