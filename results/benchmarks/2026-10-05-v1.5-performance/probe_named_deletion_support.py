"""Read-only feasibility probe for retaining deletion rows with fresh named-Horn proofs.
Not a production reuse certificate. Full source coverage and IRI binding need an
executable certificate before any such row can bypass complete reasoning.
"""
import argparse,collections,hashlib,json,re,time
from pathlib import Path
p=argparse.ArgumentParser()
for name in ['old','new','source','answer','affected','fresh_answer','output']:p.add_argument('--'+name,type=Path,required=True)
a=p.parse_args();start=time.monotonic()
old=json.loads(a.old.read_text());new=json.loads(a.new.read_text())
key=lambda x:json.dumps(x,sort_keys=True,separators=(',',':'))
assert not (collections.Counter(map(key,new['source_axioms']))-collections.Counter(map(key,old['source_axioms'])))
answer=json.loads(a.answer.read_text())['result'];assert answer['consistent'] and answer['dropped']==0
queries=[old['concepts'][q] for q in old['queries']];assert len(set(queries))==len(queries)
# Only a unique full IRI with exactly the recorded local name may participate.
by_short=collections.defaultdict(set)
for iri in re.findall(r'<([^<>]+)>',a.source.read_text()):by_short[re.split(r'[/#]',iri)[-1]].add(iri)
iri_to_name={next(iter(iris)):name for name,iris in by_short.items() if len(iris)==1 and name in queries}
full=(1<<len(queries))-1; values=collections.defaultdict(int)
for i,q in enumerate(queries):values[q]|=1<<i
values['@top']=full
rules=[]
def body(c):
 if c=='Top':return []
 if isinstance(c,dict) and 'Name' in c:return [c['Name']]
 if isinstance(c,dict) and 'And' in c:
  parts=[body(x) for x in c['And']]
  if all(x is not None for x in parts):return sorted(set(sum(parts,[])))
 return None
def heads(c):
 if c=='Bottom':return ['@bottom']
 if isinstance(c,dict) and 'Name' in c:return [c['Name']]
 if isinstance(c,dict) and 'And' in c:return sum([heads(x) for x in c['And']],[])
 return []
def inclusion(left,right):
 b=body(left)
 if b is not None:
  rules.extend((b,h) for h in heads(right))
for ax in new['source_axioms']:
 kind=ax['kind'];left=ax['left'];right=ax['right']
 if kind in ['sub-class','equivalent']:inclusion(left,right)
 if kind=='equivalent':inclusion(right,left)
 if kind=='disjoint':
  x,y=body(left),body(right)
  if x is not None and y is not None:rules.append((sorted(set(x+y)),'@bottom'))
users=collections.defaultdict(list)
for i,(b,h) in enumerate(rules):
 for c in b:users[c].append(i)
queue=collections.deque(range(len(rules)));queued=set(queue)
while queue:
 i=queue.popleft();queued.remove(i);b,h=rules[i];bits=full
 for c in b:bits&=values[c]
 if bits & ~values[h]:
  values[h]|=bits
  for j in users[h]:
   if j not in queued:queued.add(j);queue.append(j)
rows=collections.defaultdict(list);unknown_subjects=set()
for q,t in answer['subsumptions']:
 if q in iri_to_name:rows[iri_to_name[q]].append(iri_to_name.get(t))
 else:unknown_subjects.add(q)
unsat={iri_to_name.get(q) for q in answer['unsatisfiable']}
affected=set(json.loads(a.affected.read_text())['affected_names']);proved=[];unproved=[]
for i,q in enumerate(queries):
 if q not in affected:continue
 bit=1<<i
 if q not in iri_to_name.values():unproved.append(q);continue
 ok=bool(values['@bottom']&bit) or (q not in unsat and all(t is not None and values[t]&bit for t in rows[q]))
 (proved if ok else unproved).append(q)
fresh=json.loads(a.fresh_answer.read_text())
if 'result' in fresh:fresh=fresh['result']
assert fresh['consistent'] and fresh['dropped']==0
old_public=collections.defaultdict(set);new_public=collections.defaultdict(set)
for q,t in answer['subsumptions']:old_public[q].add(t)
for q,t in fresh['subsumptions']:new_public[q].add(t)
old_unsat=set(answer['unsatisfiable']);new_unsat=set(fresh['unsatisfiable'])
name_to_iri={name:iri for iri,name in iri_to_name.items()}
for q in proved:
 iri=name_to_iri[q]
 assert old_public[iri]==new_public[iri] and (iri in old_unsat)==(iri in new_unsat),q
result=dict(diagnostic_only=True,affected=len(affected),named_horn_rules=len(rules),rows_with_named_horn_support=len(proved),remaining_rows=len(unproved),proved_names=proved,remaining_names=unproved,unknown_public_subjects=len(unknown_subjects),all_supported_rows_match_fresh=True,seconds=time.monotonic()-start,inputs={name:hashlib.sha256(getattr(a,name).read_bytes()).hexdigest() for name in ['old','new','source','answer','affected','fresh_answer']},scope='Feasibility only. No production row is reused on this evidence; source coverage and IRI binding remain requirements.')
a.output.write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items() if k not in ['proved_names','remaining_names','inputs']})
