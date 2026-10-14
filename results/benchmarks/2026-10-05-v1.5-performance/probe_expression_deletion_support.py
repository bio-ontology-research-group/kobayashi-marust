"""Read-only feasibility probe for retaining deletion rows with fresh expression-Horn proofs.
Not a production reuse certificate. Full source coverage and IRI binding need an
executable certificate before any such row can bypass complete reasoning.
"""
import argparse,collections,hashlib,json,re,time
from pathlib import Path
p=argparse.ArgumentParser()
for name in ['old','new','source','answer','affected','fresh_answer','output']:p.add_argument('--'+name,type=Path,required=True)
p.add_argument('--existential-monotonicity',action='store_true')
p.add_argument('--role-background',action='store_true')
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
# Every expression is an independent predicate except for sound conjunction
# rules and explicit source inclusions. No existential is identified with its
# filler at the same individual. Optional lifting uses only global filler
# subsumptions: B <= C entails exists r.B <= exists r.C for the same role.
ids={};expressions=[];rules=[];exists_by_filler=collections.defaultdict(dict)
def intern(c):
 k=key(c)
 if k in ids:return ids[k]
 i=len(ids);ids[k]=i;expressions.append(c)
 if c in ['Top','Bottom']:return i
 assert isinstance(c,dict) and len(c)==1,c
 if 'Name' in c:return i
 if 'And' in c:
  children=[intern(x) for x in c['And']]
  rules.append((children,i));rules.extend(([i],x) for x in children)
 elif 'Exists' in c:
  role,filler=c['Exists'];f=intern(filler)
  exists_by_filler[f].setdefault(key(role),[]).append(i)
 else:raise ValueError('unsupported source expression: '+k)
 return i
for q in queries:intern({'Name':q})
top=intern('Top');bottom=intern('Bottom');rules.append(([],top))
for ax in new['source_axioms']:
 left,right=intern(ax['left']),intern(ax['right'])
 if ax['kind']=='sub-class':rules.append(([left],right))
 elif ax['kind']=='equivalent':rules.extend([([left],right),([right],left)])
 elif ax['kind']=='disjoint':rules.append(([left,right],bottom))
 else:raise ValueError(ax['kind'])
role_chains=collections.defaultdict(set)
role_head={i:(key(c['Exists'][0]),ids[key(c['Exists'][1])]) for i,c in enumerate(expressions)
           if isinstance(c,dict) and 'Exists' in c}
if a.role_background:
 role_key=lambda r:key({'Name':new['roles'][r]})
 for r,s,t in new['chains']:role_chains[role_key(r),role_key(s)].add(role_key(t))
 for r in new['transitive']:role_chains[role_key(r),role_key(r)].add(role_key(r))
 for r,c in new['role_domains']:
  target=intern({'Name':new['concepts'][c]})
  rules.extend(([e],target) for e,(role,filler) in role_head.items() if role==role_key(r))
 # The reflexive filler inclusion supplies the direct nested-existential case.
 for inner,(s,filler) in role_head.items():
  for r,lefts in exists_by_filler.get(inner,{}).items():
   for t in role_chains[r,s]:
    for left in lefts:
     for right in exists_by_filler.get(filler,{}).get(t,[]):rules.append(([left],right))
full=(1<<len(ids))-1; bits=[1<<i for i in range(len(ids))]
users=collections.defaultdict(list)
for i,(body,head) in enumerate(rules):
 for c in body:users[c].append(i)
queue=collections.deque(range(len(rules)));queued=set(queue);lifted=set()
def add_unary(left,right):
 if (left,right) in lifted:return
 lifted.add((left,right));assert len(lifted)<500000,'diagnostic edge budget'
 i=len(rules);rules.append(([left],right));users[left].append(i);queue.append(i);queued.add(i)
while queue:
 i=queue.popleft();queued.remove(i);body,head=rules[i];mask=full
 for c in body:mask&=bits[c]
 delta=mask & ~bits[head]
 if not delta:continue
 bits[head]|=delta
 for j in users[head]:
  if j not in queued:queued.add(j);queue.append(j)
 if (a.existential_monotonicity and (head in exists_by_filler or head==bottom)) or (a.role_background and head in role_head):
  while delta:
   bit=delta & -delta;delta-=bit;sub=bit.bit_length()-1
   if sub not in exists_by_filler:continue
   for role,lefts in exists_by_filler[sub].items():
    rights=[]
    if a.existential_monotonicity:
     rights.extend([bottom] if head==bottom else exists_by_filler[head].get(role,[]))
    if a.role_background and head in role_head:
     inner_role,filler=role_head[head]
     for outer_role in role_chains[role,inner_role]:
      rights.extend(exists_by_filler.get(filler,{}).get(outer_role,[]))
    for left in lefts:
     for right in rights:add_unary(left,right)
values={q:bits[ids[key({'Name':q})]] for q in queries}
values['@bottom']=bits[bottom]
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
result=dict(diagnostic_only=True,existential_monotonicity=a.existential_monotonicity,role_background=a.role_background,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),expressions=len(ids),lifted_edges=len(lifted),affected=len(affected),horn_rules=len(rules),rows_with_horn_support=len(proved),remaining_rows=len(unproved),proved_names=proved,remaining_names=unproved,unknown_public_subjects=len(unknown_subjects),all_supported_rows_match_fresh=True,seconds=time.monotonic()-start,inputs={name:hashlib.sha256(getattr(a,name).read_bytes()).hexdigest() for name in ['old','new','source','answer','affected','fresh_answer']},scope='Feasibility only. No production row is reused on this evidence; source coverage and IRI binding remain requirements.')
a.output.write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items() if k not in ['proved_names','remaining_names','inputs']})
