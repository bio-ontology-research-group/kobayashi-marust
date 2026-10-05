import json,pathlib,collections
import argparse
parser=argparse.ArgumentParser(description='Diagnostic abstraction only; never authorizes retained publication.')
parser.add_argument('old',type=pathlib.Path);parser.add_argument('new',type=pathlib.Path)
parser.add_argument('--assume-all-roles',action='store_true')
args=parser.parse_args()
a=json.loads(args.old.read_text());b=json.loads(args.new.read_text());can=lambda x:json.dumps(x,sort_keys=True);changed=[json.loads(x) for x in set(map(can,a['clauses']))-set(map(can,b['clauses']))]
def pred(atom):
 if atom['kind']=='concept':return 'c:'+atom['concept']
 if atom['kind']=='role':return 'r:'+atom['role']
 return None
reverse=collections.defaultdict(set);forward=collections.defaultdict(set);glob=set()
for clause in a['clauses']+b['clauses']:
 body={pred(x) for x in clause['body']}-{None};allp={pred(x) for x in clause['head']+clause['body']}-{None}
 if not body:glob.update(allp)
 for u in body:
  forward[u].update(allp)
  for v in allp:reverse[v].add(u)
def closure(graph,seeds):
 seen=set(seeds);q=list(seeds)
 while q:
  for x in graph.get(q.pop(),()):
   if x not in seen:seen.add(x);q.append(x)
 return seen
seeds={pred(x) for c in changed for x in c['body']}-{None};reach=closure(reverse,seeds);globalreach=closure(forward,glob|{'c:owl:Thing','c:⊤'})
concepts=sorted({pred(x) for c in a['clauses']+b['clauses'] for x in c['body']+c['head'] if x['kind']=='concept'})
values={x:1<<i for i,x in enumerate(concepts)};allbits=(1<<len(concepts))-1
for x in ['c:owl:Thing','c:⊤','c:http://www.w3.org/2002/07/owl#Thing']:values[x]=allbits
rules=[];users=collections.defaultdict(list)
for c in a['clauses']+b['clauses']:
 body={pred(x) for x in c['body']}-{None};head={pred(x) for x in c['head']}-{None}
 idx=len(rules);rules.append((body,head))
 for x in body:users[x].append(idx)
for row in a['rbox']:
 tag,*args=row
 if tag in ('chain','chain-n'):
  body={'r:'+x for x in args[:-1]};head={'r:'+args[-1]}
 elif tag=='subrole':body={'r:'+args[0]};head={'r:'+args[1]}
 elif tag=='inverse':
  for u,v in [(args[0],args[1]),(args[1],args[0])]:
   idx=len(rules);rules.append(({'r:'+u},{'r:'+v}));users['r:'+u].append(idx)
  continue
 elif tag in ('domain','range'):body={'r:'+args[0]};head={'c:'+args[1]}
 elif tag=='transitive':continue
 else:raise ValueError(row)
 idx=len(rules);rules.append((body,head))
 for x in body:users[x].append(idx)
if args.assume_all_roles:
 for symbol in users:
  if symbol.startswith('r:'):values[symbol]=allbits
q=collections.deque(range(len(rules)));queued=set(q)
while q:
 idx=q.popleft();queued.discard(idx);body,head=rules[idx];bits=allbits
 for x in body:
  bits&=values.get(x,0)
  if not bits:break
 if not bits:continue
 for x in head:
  old=values.get(x,0);new=old|bits
  if new!=old:
   values[x]=new
   for j in users[x]:
    if j not in queued:queued.add(j);q.append(j)
active=allbits
for x in seeds:active&=values.get(x,0)
names=[x[2:] for i,x in enumerate(concepts) if active>>i&1]
print(json.dumps({'diagnostic_only':True,'all_concept_seeds':len(concepts),'affected_concepts':len(names),'concepts':names,'limitation':'Typed RBox included; nominal, datatype, rule, cardinality, and publication proof coverage not established. Never used to retain production results.'},indent=2))
