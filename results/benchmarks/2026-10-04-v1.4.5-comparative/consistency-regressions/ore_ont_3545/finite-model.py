"""Check a finite object model with standard OWL 2 / XSD 1.1 datatype domains."""
from pathlib import Path
from collections import defaultdict,Counter
import re,json,hashlib
root=Path(__file__).parent;source=root/'ore_ont_3545.owl';text=source.read_text();prefix={m[1]:m[2] for m in re.finditer(r'Prefix\(([^=]+)=<([^>]+)>\)',text)}
def iri(t):
 if t.startswith('<'):return t[1:-1]
 a,b=t.split(':',1);return prefix[a+':']+b
def parse(line):
 ts=re.findall(r'"(?:[^"\\]|\\.)*"(?:\^\^(?:<[^>]*>|[^\s()]+)|@[\w-]+)?|<[^>]*>|[^\s()]+|[()]',line)
 def expr(i):
  name=ts[i];i+=1
  if i<len(ts) and ts[i]=='(':
   args=[];i+=1
   while ts[i]!=')':
    x,i=expr(i);args.append(x)
   return (name,args),i+1
  return name,i
 result,end=expr(0);assert end==len(ts),(line,ts);return result
OWL='http://www.w3.org/2002/07/owl#';XSD='http://www.w3.org/2001/XMLSchema#'
classes=set();individuals=set();edges=defaultdict(set);sub=[];inverse=[];symmetric=set();transitive=set();functional=set();ifunctional=set();data=defaultdict(set);dfunc=set();ranges={};counts=Counter();class_constraints=[]
for line in text.splitlines():
 line=line.strip()
 if not line or line.startswith(('Prefix(','Ontology(')) or line==')':continue
 kind,args=parse(line);counts[kind]+=1
 if kind=='Declaration':
  k,a=args[0]
  if k=='Class':classes.add(iri(a[0]))
  elif k=='NamedIndividual':individuals.add(iri(a[0]))
  else:assert k in ['ObjectProperty','DataProperty','AnnotationProperty'],k
 elif kind.startswith('Annotation'):continue
 elif kind in ['SubClassOf','ClassAssertion','ObjectPropertyDomain','ObjectPropertyRange','DataPropertyDomain']:
  if kind=='SubClassOf':class_constraints.extend(args)
  elif kind=='ClassAssertion':class_constraints.append(args[0]);individuals.add(iri(args[1]))
  else:class_constraints.append(args[1])
 elif kind=='ObjectPropertyAssertion':
  r,a,b=map(iri,args);edges[r].add((a,b));individuals.update([a,b])
 elif kind=='SubObjectPropertyOf':sub.append(tuple(map(iri,args)))
 elif kind=='InverseObjectProperties':inverse.append(tuple(map(iri,args)))
 elif kind=='SymmetricObjectProperty':symmetric.add(iri(args[0]))
 elif kind=='TransitiveObjectProperty':transitive.add(iri(args[0]))
 elif kind=='FunctionalObjectProperty':functional.add(iri(args[0]))
 elif kind=='InverseFunctionalObjectProperty':ifunctional.add(iri(args[0]))
 elif kind=='FunctionalDataProperty':dfunc.add(iri(args[0]))
 elif kind=='DataPropertyRange':
  r,t=map(iri,args);assert r not in ranges or ranges[r]==t;ranges[r]=t
 elif kind=='DataPropertyAssertion':
  prop,subject,literal=args;m=re.fullmatch(r'("(?:[^"\\]|\\.)*")\^\^(.+)',literal);assert m,literal
  lexical=json.loads(m[1]);dtype=iri(m[2]);assert dtype in [XSD+'string',XSD+'anyURI'],dtype
  assert all(ord(c) in [9,10,13] or 0x20<=ord(c)<=0xD7FF or 0xE000<=ord(c)<=0xFFFD or 0x10000<=ord(c)<=0x10FFFF for c in lexical),'non-XML character'
  data[(iri(prop),iri(subject))].add((dtype,lexical));individuals.add(iri(subject))
 else:raise AssertionError(('unhandled axiom',kind))
def universal(c):
 if isinstance(c,str):
  name=iri(c);assert name!=OWL+'Nothing';classes.add(name);return
 kind,args=c;assert kind=='ObjectUnionOf' and args,c
 for x in args:universal(x)
for c in class_constraints:universal(c)
assert OWL+'Nothing' not in classes
assert not any(r.startswith(OWL) for r in edges),'builtin roles need a separate interpretation'
for iteration in range(100):
 size=sum(map(len,edges.values()))
 for a,b in sub:edges[b].update(edges[a])
 for a,b in inverse:
  edges[b].update((y,x) for x,y in list(edges[a]));edges[a].update((y,x) for x,y in list(edges[b]))
 for r in symmetric:edges[r].update((y,x) for x,y in list(edges[r]))
 for r in transitive:
  g=defaultdict(set)
  for a,b in edges[r]:g[a].add(b)
  additions=set()
  for a,bs in list(g.items()):
   for b in list(bs):additions.update((a,c) for c in g.get(b,set()))
  edges[r].update(additions)
 assert sum(map(len,edges.values()))<100000,'diagnostic bound'
 if sum(map(len,edges.values()))==size:break
else:raise AssertionError('closure bound')
for r in functional:
 g=defaultdict(set)
 for a,b in edges[r]:g[a].add(b)
 assert all(len(v)<=1 for v in g.values()),('functional collision',r)
for r in ifunctional:
 g=defaultdict(set)
 for a,b in edges[r]:g[b].add(a)
 assert all(len(v)<=1 for v in g.values()),('inverse functional collision',r)
for (r,subject),values in data.items():
 assert all(t==ranges[r] for t,v in values),(r,values)
 if r in dfunc:assert len(values)<=1,('data functional collision',r,subject,values)
assert individuals
model={'object_domain':sorted(individuals),'classes_interpreted_as_full_domain':sorted(classes),'object_properties':{r:sorted(values) for r,values in sorted(edges.items())},'data_assertions':[{'property':r,'subject':a,'values':sorted(values)} for (r,a),values in sorted(data.items())],'datatype_domains':'Standard OWL 2 datatype domains; not restricted to listed literal values'}
(root/'finite-model-witness.json').write_text(json.dumps(model,indent=2)+'\n')
result={'witness_sha256':hashlib.sha256((root/'finite-model-witness.json').read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'status':'consistent: finite object model verified with standard XSD 1.1 datatype domains','model':'All named individuals denote distinct domain elements; all named classes denote the full object domain; object roles are the closed asserted relations; data roles are exactly their assertions.','individuals':len(individuals),'classes':len(classes),'closed_object_edges':sum(map(len,edges.values())),'closure_iterations':iteration+1,'functional_object_role_sizes':{r:len(edges[r]) for r in functional|ifunctional},'axiom_counts':dict(counts),'datatype_basis':{'normative_owl_reference':'https://www.w3.org/TR/owl2-syntax/#References','xsd_anyuri_lexical_space':'https://www.w3.org/TR/xmlschema11-2/#anyURI','check':'Every string/anyURI literal consists solely of XML Char code points; every asserted datatype matches its property range. No functional data-property subject has multiple values. Datatype domains remain standard and disjoint; they are not restricted to the finite asserted values.'}}
(root/'finite-model.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
