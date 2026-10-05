import json,sys
from pathlib import Path
from measure_classification import digest
from measure_retained_konclude import measure
root,job=Path(sys.argv[1]),sys.argv[2]
out=root/('konclude-retained-pilot-'+job);out.mkdir(exist_ok=False)
row=next(r for r in json.loads((root/'artifact-inventory-53198415.json').read_text())['artifacts'] if r['id']=='konclude')
revisions=[]
for index,pairs in enumerate([[('A','B'),('B','C')],[('A','B')],[('A','B'),('B','C')],[],[('A','B'),('B','C')]]):
 p=out/f'{index:03}.owlxml'
 text='<Ontology xmlns="http://www.w3.org/2002/07/owl#">'
 text+=''.join('<Declaration><Class IRI="urn:pilot:'+x+'"/></Declaration>' for x in 'ABC')
 text+=''.join('<SubClassOf><Class IRI="urn:pilot:'+a+'"/><Class IRI="urn:pilot:'+b+'"/></SubClassOf>' for a,b in pairs)
 p.write_text(text+'</Ontology>')
 revisions.append({'path':str(p),'sha256':digest(p),'classes':['urn:pilot:'+x for x in 'ABC']})
record=measure(row,revisions,out/'session')
audit={'measurement_status':record['status'],'status':'failed'}
if record['status']=='executed_unvalidated':
 values=[]
 for i in range(5):
  taxonomy=json.loads((out/'session'/f'{i:03}.taxonomy.json').read_text())
  assert taxonomy['consistent'] is True
  seen=set();todo=['urn:pilot:A']
  while todo:
   n=todo.pop()
   if n in seen:continue
   seen.add(n);todo.extend(b for a,b in taxonomy['subsumptions'] if a==n)
  values.append('urn:pilot:C' in seen)
 audit.update(status='passed' if values==[True,False,True,False,True] else 'failed',entails_A_C=values)
(out/'audit.json').write_text(json.dumps(audit,indent=2)+'\n');print(json.dumps(audit))
