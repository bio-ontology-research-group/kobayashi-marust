"""Exercise one pinned Konclude process through TBox retraction and restoration."""
import json, os, subprocess, sys
from pathlib import Path
import xml.etree.ElementTree as ET
from measure_classification import digest
import tree_watchdog as watchdog
root, job = Path(sys.argv[1]), sys.argv[2]
out = root / ('konclude-owllink-pilot-' + job)
out.mkdir(exist_ok=False)
row = next(r for r in json.loads((root/'artifact-inventory-53198415.json').read_text())['artifacts'] if r['id']=='konclude')
assert digest(row['path']) == row['sha256']
axiom = '<owl:SubClassOf><owl:Class IRI="urn:pilot:B"/><owl:Class IRI="urn:pilot:C"/></owl:SubClassOf>'
request = '<RequestMessage xmlns="http://www.owllink.org/owllink#" xmlns:owl="http://www.w3.org/2002/07/owl#"><CreateKB kb="urn:pilot:kb"/><Tell kb="urn:pilot:kb">'
request += ''.join('<owl:Declaration><owl:Class IRI="urn:pilot:'+x+'"/></owl:Declaration>' for x in 'ABC')
request += '<owl:SubClassOf><owl:Class IRI="urn:pilot:A"/><owl:Class IRI="urn:pilot:B"/></owl:SubClassOf>'+axiom+'</Tell>'
query = '<IsKBSatisfiable kb="urn:pilot:kb"/><GetSubClassHierarchy kb="urn:pilot:kb"/>'
request += query+'<Retract kb="urn:pilot:kb">'+axiom+'</Retract>'+query+'<Tell kb="urn:pilot:kb">'+axiom+'</Tell>'+query+'</RequestMessage>'
(out/'request.xml').write_text(request)
command=[row['path'],'owllinkfile','-w','1','-i',str(out/'request.xml'),'-o',str(out/'response.xml')]
watchdog.protect_supervisor()
with (out/'stdout').open('wb') as stdout,(out/'stderr').open('wb') as stderr:
 p=subprocess.Popen(command,stdout=stdout,stderr=stderr,env=dict(os.environ,LD_LIBRARY_PATH=str(Path(row['path']).parent/'runtime-lib')),preexec_fn=watchdog.child_preexec)
 result=watchdog.monitor(p,timeout=240,memcap_bytes=20480*1024**2)
record={'status':result.status,'exit_code':p.returncode,'wall_s':result.wall_s,'peak_bytes':result.peak_bytes,'artifact_sha256':row['sha256'],'runner_sha256':digest(__file__)}
try:
 assert result.status=='ok' and p.returncode==0
 tree=ET.parse(out/'response.xml').getroot()
 local=lambda tag:tag.rsplit('}',1)[-1]
 assert not any('Error' in local(e.tag) for e in tree.iter()),'OWLlink error response'
 hierarchies=[e for e in tree.iter() if local(e.tag)=='ClassHierarchy']
 booleans=[e.attrib.get('result') for e in tree.iter() if local(e.tag)=='BooleanResponse']
 assert booleans==['true']*3,booleans
 assert len(hierarchies)==3,len(hierarchies)
 entails=[]
 for h in hierarchies:
  edges={}
  for pair in h:
   if local(pair.tag)!='ClassSubClassesPair':continue
   parents=[c.attrib['IRI'] for c in pair[0]]
   for group in pair[1]:
    for child in group:edges.setdefault(child.attrib['IRI'],set()).update(parents)
  seen=set();todo=['urn:pilot:A']
  while todo:
   node=todo.pop()
   if node in seen:continue
   seen.add(node);todo.extend(edges.get(node,()))
  entails.append('urn:pilot:C' in seen)
 assert entails==[True,False,True],entails
 record.update(status='retained_retraction_restore_verified',entails_A_C=entails,internal_reuse='not inferred from persistent process')
except Exception as error:record.update(status='contract_failed',error=str(error))
(out/'record.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
