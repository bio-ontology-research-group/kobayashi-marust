import json,subprocess,sys
from pathlib import Path
from measure_justification_java import measure,digest
root,job=Path(sys.argv[1]),sys.argv[2]
out=root/('external-justification-pilot-'+job);out.mkdir(exist_ok=False)
inventory={r['id']:r for r in json.loads((root/'artifact-inventory-53198415.json').read_text())['artifacts']}
hermit=inventory['hermit'];assert digest(hermit['path'])==hermit['sha256']
sources=Path(__file__).parent;classes=out/'classes';classes.mkdir()
files=['ExportExplanationAxioms.java','SourceSignature.java','ConvertSyntax.java','VerifyJustification.java']
subprocess.run(['javac','--release','11','-cp',hermit['path'],'-d',str(classes)]+[str(sources/name) for name in files],check=True)
module=out/'module.ofn'
module.write_text('Ontology(Declaration(Class(<urn:pilot:A>)) Declaration(Class(<urn:pilot:B>)) Declaration(Class(<urn:pilot:C>)) SubClassOf(<urn:pilot:A> <urn:pilot:B>) SubClassOf(<urn:pilot:B> <urn:pilot:C>))\n')
reference=out/'consistency-reference.tsv'
subprocess.run(['java','-Xmx2g','-XX:ActiveProcessorCount=1','-jar',hermit['path'],hermit['factory'],str(module),str(reference)],check=True,timeout=60)
cert={'module_sha256':digest(module),'verifier':'hermit','taxonomy':str(reference),'taxonomy_sha256':digest(reference),'format':'owlapi-tsv','artifact_sha256':hermit['sha256']}
results=[]
for baseline in ['konclude','sequoia','more']:
 result=measure(inventory[baseline],hermit,classes,classes,module,digest(module),module,digest(module),'urn:pilot:A','urn:pilot:C',out/baseline,consistency_certificate=cert)
 results.append({'baseline':baseline,'status':result['status'],'error':result.get('error')})
(out/'summary.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results))
