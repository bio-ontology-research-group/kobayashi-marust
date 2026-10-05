"""Cross-reasoner source-justification pilot using fixed EL entailments."""
import argparse,hashlib,json,pathlib,subprocess
p=argparse.ArgumentParser();p.add_argument('--inventory',type=pathlib.Path,required=True);p.add_argument('--sources',type=pathlib.Path,required=True);p.add_argument('--output',type=pathlib.Path,required=True);p.add_argument('--baseline',required=True);a=p.parse_args()
art={r['id']:r for r in json.loads(a.inventory.read_text())['artifacts']};generator=art[a.baseline];verifier=art['jfact' if a.baseline=='hermit' else 'hermit'];root=a.output/a.baseline;root.mkdir(parents=True,exist_ok=False)
for r in [generator,verifier]:assert hashlib.sha256(pathlib.Path(r['path']).read_bytes()).hexdigest()==r['sha256']
report={'generator':a.baseline,'verifier':verifier['id'],'runtime_sha256':generator['sha256'],'verifier_sha256':verifier['sha256'],'scope':'Bounded semantic pilot, not performance results','cases':[],'commands':[]}
def run(cmd,label):
 report['commands'].append(cmd)
 try:r=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=40)
 except subprocess.TimeoutExpired as e:raise RuntimeError('timeout: '+label) from e
 (root/(label+'.stdout')).write_bytes(r.stdout);(root/(label+'.stderr')).write_bytes(r.stderr)
 if r.returncode:raise RuntimeError(label+' exit '+str(r.returncode)+': '+r.stderr.decode(errors='replace')[-2500:])
java=['java','-Xmx1g','-XX:ActiveProcessorCount=1']
cases=[('chain','SubClassOf(:A :B) SubClassOf(:B :C) SubClassOf(:C :B)','urn:v145:C'),('existential','SubClassOf(:A ObjectSomeValuesFrom(:r :B)) SubClassOf(:B :C) SubClassOf(ObjectSomeValuesFrom(:r :C) :D)','urn:v145:D')]
try:
 for label,r,file in [('generator',generator,'EntailmentExplanation.java'),('verifier',verifier,'VerifyJustification.java')]:
  classes=root/label;classes.mkdir();run(['javac','--release','11','-cp',r['path'],'-d',str(classes),str(a.sources/file)],'compile-'+label)
 for name,axioms,sup in cases:
  source=root/(name+'.ofn');source.write_text('Prefix(:=<urn:v145:>)\nOntology(Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) Declaration(Class(:D)) Declaration(ObjectProperty(:r))\n'+axioms+')\n')
  result=root/(name+'.explanation.tsv');module=root/(name+'.module.ofn');receipt=root/(name+'.verification.tsv')
  run(java+['-cp',str(root/'generator')+':'+generator['path'],'org.kmbenchmark.EntailmentExplanation',generator['factory'],str(source),'urn:v145:A',sup,str(module),str(result)]+(['hierarchy-deletion'] if a.baseline=='whelk' else []),'generate-'+name)
  assert 'M\tentailed\ttrue\n' in result.read_text()
  run(java+['-cp',str(root/'verifier')+':'+verifier['path'],'org.kmbenchmark.VerifyJustification',verifier['factory'],str(source),str(result)+'.ofn','urn:v145:A',sup,str(receipt)],'verify-'+name)
  report['cases'].append({'name':name,'independent_verification':receipt.read_text(),'generation':result.read_text(),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'justification_sha256':hashlib.sha256(pathlib.Path(str(result)+'.ofn').read_bytes()).hexdigest()})
 report['status']='passed'
except Exception as e:report['status']='pilot_failed';report['error']=str(e)
(root/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k in ['generator','verifier','status','error']}))
