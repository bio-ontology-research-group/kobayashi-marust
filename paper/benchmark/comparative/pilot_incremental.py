"""Bounded update semantics and shared-writer regression pilot for Java baselines."""
import argparse,hashlib,json,pathlib,subprocess
p=argparse.ArgumentParser();p.add_argument('--inventory',type=pathlib.Path,required=True);p.add_argument('--sources',type=pathlib.Path,required=True);p.add_argument('--output',type=pathlib.Path,required=True);p.add_argument('--baseline',required=True);args=p.parse_args()
row=next(r for r in json.loads(args.inventory.read_text())['artifacts'] if r['id']==args.baseline)
jar=pathlib.Path(row['path']);assert hashlib.sha256(jar.read_bytes()).hexdigest()==row['sha256']
root=args.output/args.baseline;root.mkdir(parents=True,exist_ok=False);classes=root/'classes';classes.mkdir()
prefix='Prefix(:=<urn:v145:>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\nOntology(Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) Declaration(NamedIndividual(:i))\n'
axioms=['SubClassOf(:A :B) SubClassOf(:B :C)','SubClassOf(:A :B)','SubClassOf(:A :B) SubClassOf(:B :C) SubClassOf(:C owl:Nothing)','SubClassOf(:A :B) SubClassOf(:B :C) SubClassOf(:C owl:Nothing) ClassAssertion(:A :i)','SubClassOf(:A :B) SubClassOf(:B :C)']
paths=[]
for i,a in enumerate(axioms):
 f=root/f'{i:03}.ofn';f.write_text(prefix+a+'\n)\n');paths.append(str(f))
commands=[]
def run(cmd,name):
 commands.append(cmd)
 try:r=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=40)
 except subprocess.TimeoutExpired as e:raise RuntimeError('pilot_timeout: '+name) from e
 (root/(name+'.stdout')).write_bytes(r.stdout);(root/(name+'.stderr')).write_bytes(r.stderr)
 if r.returncode:raise RuntimeError(name+' exit '+str(r.returncode)+': '+r.stderr.decode(errors='replace')[-4000:])
 return r
report={'baseline':args.baseline,'runtime_sha256':row['sha256'],'mode':'OWLAPI retained object and flush; internal incremental reuse is not assumed','scope':'semantic pilot, not measured benchmark','sources':{f:hashlib.sha256((args.sources/f).read_bytes()).hexdigest() for f in ['FullIriClassifier.java','IncrementalClassifier.java']},'commands':commands,'revisions':[]}
try:
 run(['javac','--release','11','-cp',str(jar),'-d',str(classes),str(args.sources/'FullIriClassifier.java'),str(args.sources/'IncrementalClassifier.java')],'compile')
 cp=str(classes)+':'+str(jar);java=['java','-Xmx1g','-XX:ActiveProcessorCount=1'];factory=row['factory']
 run(java+['-cp',cp,'org.kmbenchmark.IncrementalClassifier',factory,str(root/'retained'),*paths],'retained')
 for i,path in enumerate(paths):
  fresh=root/f'fresh-{i}.tsv';old=root/f'original-{i}.tsv'
  run(java+['-cp',cp,'org.kmbenchmark.FullIriClassifier',factory,path,str(fresh)],'fresh-'+str(i))
  run(java+['-jar',str(jar),factory,path,str(old)],'original-'+str(i))
  raw=(root/'retained'/f'{i:03}.taxonomy.tsv').read_bytes();assert raw==fresh.read_bytes()==old.read_bytes(),('taxonomy_difference',i)
  lines=raw.decode().splitlines();assert lines[-1]=='Z\tcomplete'
  assert ('C\tfalse' in lines)==(i==3),(i,'consistency')
  assert ('S\turn:v145:A\turn:v145:C' in lines)==(i in [0,4]),(i,'updated consequence')
  assert {l for l in lines if l.startswith('U\t')}==({'U\turn:v145:'+x for x in 'ABC'} if i==2 else set()),(i,'unsatisfiable classes')
  report['revisions'].append({'revision':i,'fresh_equals_retained':True,'writer_equals_original':True,'expected_semantics':True,'taxonomy_sha256':hashlib.sha256(raw).hexdigest()})
 report['status']='passed'
except Exception as e:
 report['status']='pilot_failed';report['error']=str(e)
(root/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'baseline':args.baseline,'status':report['status'],'error':report.get('error')}))
