import json,hashlib,shutil,subprocess,os
from pathlib import Path
base=Path('/ibex/scratch/hohndor/km/dynamic-benchmark-20260917').resolve()
assets=base/'justification-stream-v4-stage'
specs=[('baseline-original','justification-driver-v3',240),('baseline-pure-dl','justification-pure-dl-v1',60),('final-original','justification-v142-original',240),('final-pure-dl','justification-v142-pure-dl',60)]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[]
for label,oldname,count in specs:
 old=base/oldname; new=base/('justification-stream-v4b-'+label)
 assert not new.exists(),str(new)
 new.mkdir(); manifest=json.loads((old/'justification-main/driver-manifest.json').read_text())
 for name,h in manifest.items():
  p=Path(name);assert sha(p)==h, name
  if str(p).startswith(str(old)+"/"):
   dst=new/p.relative_to(old);dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dst)
 for name in ['JustificationBenchmark.java','JustificationStreamRegression.java']:
  shutil.copy2(assets/name,new/name)
 classes=new/'justification-main/classes'
 jar=Path('/ibex/scratch/hohndor/km/paper-benchmark-20260830/runtimes/classifier-hermit.jar')
 subprocess.run(['javac','-cp',str(jar),'-d',str(classes)]+[str(p) for p in sorted(new.glob('*.java'))],check=True)
 subprocess.run(['java','-cp',str(classes)+':'+str(jar),'JustificationStreamRegression'],check=True)
 updated={}
 for name,h in manifest.items():
  p=Path(name);p=new/p.relative_to(old) if str(p).startswith(str(old)+"/") else p
  updated[str(p)]=sha(p)
 for p in classes.rglob('*.class'):updated[str(p)]=sha(p)
 updated[str(new/'JustificationStreamRegression.java')]=sha(new/'JustificationStreamRegression.java')
 mp=new/'justification-main/driver-manifest.json';mp.write_text(json.dumps(updated,indent=2,sort_keys=True)+'\n')
 td=new/'justification-main/tasks';td.mkdir()
 (new/'justification-main/task-count.txt').write_text(str(count)+'\n')
 if (old/'justification-main/panel-status.json').exists():shutil.copy2(old/'justification-main/panel-status.json',new/'justification-main/panel-status.json')
 originals=sorted((old/'justification-main/tasks').glob('*.json'));assert len(originals)==count
 for f in originals:
  t=json.loads(f.read_text());t['prior_task_sha256']=sha(f);t['prior_driver_manifest_sha256']=t['driver_manifest_sha256']
  t['arms']=['km-common'];t['driver_manifest']=str(mp);t['driver_manifest_sha256']=sha(mp);t['classes']=str(classes)
  t['konclude']=str(new/'konclude_oracle.py');t['harness_revision']='stream-v4'
  (td/f.name).write_text(json.dumps(t,indent=2)+'\n')
 receipts.append(dict(label=label,root=str(new),tasks=count,attempts=count*3,driver_manifest_sha256=sha(mp)))
 # Only original-panel adapters need repeat probes on HAO; source/query identical across builds.
 if label.endswith('-original'):
  t=next(json.loads(f.read_text()) for f in td.glob('*.json') if (lambda t:t['ontology']=='hao' and t['query_id']=='q002' and t['track']=='module' and t['repetition']==0)(json.loads(f.read_text())))
  empty=new/'probe-empty';empty.mkdir()
  for kind,sub,sup,expected in [('positive',t['sub'],t['super'],'true'),('negative','http://www.w3.org/2002/07/owl#Thing','http://www.w3.org/2002/07/owl#Nothing','false')]:
   out=new/('probe-'+kind)
   cmd=['java','-XX:ActiveProcessorCount=1','-Xmx16g','-cp',str(classes)+':'+str(jar),'org.kmbenchmark.JustificationBenchmark','verify','km:'+t['km'],t['input'],sub,sup,str(out),str(empty)]
   subprocess.run(cmd,check=True,timeout=300)
   assert (out/'source-entailed.txt').read_text().strip()==expected
  pilot=json.loads((td/'0000.json').read_text());pilot['limits']=[1]
  pp=new/'pilot.json';pp.write_text(json.dumps(pilot,indent=2)+'\n')
  subprocess.run(['python3',str(new/'justification_run.py'),str(pp),str(new/'pilot-result')],check=True,cwd=new,timeout=1300)
  import importlib.util
  sp=importlib.util.spec_from_file_location('auditor',new/'audit_justification_main.py');mod=importlib.util.module_from_spec(sp);sp.loader.exec_module(mod)
  result=mod.audit(pilot,new/'pilot-result/1/km-common',1,'km-common');assert result['status']=='correct',result
  (new/'pilot-audit.json').write_text(json.dumps(result,indent=2)+'\n')
(assets/'stage-receipt.json').write_text(json.dumps(receipts,indent=2)+'\n')
(assets/'PASS').write_text('Four manifests staged; pinned stream regression and positive/negative HAO plus independent MMO support probes passed.\n')
