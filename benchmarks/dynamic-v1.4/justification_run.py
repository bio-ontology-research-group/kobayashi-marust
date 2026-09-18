#!/usr/bin/env python3
"""One frozen query, common oracle and native extraction, independent verification."""
import argparse,hashlib,json,os,signal,subprocess,time
from pathlib import Path
FACTORIES={'hermit':'org.semanticweb.HermiT.ReasonerFactory','jfact':'uk.ac.manchester.cs.jfact.JFactFactory','openllet':'openllet.owlapi.OpenlletReasonerFactory','elk':'org.semanticweb.elk.owlapi.ElkReasonerFactory','whelk':'org.geneontology.whelk.owlapi.WhelkOWLReasonerFactory'}

def process_tree_rss(pid):
 # Read kernel process parent IDs and resident pages; includes Java, KM workers,
 # timeout and wrappers. Sampling misses peaks shorter than the 50ms interval.
 parents={};rss={}
 for entry in Path('/proc').iterdir():
  if not entry.name.isdigit():continue
  try:
   fields=(entry/'stat').read_text().rsplit(')',1)[1].split()
   child=int(entry.name);parents[child]=int(fields[1]);rss[child]=int(fields[21])*os.sysconf('SC_PAGE_SIZE')
  except (OSError,ValueError,IndexError):continue
 active={pid}
 while True:
  new={child for child,parent in parents.items() if parent in active}-active
  if not new:break
  active.update(new)
 return sum(rss.get(child,0) for child in active)

def run(cmd,out,timeout=600):
 out.mkdir(parents=True,exist_ok=True)
 env={k:v for k,v in os.environ.items() if not k.startswith('KM_')};env['KM_THREADS']='1';env['KM_CENTRAL_TIME_CAP']='240'
 start=time.monotonic()
 with (out/'stdout.log').open('w') as stdout,(out/'stderr.log').open('w') as stderr:
  p=subprocess.Popen(['/usr/bin/time','-v','-o',str(out/'process.time'),'timeout','-k','5',str(timeout),*map(str,cmd)],stdout=stdout,stderr=stderr,env=env,start_new_session=True)
  peak=0;memout=False
  while p.poll() is None:
   peak=max(peak,process_tree_rss(p.pid))
   if peak>20*1024**3:
    memout=True
    try:os.killpg(p.pid,signal.SIGTERM)
    except ProcessLookupError:pass
    try:p.wait(timeout=5)
    except subprocess.TimeoutExpired:
     try:os.killpg(p.pid,signal.SIGKILL)
     except ProcessLookupError:pass
     p.wait()
    break
   time.sleep(.05)
 (out/'exit-code').write_text(str(p.returncode)+'\n')
 (out/'invocation.json').write_text(json.dumps({'command':list(map(str,cmd)),'elapsed_s':time.monotonic()-start,'exit_code':p.returncode,'sampled_peak_process_tree_rss_bytes':peak,'rss_sample_period_s':0.05,'memory_limit_bytes':20*1024**3,'status':'memout' if memout else ('ok' if p.returncode==0 else ('timeout' if p.returncode==124 else 'error')),'job':os.environ.get('SLURM_JOB_ID')},indent=2)+'\n')
 return p.returncode

def main(a):
 task=json.loads(a.task.read_text());out=a.output
 out.mkdir(parents=True,exist_ok=True)
 if (out/'task.json').exists():raise ValueError('refusing to overwrite prior task output')
 (out/'task.json').write_text(json.dumps(task,indent=2)+'\n')
 if task.get('driver_manifest'):
  manifest=Path(task['driver_manifest'])
  if hashlib.sha256(manifest.read_bytes()).hexdigest()!=task['driver_manifest_sha256']:raise ValueError('driver manifest changed')
  for filename,expected in json.loads(manifest.read_text()).items():
   if hashlib.sha256(Path(filename).read_bytes()).hexdigest()!=expected:raise ValueError('driver/runtime mismatch: '+filename)
  (out/'driver-manifest.json').write_bytes(manifest.read_bytes())
 input=Path(task['input'])
 if 'sha256' in task and hashlib.sha256(input.read_bytes()).hexdigest()!=task['sha256']:raise ValueError('frozen source hash mismatch')
 sub=task['sub'];sup=task['super'];binary=task['km'];runtime=Path(task['runtime']);classes=task['classes']
 java=['java','-XX:ActiveProcessorCount=1','-Xmx16g','-Delk.reasoner.number_of_workers=1']
 def command(reasoner,operation,target,support_or_limit):
  jar=reasoner if reasoner in FACTORIES else 'hermit'
  oracle=task['konclude'] if reasoner=='konclude' else binary
  factory=FACTORIES.get(reasoner,'km:'+oracle)
  return java+['-cp',classes+':'+str(runtime/f'classifier-{jar}.jar'),'org.kmbenchmark.JustificationBenchmark',operation,factory,str(input),sub,sup,str(target),str(support_or_limit)]
 arms=['km-native','km-common','hermit-common','jfact-common','openllet-common']
 if task.get('library'):arms+=['hermit-library','jfact-library','openllet-library']
 if task.get('konclude'):arms+=['konclude-common']
 if task['el']:arms+=['elk-common','whelk-common']
 arms=task.get('arms',arms)
 rotation=task.get('repetition',0)%len(arms);arms=arms[rotation:]+arms[:rotation]
 for limit in task.get('limits',[1,10,100]):
  for arm in arms:
   dest=out/str(limit)/arm
   if arm=='km-native':
    rc=run([binary,'explain','--max-axioms','1000000','--max-source-bytes','1073741824','--max-checks','10000000','--max-justifications',str(limit),str(input),'subclass',sub,sup],dest)
    if rc==0:
     report=json.loads((dest/'stdout.log').read_text());(dest/'report.json').write_text(json.dumps(report)+'\n')
     for i,j in enumerate(report['justifications']):
      (dest/f'support-{i:03}.ofn').write_text('\n'.join(report['prefixDeclarations'])+'\nOntology(\n'+'\n'.join(ax['functionalSyntax'] for ax in j['axioms'])+'\n)\n')
   elif arm.endswith('-library'):
    reasoner=arm[:-8]
    rc=run(java+['-cp',classes+':'+str(runtime/('classifier-'+reasoner+'.jar')),'org.kmbenchmark.JustificationLibrary',FACTORIES[reasoner],str(input),sub,sup,str(dest),str(limit)],dest)
   else:rc=run(command(arm[:-7],'extract',dest,limit),dest)
   if rc:continue
   validator='jfact' if arm.startswith('hermit-') else 'hermit'
   target=dest/f'independent-{validator}'
   rc=run(command(validator,'verify',target,dest),target)
   if rc==0:(dest/'VERIFIED-RUN-COMPLETE').write_text('inspect verification.tsv for validity\n')
 out.mkdir(parents=True,exist_ok=True)
 (out/'task.json').write_text(json.dumps(task,indent=2)+'\n')
 (out/'source.sha256').write_text(hashlib.sha256(input.read_bytes()).hexdigest()+'\n')
 (out/'COMPLETE').write_text('all scheduled arms attempted\n')
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('task',type=Path);p.add_argument('output',type=Path);main(p.parse_args())
