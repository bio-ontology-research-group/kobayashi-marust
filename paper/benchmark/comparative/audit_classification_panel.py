"""Validate each frozen source's available outputs, then compare every reasoner pair.

Raw failures and missing outcomes remain visible. Run on a Slurm worker because
signature extraction and taxonomy closure can require substantial resources.
"""
import itertools
import json
from pathlib import Path
import subprocess
import sys
import tree_watchdog as watchdog
from measure_classification import digest
from compare_taxonomies import compare
from run_set import load as load_run_set

root,task,job=Path(sys.argv[1]),int(sys.argv[2]),sys.argv[3]
limit=int(sys.argv[4]) if len(sys.argv)>4 else 32
runs=load_run_set(root,sys.argv[5] if len(sys.argv)>5 else None)
sources=Path(__file__).parent
manifest=json.loads((sources/'classification-inputs.json').read_text())['inputs']
inputs=manifest[task*32:task*32+limit]
inventory={r['id']:r for r in json.loads((root/runs['inventory']).read_text())['artifacts']}
output=root/('classification-audit-'+job)/str(task);output.mkdir(parents=True,exist_ok=False)
summary={'status':'running','run_set':runs,'inputs':[],'runner_sha256':digest(__file__),'manifest_sha256':digest(sources/'classification-inputs.json')}
def publish(path,data):
 temporary=path.with_suffix('.part');temporary.write_text(json.dumps(data,indent=2)+'\n');temporary.replace(path)
def run(command,directory):
 directory.mkdir(parents=True,exist_ok=False)
 with (directory/'stdout').open('wb') as stdout,(directory/'stderr').open('wb') as stderr:
  p=subprocess.Popen(command,stdout=stdout,stderr=stderr,stdin=subprocess.DEVNULL,preexec_fn=watchdog.child_preexec)
  result=watchdog.monitor(p,timeout=600,memcap_bytes=20480*1024**2)
 receipt={'status':result.status,'exit_code':p.returncode,'wall_s':result.wall_s,'peak_bytes':result.peak_bytes,'command':command}
 publish(directory/'record.json',receipt)
 if result.status!='ok' or p.returncode:raise ValueError('audit worker failed: '+str(receipt))
watchdog.protect_supervisor()
hermit=inventory['hermit'];assert digest(hermit['path'])==hermit['sha256']
classes=output/'classes';classes.mkdir()
run(['javac','--release','11','-cp',hermit['path'],'-d',str(classes),str(sources/'SourceSignature.java')],output/'compile')
for source in inputs:
 destination=output/source['ontology'];destination.mkdir()
 case={'ontology':source['ontology'],'source_sha256':source['sha256'],'input_admission':source['input_admission'],'outcomes':{},'comparisons':[],'status':'running'}
 canonical={}
 try:
  assert digest(source['path'])==source['sha256'],'source changed'
  signature=destination/'signature.tsv'
  run(['java','-Xmx16g','-XX:ActiveProcessorCount=1','-cp',str(classes)+':'+hermit['path'],'org.kmbenchmark.SourceSignature',source['path'],str(signature)],destination/'signature-worker')
  for baseline,row in inventory.items():
   if baseline=='konclude': measured=root/('classification-konclude-'+runs['classification_konclude'])/'konclude'/source['ontology']
   else: measured=root/('classification-'+runs['classification_km' if baseline=='km' else 'classification'])/baseline/source['ontology']
   if not (measured/'record.json').exists():
    case['outcomes'][baseline]={'status':'missing_measurement'};continue
   record=json.loads((measured/'record.json').read_text())
   outcome={'measurement_status':record['status'],'measurement_receipt_sha256':digest(measured/'record.json')}
   case['outcomes'][baseline]=outcome
   if record['status']!='executed_unvalidated':outcome['status']='no_completed_taxonomy';continue
   try:
    assert record['source_sha256']==source['sha256'],'measurement source mismatch'
    assert record['artifact_sha256']==row['sha256'],'measurement binary mismatch'
    raw=measured/'taxonomy.raw'
    assert digest(raw)==record['files']['taxonomy.raw']['sha256'],'raw taxonomy changed'
    prefix=destination/baseline
    command=[sys.executable,str(sources/'canonicalize.py'),'--input',str(raw),'--format',record['output_format'],'--signature',str(signature),'--output-prefix',str(prefix),'--fingerprint-script',str(sources/'full_iri_fingerprint.py')]
    run(command,destination/(baseline+'-canonicalization'))
    validated=json.loads(Path(str(prefix)+'.validated.json').read_text())
    assert validated['source_sha256']==source['sha256'],'canonical input binding mismatch'
    canonical[baseline]=validated;outcome.update(status='canonicalized_requires_comparison',canonical_sha256=digest(str(prefix)+'.validated.json'))
   except Exception as error:outcome.update(status='validation_error',error=str(error))
  for left,right in itertools.combinations(sorted(canonical),2):
   result=compare(canonical[left],canonical[right]);result.update(left=left,right=right)
   case['comparisons'].append(result)
  case['status']='audited_available_outputs'
 except Exception as error:case.update(status='source_or_audit_error',error=str(error))
 publish(destination/'audit.json',case)
 summary['inputs'].append({'ontology':source['ontology'],'status':case['status'],'comparisons':len(case['comparisons'])})
 publish(output/'summary.json',summary)
summary['status']='audit_finished';publish(output/'summary.json',summary)
