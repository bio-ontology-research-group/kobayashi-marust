"""Audit all update revisions against fresh runs and an independent reference."""
import json
from pathlib import Path
import subprocess
import sys
import tree_watchdog as watchdog
from measure_classification import digest
from update_outputs import extract
from compare_taxonomies import compare
from run_set import load as load_run_set

root,task,job=Path(sys.argv[1]),int(sys.argv[2]),sys.argv[3]
runs=load_run_set(root,sys.argv[4] if len(sys.argv)>4 else None)
sources=Path(__file__).parent
source=json.loads((root/'workload-selection.json').read_text())['selected'][task]
inventory={r['id']:r for r in json.loads((root/runs['inventory']).read_text())['artifacts']}
output=root/('update-audit-'+job)/source['ontology'];output.mkdir(parents=True,exist_ok=False)
summary={'ontology':source['ontology'],'source_sha256':source['sha256'],'status':'preparing','run_set':runs,'revisions':[],'runner_sha256':digest(__file__)}
def publish(path,value):
 temporary=path.with_suffix('.part');temporary.write_text(json.dumps(value,indent=2)+'\n');temporary.replace(path)
def run(command,directory):
 directory.mkdir(parents=True,exist_ok=False)
 with (directory/'stdout').open('wb') as stdout,(directory/'stderr').open('wb') as stderr:
  process=subprocess.Popen(command,stdout=stdout,stderr=stderr,stdin=subprocess.DEVNULL,preexec_fn=watchdog.child_preexec)
  result=watchdog.monitor(process,timeout=600,memcap_bytes=20480*1024**2)
 receipt={'status':result.status,'exit_code':process.returncode,'wall_s':result.wall_s,'peak_bytes':result.peak_bytes,'command':command}
 publish(directory/'record.json',receipt)
 if result.status!='ok' or process.returncode:raise ValueError('audit worker failed; see '+str(directory/'record.json'))
def measured_path(baseline,mode,repetition,revision):
 ontology=source['ontology'];repeat=f'repetition-{repetition}'
 if baseline=='konclude':
  return root/('konclude-retained-'+runs['retained_konclude'])/ontology/repeat if mode=='retained' else root/('konclude-updates-'+runs['updates_konclude'])/ontology/repeat/f'{revision:03}'
 if baseline in ['rustdl','more','sequoia']:
  return root/('native-updates-'+runs['updates_native'])/ontology/baseline/repeat/f'{revision:03}'
 jobdir=('km-updates-'+runs['updates_km']) if baseline=='km' else 'java-updates-'+runs['updates_whelk' if baseline=='whelk' else 'updates_java']
 directory=root/jobdir/ontology/baseline/repeat/mode
 return directory if mode=='retained' else directory/f'{revision:03}'
publish(output/'summary.json',summary)
try:
 watchdog.protect_supervisor()
 prepared=root/('prepared-updates-'+runs['updates_preparation'])/source['ontology']
 receipt=json.loads((prepared/'receipt.json').read_text())
 assert receipt['status']=='prepared' and receipt['source_sha256']==source['sha256'],'source preparation failed'
 preservation=prepared/'revisions/verification.tsv'
 assert digest(preservation)==receipt['files']['verification.tsv'],'preservation receipt changed'
 assert preservation.read_text().endswith('status\tpassed\n'),'source preservation failed'
 summary['preparation_receipt_sha256']=digest(prepared/'receipt.json')
 hermit=inventory['hermit'];assert digest(hermit['path'])==hermit['sha256'],'signature runtime changed'
 classes=output/'classes';classes.mkdir()
 run(['javac','--release','11','-cp',hermit['path'],'-d',str(classes),str(sources/'SourceSignature.java')],output/'compile')
 for revision in range(5):
  destination=output/f'{revision:03}';destination.mkdir()
  original=prepared/'revisions'/f'{revision:03}.ofn';source_hash=receipt['files'][original.name]
  assert digest(original)==source_hash,'revision source changed'
  case={'revision':revision,'source_sha256':source_hash,'outcomes':{},'comparisons':[],'status':'running'}
  canonical={}
  try:
   signature=destination/'signature.tsv'
   run(['java','-Xmx16g','-XX:ActiveProcessorCount=1','-cp',str(classes)+':'+hermit['path'],'org.kmbenchmark.SourceSignature',str(original),str(signature)],destination/'signature-worker')
   for baseline,row in inventory.items():
    modes=['cold'] if baseline in ['rustdl','more','sequoia'] else ['cold','retained']
    for mode in modes:
     for repetition in range(3):
      key=f'{baseline}-{mode}-{repetition}';directory=measured_path(baseline,mode,repetition,revision)
      if not (directory/'record.json').exists():case['outcomes'][key]={'status':'missing_measurement'};continue
      try:
       raw=destination/(key+'.raw')
       outcome=extract(directory,baseline,mode,revision,source_hash,row['sha256'],raw)
       case['outcomes'][key]=outcome
       if outcome['status']!='extracted_requires_semantic_audit':continue
       prefix=destination/key
       run([sys.executable,str(sources/'canonicalize.py'),'--input',str(raw),'--format',outcome['format'],'--signature',str(signature),'--output-prefix',str(prefix),'--fingerprint-script',str(sources/'full_iri_fingerprint.py')],destination/(key+'-canonicalization'))
       validated=json.loads(Path(str(prefix)+'.validated.json').read_text())
       assert validated['source_sha256']==source_hash,'canonical revision mismatch'
       canonical[key]=validated;outcome.update(status='canonicalized_requires_comparison',canonical_sha256=digest(str(prefix)+'.validated.json'))
      except Exception as error:case['outcomes'][key]={'status':'validation_error','error':str(error)}
   pairs=[]
   reference='hermit-cold-0'
   for key in sorted(canonical):
    if key!=reference:pairs.append((reference,key,'reference'))
    baseline,mode,repetition=key.split('-')
    if mode=='retained':pairs.append((f'{baseline}-cold-{repetition}',key,'fresh_vs_retained'))
    if repetition!='0':pairs.append((f'{baseline}-{mode}-0',key,'repeatability'))
   for left,right,kind in pairs:
    if left not in canonical:result={'status':'comparison_unavailable','agreement':None}
    else:result=compare(canonical[left],canonical[right])
    case['comparisons'].append(dict(result,left=left,right=right,kind=kind))
   case['status']='audited_available_outputs'
  except Exception as error:case.update(status='revision_audit_error',error=str(error))
  publish(destination/'audit.json',case)
  summary['revisions'].append({'revision':revision,'status':case['status'],'outcomes':len(case['outcomes']),'comparisons':len(case['comparisons'])})
  publish(output/'summary.json',summary)
 summary['status']='audit_finished'
except Exception as error:summary.update(status='preparation_or_audit_error',error=str(error))
publish(output/'summary.json',summary)
