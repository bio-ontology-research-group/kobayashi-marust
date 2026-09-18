#!/usr/bin/env python3
"""Freeze all tasks from preselected panel, recording unavailable preparations."""
import argparse,json,hashlib
from pathlib import Path

def main(a):
 root=a.root.resolve();tasks=[];status=[]
 manifest=root/'justification-main/driver-manifest.json'
 manifest_hash=hashlib.sha256(manifest.read_bytes()).hexdigest()
 selection=json.loads(a.panel.read_text()) if a.panel else [{'ontology':n,'el':el} for n,el in [('mmo',True),('hao',True),('vto',True),('mfomd',False),('to',False),('uberon',False)]]
 for selected in selection:
  name,el=selected['ontology'],selected['el']
  panel=root/'justification-panel-v2'/name
  if not (panel/'modules/COMPLETE').exists():
   status.append({'ontology':name,'status':'preparation_unavailable','reason':'independent entailment confirmation or module preparation incomplete'})
   continue
  queries=(panel/'queries.tsv').read_text().splitlines()
  status.append({'ontology':name,'status':'prepared','queries':len(queries)})
  for i,line in enumerate(queries):
   queryhash,sub,sup=line.split('\t')
   for track in ['module','full']:
    input=(panel/'modules'/('q%03d.ofn'%i)) if track=='module' else Path('/ibex/scratch/hohndor/km/paper-benchmark-20260830/obo-snapshot/merged')/(name+'.ofn')
    source_hash=hashlib.sha256(input.read_bytes()).hexdigest()
    for repetition in range(6):
     task={'ontology':name,'query_id':'q%03d'%i,'query_hash':queryhash,'track':track,'input':str(input),'sha256':source_hash,'sub':sub,'super':sup,'el':el,'limits':[1,10,100],'library':True,'repetition':repetition,'warmup':repetition==0,'driver_manifest':str(manifest),'driver_manifest_sha256':manifest_hash,'km':'/ibex/scratch/hohndor/km/v140-release-final-20260916/km.ibex','konclude':str(root/'konclude_oracle.py'),'runtime':'/ibex/scratch/hohndor/km/paper-benchmark-20260830/runtimes','classes':str(root/'justification-main/classes')}
     tasks.append(task)
 out=root/'justification-main';out.mkdir(exist_ok=True)
 (out/'panel-status.json').write_text(json.dumps(status,indent=2)+'\n')
 taskdir=out/'tasks';taskdir.mkdir(exist_ok=True)
 for i,t in enumerate(tasks):(taskdir/('%04d.json'%i)).write_text(json.dumps(t,indent=2)+'\n')
 (out/'task-count.txt').write_text(str(len(tasks))+'\n')
 print(json.dumps({'tasks':len(tasks),'panel':status}))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('root',type=Path);p.add_argument('--panel',type=Path);main(p.parse_args())
