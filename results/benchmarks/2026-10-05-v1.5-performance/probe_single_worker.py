"""Paired scheduling diagnostic: fixed binary and limits, alternate worker order."""
import os,json,hashlib
from pathlib import Path
from measure_classification import measure
root=Path(__file__).resolve().parent
inputs=json.loads((root/'dense-slow-profile-inputs.json').read_text())['inputs']
cases=[r for r in inputs if r['ontology'] in {'ore_ont_14572','ore_ont_7361','ore_ont_9724'}]
task=int(os.environ['SLURM_ARRAY_TASK_ID']); row=cases[task//2]; repetition=task%2
inventory=json.loads((root/'dense-data-candidate-artifact.json').read_text())
base=root/('single-worker-probe-'+os.environ['SLURM_ARRAY_JOB_ID'])/row['ontology']/str(repetition)
base.mkdir(parents=True,exist_ok=True)
records=[]
for workers in ([1,2] if repetition==0 else [2,1]):
 flags=dict(inventory['flags'],KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=str(workers),KM_TIMING='1')
 os.environ.update(flags)
 destination=base/('workers-'+str(workers))
 record=measure(inventory,'km',row['path'],row['sha256'],destination,timeout=240,memory_mib=20480)
 records.append({'workers':workers,'flags':flags,'record':record,'record_sha256':hashlib.sha256((destination/'record.json').read_bytes()).hexdigest()})
 (base/'receipt.json').write_text(json.dumps({'diagnostic_only':True,'input':row,'repetition':repetition,'records':records,'scope':'Scheduling comparison only; completed outputs require independent audit.'},indent=2)+'\n')
 if record['status']=='adapter_error': raise RuntimeError(record)
