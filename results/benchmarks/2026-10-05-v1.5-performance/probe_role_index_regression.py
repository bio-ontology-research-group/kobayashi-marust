"""Paired finite-model verifier diagnostic; fixed source and limits, alternating binaries."""
import os,json,hashlib
from pathlib import Path
from measure_classification import measure
root=Path(__file__).resolve().parent
inputs=json.loads((root/'role-index-regression-inputs.json').read_text())['inputs']
cases=inputs
task=int(os.environ['SLURM_ARRAY_TASK_ID']); row=cases[task//2]; repetition=task%2
inventories={arm:json.loads((root/name).read_text()) for arm,name in [('baseline','single-worker-candidate-artifact.json'),('indexed','finite-role-index-full-artifact.json')]}
base=root/('role-index-regression-'+os.environ['SLURM_ARRAY_JOB_ID'])/row['ontology']/str(repetition)
base.mkdir(parents=True,exist_ok=True)
records=[]
for arm in (['baseline','indexed'] if repetition==0 else ['indexed','baseline']):
 inventory=inventories[arm]
 flags=dict(inventory['flags'],KM_TIMING='1')
 os.environ.update(flags)
 destination=base/arm
 record=measure(inventory,'km',row['path'],row['sha256'],destination,timeout=240,memory_mib=20480)
 records.append({'arm':arm,'flags':flags,'record':record,'record_sha256':hashlib.sha256((destination/'record.json').read_bytes()).hexdigest()})
 (base/'receipt.json').write_text(json.dumps({'diagnostic_only':True,'input':row,'repetition':repetition,'records':records,'scope':'Finite-model indexing comparison only; completed outputs require independent audit.'},indent=2)+'\n')
 if record['status']=='adapter_error': raise RuntimeError(record)
