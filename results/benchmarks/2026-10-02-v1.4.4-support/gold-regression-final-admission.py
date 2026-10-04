import hashlib, json, os, subprocess
from pathlib import Path
root=Path('/ibex/scratch/projects/c2014/hohndor/km/v144-support-recovery-20261003')
binary=root/'km-final-admission'
expected=(root/'final-admission-binary.sha256').read_text().split()[0]
assert hashlib.sha256(binary.read_bytes()).hexdigest()==expected
names=(root/'previous-gold-inputs.txt').read_text().splitlines()
chunk=int(os.environ['SLURM_ARRAY_TASK_ID']); panel=root/('gold-regression-final-admission-'+os.environ['SLURM_ARRAY_JOB_ID']);(panel/'results').mkdir(parents=True,exist_ok=True)
general='/ibex/scratch/hohndor/km/v12-sparse-horn-16-20260827/full-v3/full_panel_run_one.py'
collision='/ibex/scratch/hohndor/km/v1.4-source-bridge-20260902/full-sweep/full_panel_run_one_collision_safe.py'
for ont in names[chunk*32:(chunk+1)*32]:
 runner=collision if ont in ['ore_ont_13503.owl','ore_ont_15703.owl','ore_ont_3524.owl','ore_ont_4669.owl']else general
 work=panel/'work'/ont;work.mkdir(parents=True,exist_ok=True)
 out=panel/'results'/(ont+'.json');assert not out.exists()
 cmd=['/usr/bin/python3',runner,'--kind','km','--arm','km_v144','--ontology','/ibex/scratch/hohndor/km/corpus/'+ont,'--binary',str(binary),'--workers','16','--timeout','240','--memcap-mb','20480','--gold','/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__'+ont+'.sig.gz','--gold-kind','konclude','--workdir',str(work/'run'),'--failures-dir',str(panel/'failures'),'--checkpoint',str(out)+'.checkpoint.json','--capture-km-route','--env','KM_ROUTE=auto']
 env=os.environ.copy();env['PYTHONPATH']=str(Path(runner).parent)
 with out.with_suffix('.tmp').open('w')as stdout,(work/'driver.stderr').open('w')as stderr:
  p=subprocess.run(cmd,stdout=stdout,stderr=stderr,env=env)
 assert p.returncode==0,(ont,p.returncode)
 data=json.loads(out.with_suffix('.tmp').read_text());assert data['ont']==ont and data['binary_sha256']==expected and data.get('checkpointed') is True
 out.with_suffix('.tmp').replace(out)
(panel/f'COMPLETE-{chunk:03}').touch()
