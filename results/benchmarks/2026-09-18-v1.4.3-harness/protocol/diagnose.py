import json, os, subprocess, time, resource
from pathlib import Path
root=Path('/ibex/scratch/hohndor/km/v143-harness-20260918')
names=(root/'diagnostic-inputs.txt').read_text().splitlines()
ont=names[int(os.environ['SLURM_ARRAY_TASK_ID'])]
out=root/'diagnostic-v142'/ont;out.mkdir(parents=True,exist_ok=False)
km='/ibex/scratch/hohndor/km/dynamic-benchmark-20260917/v142-rc1/km.ibex'
inp=root/'corpus/pool_sample/files'/(ont+'.owl')
resource.setrlimit(resource.RLIMIT_AS,(20*1024**3,20*1024**3))
env=os.environ.copy();env.update(RAYON_NUM_THREADS='1',KM_TIMING='1')
for name,args in [('profile',['profile',str(inp)]),('auto',['classify','--route','auto',str(inp)]),('production_all1',['classify','--route','production_all1',str(inp)])]:
 command=['/usr/bin/time','-v','-o',str(out/(name+'.time')),'timeout','--kill-after=5s','240',km,*args]
 start=time.monotonic()
 with (out/(name+'.stdout')).open('wb') as stdout,(out/(name+'.stderr')).open('wb') as stderr:
  p=subprocess.run(command,stdout=stdout,stderr=stderr,env=env)
 (out/(name+'.receipt.json')).write_text(json.dumps(dict(command=command,rc=p.returncode,wall_s=time.monotonic()-start,slurm_job=os.environ['SLURM_JOB_ID']),indent=2)+'\n')
(out/'COMPLETE').touch()
