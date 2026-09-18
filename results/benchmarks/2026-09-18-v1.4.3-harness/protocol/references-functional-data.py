import json, os, subprocess, time, resource
from pathlib import Path
root=Path('/ibex/scratch/hohndor/km/v143-harness-20260918')
ont=(root/'functional-data-reference-inputs.txt').read_text().splitlines()[int(os.environ['SLURM_ARRAY_TASK_ID'])]
resource.setrlimit(resource.RLIMIT_AS,(20*1024**3,20*1024**3))
for name,factory in [('hermit','org.semanticweb.HermiT.Reasoner$ReasonerFactory'),('jfact','uk.ac.manchester.cs.jfact.JFactFactory')]:
 out=root/'references-functional-data'/ont/name;out.mkdir(parents=True,exist_ok=False)
 cmd=['/usr/bin/time','-v','-o',str(out/'time'),'timeout','--kill-after=5s','240','java','-XX:ActiveProcessorCount=1','-Xmx12g','-jar',str(root/('classifier-'+name+'.jar')),factory,str(root/'corpus/pool_sample/files'/(ont+'.owl')),str(out/'taxonomy.tsv')]
 start=time.monotonic()
 with (out/'stdout').open('wb') as stdout,(out/'stderr').open('wb') as stderr:
  proc=subprocess.run(cmd,stdout=stdout,stderr=stderr)
 (out/'receipt.json').write_text(json.dumps(dict(command=cmd,rc=proc.returncode,wall_s=time.monotonic()-start,job=os.environ['SLURM_JOB_ID']))+'\n')
