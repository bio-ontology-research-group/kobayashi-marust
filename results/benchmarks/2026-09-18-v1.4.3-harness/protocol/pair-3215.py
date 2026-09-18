import json,os,subprocess,time
from pathlib import Path
root=Path('/ibex/scratch/hohndor/km/v143-harness-20260918')
out=root/('paired-3215-'+os.environ['SLURM_JOB_ID']);out.mkdir()
for index,(name,binary) in enumerate([('v142','/ibex/scratch/hohndor/km/dynamic-benchmark-20260917/v142-rc1/km.ibex'),('rc2',str(root/'km-candidate-v143-rc2')),('rc2-repeat',str(root/'km-candidate-v143-rc2')),('v142-repeat','/ibex/scratch/hohndor/km/dynamic-benchmark-20260917/v142-rc1/km.ibex')]):
 dest=out/name;dest.mkdir();env=os.environ.copy();env.update(KM_TIMING='1',KM140_BIN=binary,HARNESS_OUT_DIR=str(dest/'output'),TMPDIR=str(dest/'tmp'));(dest/'tmp').mkdir()
 cmd=[str(root/'target/release/owl-reasoner-harness'),'run','--corpus',str(root/'corpus/pool_sample/files'),'--only',str(root/'targeted-3215.txt'),'--reasoner',str(root/'source/wrappers/run-km-v140.sh'),'--args','{}','--cap-secs','240','--threads','1','--mem-mb','20480','--out',str(dest/'results.jsonl')]
 start=time.monotonic()
 with (dest/'driver.stdout').open('w')as stdout,(dest/'driver.stderr').open('w')as stderr:p=subprocess.run(cmd,env=env,stdout=stdout,stderr=stderr)
 (dest/'receipt.json').write_text(json.dumps(dict(rc=p.returncode,wall_s=time.monotonic()-start,binary=binary,command=cmd,job=os.environ['SLURM_JOB_ID'],index=index))+'\n')
 assert p.returncode==0
(out/'COMPLETE').touch()
