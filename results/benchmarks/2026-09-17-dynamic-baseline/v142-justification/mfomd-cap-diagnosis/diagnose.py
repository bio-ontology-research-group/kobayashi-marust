import json,os,subprocess,time,hashlib
from pathlib import Path
base=Path('/ibex/scratch/hohndor/km/dynamic-benchmark-20260917')
root=base/'mfomd-cap-diagnosis-v1';root.mkdir(exist_ok=True)
tasks=base/'justification-v142-original/justification-main/tasks'
task=next(json.loads(p.read_text()) for p in sorted(tasks.glob('*.json')) if (lambda t:t['ontology']=='mfomd' and t['query_id']=='q000' and t['track']=='module' and t['repetition']==1)(json.loads(p.read_text())))
assert hashlib.sha256(Path(task['input']).read_bytes()).hexdigest()==task['sha256']
rows=[]
for cap in [1,2,1,2]:
 out=root/str(len(rows));out.mkdir()
 env={k:v for k,v in os.environ.items() if not k.startswith('KM_')};env.update(KM_THREADS='1',KM_CENTRAL_TIME_CAP=str(cap))
 cmd=['timeout','-k','2','15',task['km'],'explain','--max-axioms','1000000','--max-source-bytes','1073741824','--max-checks','10000000','--max-justifications','1',task['input'],'subclass',task['sub'],task['super']]
 start=time.monotonic()
 with (out/'stdout').open('w') as stdout,(out/'stderr').open('w') as stderr:r=subprocess.run(cmd,stdout=stdout,stderr=stderr,env=env)
 rows.append(dict(cap_s=cap,elapsed_s=time.monotonic()-start,exit_code=r.returncode,stderr=(out/'stderr').read_text(),command=cmd))
(root/'diagnosis.json').write_text(json.dumps(dict(purpose='Mechanism diagnosis only; not a benchmark replacement',task=task,binary_sha256=hashlib.sha256(Path(task['km']).read_bytes()).hexdigest(),rows=rows),indent=2)+'\n')
