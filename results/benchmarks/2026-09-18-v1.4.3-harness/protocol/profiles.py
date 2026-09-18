import json, subprocess, resource
from pathlib import Path
root=Path('/ibex/scratch/hohndor/km/v143-harness-20260918')
km='/ibex/scratch/hohndor/km/dynamic-benchmark-20260917/v142-rc1/km.ibex'
resource.setrlimit(resource.RLIMIT_AS,(20*1024**3,20*1024**3))
with (root/'all-profiles.jsonl').open('x') as out:
 for inp in sorted((root/'corpus/pool_sample/files').glob('*.owl')):
  try:
   p=subprocess.run([km,'profile',str(inp)],capture_output=True,text=True,timeout=240)
   row=dict(ont=inp.stem,rc=p.returncode,stderr=p.stderr,profile=json.loads(p.stdout) if p.returncode==0 else None)
  except subprocess.TimeoutExpired: row=dict(ont=inp.stem,rc=124)
  out.write(json.dumps(row)+'\n');out.flush()
