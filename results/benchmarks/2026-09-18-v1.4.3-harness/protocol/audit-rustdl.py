import json
from pathlib import Path
root=Path('/ibex/scratch/hohndor/km/v143-harness-20260918')
with (root/'rustdl-source-coverage.jsonl').open('w') as out:
 for results in sorted((root/'baseline-rustdl-v0428').glob('*/results.jsonl')):
  assert (results.parent/'COMPLETE').exists(), results
  for line in results.read_text().splitlines():
   row=json.loads(line)
   if row.get('kind')!='case':continue
   report={k:row.get(k)for k in ['ont','outcome','out_sha256','wall_s']}
   if row['outcome']=='ok':
    data=json.loads((results.parent/'output'/(row['ont']+'.json')).read_text())
    report.update({k:data.get(k)for k in ['consistent','incomplete','dropped','trusted_sat_refutations']})
   out.write(json.dumps(report)+'\n')
