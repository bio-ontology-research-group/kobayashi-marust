#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=22G
#SBATCH --time=01:00:00
#SBATCH --job-name=km-incremental-v3-gate
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
python3 - <<'PY'
import hashlib,json,gzip
from pathlib import Path
from run_incremental import measure,verify_driver
root=Path.cwd();verify_driver(root)
full=root/'inputs/mmo-n10/pilot-states.txt'
digest=root/'gate/inputs/states.txt';digest.parent.mkdir(parents=True);digest.write_bytes(full.read_bytes())
reference=None
for reasoner in ['hermit','jfact','openllet','elk','whelk','km','konclude']:
    for arm in (['fresh'] if reasoner=='konclude' else ['session','fresh']):
        out=root/'gate'/reasoner/arm
        compressed=measure(root,full,reasoner,arm,out/'full',1800)
        hashed=measure(root,digest,reasoner,arm,out/'digest',1800)
        assert compressed['status']==hashed['status']=='ok',(reasoner,arm,compressed['status'],hashed['status'])
        observed=[]
        for i in range(6):
            with gzip.open(out/'full'/f'{i:03d}.sig.gz','rb') as f:data=f.read()
            actual=hashlib.sha256(data).hexdigest()
            assert actual==(out/'digest'/f'{i:03d}.sig.sha256').read_text().strip(),(reasoner,arm,i,'digest')
            observed.append(actual)
        if reference is None:reference=observed
        assert observed==reference,(reasoner,arm,'taxonomy')
(root/'gate/PASS').write_text(json.dumps({'states':6,'arms':13,'checks':'full versus digest and exact HermiT taxonomy for each arm'})+'\n')
PY
