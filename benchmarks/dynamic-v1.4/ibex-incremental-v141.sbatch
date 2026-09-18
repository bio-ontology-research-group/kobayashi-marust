#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=22G
#SBATCH --time=1-01:00:00
#SBATCH --array=0-23%6
#SBATCH --job-name=km-v141-incremental
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
python3 - <<'PY'
import hashlib,json
from pathlib import Path
r=json.loads(Path('deployment.json').read_text())
for path,digest in r['artifacts'].items():
 assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==digest,path
PY
id=$(python3 - "$SLURM_ARRAY_TASK_ID" <<'PY'
import csv,sys,random
jobs=[r['id']+'-n'+str(n) for r in csv.DictReader(open('incremental-panel.tsv'),delimiter='\t') for n in (1,10,100)]
assert len(jobs)==24
random.Random(20260917).shuffle(jobs)
print(jobs[int(sys.argv[1])])
PY
)
test -f "inputs/$id/COMPLETE"
sha256sum -c "inputs/$id/SHA256SUMS" > "input-verified-$id-$SLURM_JOB_ID.log"
python3 run_incremental.py "$DYNAMIC_ROOT" "$id" km --repetitions 5
