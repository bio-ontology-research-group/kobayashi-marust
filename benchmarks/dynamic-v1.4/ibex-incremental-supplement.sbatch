#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=22G
#SBATCH --time=1-01:00:00
#SBATCH --array=0-29%4
#SBATCH --job-name=km-incremental-supplement
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
test -f gate/PASS
read -r id reasoner < <(python3 - "$SLURM_ARRAY_TASK_ID" <<'PY'
import csv,sys,random
jobs=[]
for row in csv.DictReader(open('incremental-panel.tsv'),delimiter='\t'):
    for n in (1,10,100):
        for reasoner in ['km','hermit','jfact','openllet','konclude']+(['elk','whelk'] if row['profile']=='EL' else []):
            jobs.append((row['id']+'-n'+str(n),reasoner))
assert len(jobs)==30
random.Random(20260917).shuffle(jobs)
print(*jobs[int(sys.argv[1])])
PY
)
test -f "inputs/$id/COMPLETE"
python3 run_incremental.py "$DYNAMIC_ROOT" "$id" "$reasoner" --repetitions 5
