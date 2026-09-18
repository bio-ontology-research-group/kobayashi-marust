#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=22G
#SBATCH --time=01:10:00
#SBATCH --array=0-29%6
#SBATCH --job-name=km-incremental-panel
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
read -r id reasoner < <(python3 - "$SLURM_ARRAY_TASK_ID" <<'PY'
import csv,sys
jobs=[]
for row in csv.DictReader(open('incremental-panel.tsv'),delimiter='\t'):
    for reasoner in ['km','hermit','jfact','openllet']+(['elk','whelk'] if row['profile']=='EL' else []):
        jobs.append((row['id']+'-n10',reasoner))
print(*jobs[int(sys.argv[1])])
PY
)
python3 run_incremental.py "$DYNAMIC_ROOT" "$id" "$reasoner" --pilot
