#!/bin/bash
# Submit with --dependency=afterany:<array-job-id> and
# --export=ALL,ARRAY_JOB_ID=<array-job-id>.
#SBATCH --job-name=km-6999-592-audit
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --export=ALL
#SBATCH --output=/ibex/scratch/hohndor/km/datetime-bridge-6999-full-20260730/slurm-%x-%j.out

set -euo pipefail
: "${ARRAY_JOB_ID:?submit with the ontology array job id}"
root=/ibex/scratch/hohndor/km/datetime-bridge-6999-full-20260730
km_root=/ibex/scratch/hohndor/km

/usr/bin/python3 "$root/audit_full_sweep.py" \
  --root "$root" \
  --ontology-list "$km_root/routing_20260715/onts.txt" \
  --array-job-id "$ARRAY_JOB_ID" \
  --binary "$root/km"
