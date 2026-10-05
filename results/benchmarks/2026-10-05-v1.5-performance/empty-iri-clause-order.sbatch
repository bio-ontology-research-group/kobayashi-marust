#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=24G
#SBATCH --time=10:00:00
#SBATCH --export=NONE
#SBATCH --job-name=km-v150-empty-iri-clause-order
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005/empty-iri-clause-order-%A_%a.log
set -euo pipefail
root=/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005
export TMPDIR="$root/empty-iri-clause-order-tmp-${SLURM_JOB_ID}"
mkdir -p "$TMPDIR"
cd "$root"
sha256sum -c runner-files.sha256
sha256sum -c empty-iri-clause-order-files.sha256
/usr/bin/python3.9 "$root/audit_empty_iri_clause_order.py" --frontend-job 53312770
