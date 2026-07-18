#!/bin/bash
# Audit every ORE source for non-OWL classes named Thing or Nothing.
#SBATCH --job-name=km-tail-iri-audit
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --array=0-29%10
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/tail-validation-20260718/slurm/iri-audit-%A_%a.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
validation=$km_root/routing_20260715/tail-validation-20260718
index=${SLURM_ARRAY_TASK_ID:-0}
/usr/bin/python3 "$validation/audit_special_iri_collisions.py" \
  --corpus "$km_root/corpus" \
  --task-index "$index" \
  --task-count 30 \
  --output "$validation/special-iri-audit/$index.jsonl"
