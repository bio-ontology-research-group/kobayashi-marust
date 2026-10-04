#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=22G
#SBATCH --time=00:30:00
#SBATCH --job-name=km-v144-output-audit
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v144-support-recovery-20261003/full-final-admission-audit-%j.log
set -euo pipefail
root=/ibex/scratch/projects/c2014/hohndor/km/v144-support-recovery-20261003
/usr/bin/python3.9 "$root/audit_full_final_admission.py" \
 --candidate-root "$root" \
 --baseline-root /ibex/scratch/hohndor/km/v143-harness-20260918/candidate-v143-rc2 \
 --recovery-references "$root/main-lazy-recovery-references.json" \
 --corpus-root /ibex/scratch/hohndor/km/v143-harness-20260918/corpus/pool_sample/files \
 --job "${1:?candidate array job ID required}" --output "$root/full-final-admission-${1}-output-audit.json"
