#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --time=00:10:00
#SBATCH --job-name=km-justification-candidate-audit
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
python3 audit_justification_candidate.py justification-candidate-controls candidate-controls-audit.json
echo JUSTIFICATION_CANDIDATE_CONTROLS_PASS
