#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --time=00:20:00
#SBATCH --job-name=km-justification-diagnose
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
python3 justification_capture.py /ibex/scratch/hohndor/km/v140-release-final-20260916/km.ibex justification-panel/mfomd/modules/q000.ofn http://purl.obolibrary.org/obo/DOID_0060154 http://purl.obolibrary.org/obo/DOID_2033 justification-diagnose-mfomd
