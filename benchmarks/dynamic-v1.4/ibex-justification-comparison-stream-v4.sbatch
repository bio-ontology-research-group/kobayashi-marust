#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=1
#SBATCH --mem=8G
#SBATCH --time=01:00:00
#SBATCH --job-name=km-v142-justification-comparison
set -euo pipefail
cd /ibex/scratch/hohndor/km/dynamic-benchmark-20260917/justification-comparison-stream-v4
python3 render_justification_comparison.py justification-comparison-stream-v4-config.json report
sha256sum render_justification_comparison.py audit_justification_main.py justification_corrections.py justification-comparison-stream-v4-config.json > report/renderer-inputs.sha256
echo JUSTIFICATION_COMPARISON_RENDERED
