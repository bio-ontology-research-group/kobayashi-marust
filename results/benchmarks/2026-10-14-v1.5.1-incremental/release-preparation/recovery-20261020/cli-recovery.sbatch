#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=24G
#SBATCH --no-requeue
#SBATCH --export=NONE
#SBATCH --time=14:00:00
#SBATCH --array=62,75-79%4
#SBATCH --job-name=km-4dd7-cli-retry
#SBATCH --output=/ibex/project/c2014/hohndor/km/v151-incremental-20261014/validation/full80-4dd7995b-recovery-20261020/slurm-cli-%A_%a.log
set -euo pipefail
[[ ${SLURM_RESTART_COUNT:-0} == 0 ]] || exit 2
I=$SLURM_ARRAY_TASK_ID
exec /usr/bin/python3.9 /ibex/project/c2014/hohndor/km/v151-incremental-20261014/final-runtime-v2/runtime/timing-runner/run_prepared_fixture.py --panel-root /ibex/project/c2014/hohndor/km/v151-incremental-20261014/real-panel/preparation-recovered69-view --task-index "$I" --protocol /ibex/project/c2014/hohndor/km/v151-incremental-20261014/final-runtime-v2/control/acceptance-protocol.json --protocol-sha256 fce89e1db19b49176ac2d389f73fc5f4cb41ad90dcd027f1660e7278c8210143 --binary-inventory /ibex/project/c2014/hohndor/km/v151-incremental-20261014/validation/full80-4dd7995b-v1/cli-binary-inventory.json --binary-inventory-sha256 0647dbe78144c8b8a345fcfc0abe8442008c092e33939c9bbd7cd2d52fce0c03 --run-panel /ibex/project/c2014/hohndor/km/v151-incremental-20261014/final-runtime-v2/runtime/timing-runner/cli-runtime-supplement-v2/run_panel.py --run-panel-sha256 2542d7fca5cff082d77a6444f4211dd77f0df20bc0c1a5a4c79b6f422a36d544 --run-panel-provenance /ibex/project/c2014/hohndor/km/v151-incremental-20261014/final-runtime-v2/runtime/timing-runner/cli-runtime-supplement-v2/four-arm-panel-driver-provenance.json --run-panel-provenance-sha256 b1d19b5f40b09c9b92623d3dc076977692aa0b871936280d4e1e91e9998390e6 --output-root /ibex/project/c2014/hohndor/km/v151-incremental-20261014/validation/full80-4dd7995b-recovery-20261020/results-cli --scratch-parent "${SLURM_TMPDIR:-/tmp}"
