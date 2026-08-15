#!/bin/bash
#SBATCH --job-name=km-bridge-closed-full-pair
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-591%40
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/bridge-closed-20260815/full-pair/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/bridge-closed-20260815/full-pair
template=/ibex/scratch/hohndor/km/el-binary-final-pair-20260815/ibex_compact_paired_v027.sbatch
generated=${SLURM_TMPDIR:-/tmp}/km-bridge-closed-pair-${SLURM_JOB_ID}.sh
/usr/bin/sed \
  -e 's|/ibex/scratch/hohndor/km/el-binary-final-pair-20260815|/ibex/scratch/hohndor/km/bridge-closed-20260815/full-pair|g' \
  -e 's|/ibex/scratch/hohndor/km/intersection-inproc-20260815/km|/ibex/scratch/hohndor/km/median-overhead-20260815/km|g' \
  -e 's|/ibex/scratch/hohndor/km/el-binary-final-20260815/km|/ibex/scratch/hohndor/km/bridge-closed-20260815/km|g' \
  -e 's|628b11d8e95dcedf2394afac53a35399ba1e9106b0e844aae3dbbad41852875a|4aa2370c8cebac9b78fcd64cfbfa6d4be0af2bd87bb6b5c0f351c478d88056af|g' \
  -e 's|1cd7dcbeea96e39b4b4b50eec48e42a9005e223a26515661b6329e746578033c|c5b85fea05cae73db5f66ec3a0b86c8439fd58ec207a612b07e85c91d08081dd|g' \
  "$template" > "$generated"
/bin/bash "$generated"
