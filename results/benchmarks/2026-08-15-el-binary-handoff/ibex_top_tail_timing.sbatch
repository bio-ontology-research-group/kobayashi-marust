#!/bin/bash
#SBATCH --job-name=km-top-tail-timing
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:06:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-1
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/top-tail-timing-20260815/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/top-tail-timing-20260815
binary=/ibex/scratch/hohndor/km/median-overhead-20260815/km
sha=4aa2370c8cebac9b78fcd64cfbfa6d4be0af2bd87bb6b5c0f351c478d88056af
[[ $(sha256sum "$binary" | cut -d' ' -f1) == $sha ]]
case ${SLURM_ARRAY_TASK_ID:?} in
  0) ont=ore_ont_10621.owl ;;
  1) ont=ore_ont_14817.owl ;;
esac
mkdir -p "$root"
export KM_ROUTE=auto KM_TIMING=1 KM_THREADS=16 KM_PAR_MEM_GB=18
/usr/bin/time -v "$binary" classify "/ibex/scratch/hohndor/km/corpus/$ont" \
  > "$root/$ont.out.tmp" 2> "$root/$ont.timing.tmp"
test -s "$root/$ont.out.tmp"
mv "$root/$ont.out.tmp" "$root/$ont.out"
mv "$root/$ont.timing.tmp" "$root/$ont.timing"
echo "TIMING_COMPLETE ontology=$ont"
