#!/bin/bash
#SBATCH --job-name=km-nf1-compact-profile
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:03:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-nf1-compact-20260825/profile-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v110-nf1-compact-20260825
ont=/ibex/scratch/hohndor/km/corpus/ore_ont_10689.owl
mkdir -p "$root/profile"
for arm in baseline candidate; do
  binary=/ibex/scratch/hohndor/km/v110-acyclic-nf1-20260825/km
  [[ $arm == candidate ]] && binary="$root/km"
  env KM_ROUTE=auto KM_TIMING=1 KM_ELC_TIMING=1 \
    /usr/bin/time -v "$binary" classify "$ont" \
    > /dev/null 2> "$root/profile/$arm.log"
done
echo PROFILE_COMPLETE
