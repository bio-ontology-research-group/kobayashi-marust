#!/bin/bash
#SBATCH --job-name=km-6934-profile
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/6934-tail-20260813/profile-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/6934-tail-20260813
binary=/ibex/scratch/hohndor/km/candidate-78d5674-atomic-abox-20260813/km
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_6934.owl
expected=d19938110369da96167feddf2a257550bf80aca1793afd40154d18d303663f8e

cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected" ]]
mkdir -p "$root"
output=${SLURM_TMPDIR:-/tmp}/ore_ont_6934-${SLURM_JOB_ID}.json
/usr/bin/time -f 'PROFILE_TIME elapsed=%e peak_kb=%M exit=%x' \
  env -i PATH=/usr/bin:/bin HOME="$HOME" KM_ROUTE=auto \
    KM_BRIDGE_PROGRESS=1 KM_HT_STATS=1 \
    "$binary" classify "$ontology" > "$output" 2> "$root/trace-${SLURM_JOB_ID}.log"
test -s "$output"
grep -q 'SELECTED_ROUTE: nominal_ni_abox' "$root/trace-${SLURM_JOB_ID}.log"
grep -q 'PROFILE_TIME .*exit=0' "$root/trace-${SLURM_JOB_ID}.log"
sha256sum "$output"
echo PROFILE_COMPLETE
