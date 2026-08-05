#!/bin/bash
#SBATCH --job-name=km1194-global-upper
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:08:00
#SBATCH --exclusive
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/1194-global-upper-20260805/slurm-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/1194-global-upper-20260805
test -x "$root/km"
test "$(stat -c %s "$root/input.json")" -eq 270429794

export KM_ELC_CERT=1
export KM_ELC_HOIST=1
export KM_ELC_TARGET_VIOLATIONS=CL_0000071
export KM_ELC_TARGET_REPAIR=1
export KM_ELC_TARGET_PROJECT=1
export KM_ELC_TARGET_ROOT_ONLY=1
export KM_ELC_QUOTIENT_UPPER=1
export KM_ELC_QUOTIENT_LEVELS=2
export KM_ELC_QUOTIENT_ROLE_SIGNATURE=1
export KM_ELC_QUOTIENT_ROLE_FILTER=UBREL_0000002
export KM_ELC_QUOTIENT_FAST_TWO=1
export KM_ELC_QUOTIENT_INCLUDE_OUTSIDE=1
export KM_ELC_QUOTIENT_ALL=1
export RAYON_NUM_THREADS=16

/usr/bin/time -v timeout --signal=TERM --kill-after=10s 420 \
  "$root/km" elc < "$root/input.json" > "$root/result.json" 2> "$root/gate.log"
