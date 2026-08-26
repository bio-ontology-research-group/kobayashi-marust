#!/bin/bash
#SBATCH --job-name=km-v110-elc-profile
#SBATCH --partition=debug
#SBATCH --array=0-3%2
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --time=00:20:00
#SBATCH --output=/ibex/scratch/hohndor/km/v1-cert-overhead-v5-20260825/elc-profile/slurm-%A_%a.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/v1-cert-overhead-v5-20260825
onts=(ore_ont_15280.owl ore_ont_13482.owl ore_ont_1012.owl ore_ont_10750.owl)
ont=${onts[$SLURM_ARRAY_TASK_ID]}
out=$root/elc-profile/$ont
tmp=${SLURM_TMPDIR:-/tmp/km-v110-elc-profile-$SLURM_JOB_ID}
mkdir -p "$root/elc-profile" "$tmp"
trap 'rm -rf "$tmp"' EXIT

sha256sum "$root/km"
/usr/bin/time -v env \
  KM_ROUTE=auto \
  KM_TIMING=1 \
  KM_OFN_TIMING=1 \
  KM_ELC_PROFILE=1 \
  timeout --signal=TERM --kill-after=10s 240s \
  "$root/km" classify "/ibex/scratch/hohndor/km/corpus/$ont" \
  > "$tmp/result.json" 2> "$out.stderr"
sha256sum "$tmp/result.json" > "$out.result.sha256"
mv "$tmp/result.json" "$out.result.json"
