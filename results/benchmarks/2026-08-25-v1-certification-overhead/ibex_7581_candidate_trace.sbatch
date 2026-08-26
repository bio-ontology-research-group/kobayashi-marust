#!/bin/bash
#SBATCH --job-name=km-v110-7581-trace
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:06:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1-cert-overhead-v4-20260825/7581-trace-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v1-cert-overhead-v4-20260825
bin=$root/km
expected=4d5bc52a185ce52aa8dedd4bafceac45d7ed67fb1392cf2d64161bb94261c534
[[ $(sha256sum "$bin" | cut -d' ' -f1) == "$expected" ]]
work=${SLURM_TMPDIR:-/tmp/km-v110-7581-${SLURM_JOB_ID}}
mkdir -p "$work"
trap 'rm -rf "$work"' EXIT
env KM_ROUTE=auto KM_ROUTE_TRACE=1 KM_TIMING=1 KM_PROF_TIME=1 KM_HT_CERT_TRACE=1 \
  KM_HT_STATS=1 KM_BRIDGE_PHASES=1 \
  /usr/bin/time -v "$bin" classify /ibex/scratch/hohndor/km/corpus/ore_ont_7581.owl \
  > "$work/out.json"
sha256sum "$work/out.json"
echo TRACE_COMPLETE
