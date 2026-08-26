#!/bin/bash
#SBATCH --job-name=km-v1-v036-4604-phases
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1-cert-overhead-20260825/4604-phase-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v1-cert-overhead-20260825
mkdir -p "$root"
ont=/ibex/scratch/hohndor/km/corpus/ore_ont_4604.owl
v1=/ibex/scratch/hohndor/km/v110-baseline-20260825/km
v036=/ibex/scratch/hohndor/km/v036-large-clean-20260815/km

[[ $(sha256sum "$v1" | cut -d' ' -f1) == 3f313fe954e2fc779364a4999ba1d0ee6118aaeef0e1bf6e1cbc49ed7a196087 ]]
[[ $(sha256sum "$v036" | cut -d' ' -f1) == bbef8d7efbc6a6b8aefa3c44e55f40fb90916f1974d6c8086eb77bb7ac1d074f ]]
work=${SLURM_TMPDIR:-/tmp/km-v1-cert-overhead-${SLURM_JOB_ID}}
mkdir -p "$work"
trap 'rm -rf "$work"' EXIT

for arm in v036 v1; do
  if [[ $arm == v036 ]]; then bin=$v036; else bin=$v1; fi
  echo "BEGIN arm=$arm binary=$(sha256sum "$bin" | cut -d' ' -f1)"
  env KM_ROUTE=auto KM_TIMING=1 KM_PROF_TIME=1 KM_HT_CERT_TRACE=1 \
    KM_HT_STATS=1 KM_BRIDGE_PHASES=1 \
    /usr/bin/time -v "$bin" classify "$ont" \
      > "$work/$arm.json" 2> "$root/$arm.stderr"
  sha256sum "$work/$arm.json"
  sed -n '/KM_TIMING\|KM_STATS\|KM_HT_CERT_TRACE\|KM_BRIDGE_PHASE\|Elapsed (wall clock)\|Maximum resident set/p' \
    "$root/$arm.stderr"
  echo "END arm=$arm"
done

cmp "$work/v036.json" "$work/v1.json"
echo PHASE_PAIR_COMPLETE
