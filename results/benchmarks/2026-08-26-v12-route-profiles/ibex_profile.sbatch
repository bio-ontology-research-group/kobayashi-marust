#!/usr/bin/env bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=12G
#SBATCH --time=00:05:00
#SBATCH --array=0-1
#SBATCH --output=/ibex/scratch/hohndor/km/v12-route-profiles-20260826/slurm-%A_%a.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/v12-route-profiles-20260826
binary=/ibex/scratch/hohndor/km/v1-cert-overhead-v11-20260826/km
corpus=/ibex/scratch/hohndor/km/corpus
expected_binary_sha=decd89c157e8bcd9f8182589f0db03f606b8fc09fd6ce169525887a53533102c
onts=(8480 9654 9881 9944 10908 11311 15846 16596)
ont=${onts[$SLURM_ARRAY_TASK_ID]}

mkdir -p "$root/results"
[[ $(sha256sum "$binary" | awk '{print $1}') == "$expected_binary_sha" ]]
grep -q 'Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz' /proc/cpuinfo
timeout -k 5 120 "$binary" profile "$corpus/ore_ont_${ont}.owl" \
  > "$root/results/ore_${ont}.profile.json"
python3 -c 'import json,sys; json.load(open(sys.argv[1]))' \
  "$root/results/ore_${ont}.profile.json"
printf 'PROFILE_OK\tontology=%s\n' "$ont"
