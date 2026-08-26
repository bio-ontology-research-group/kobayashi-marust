#!/usr/bin/env bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --time=00:08:00
#SBATCH --array=0-5
#SBATCH --output=/ibex/scratch/hohndor/km/v12-top-profiles-20260826/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v12-top-profiles-20260826
binary=/ibex/scratch/hohndor/km/v1-cert-overhead-v11-20260826/km
corpus=/ibex/scratch/hohndor/km/corpus
expected_binary_sha=decd89c157e8bcd9f8182589f0db03f606b8fc09fd6ce169525887a53533102c
onts=(3215 14817 4669 9724 10621 15703)
ont=${onts[$SLURM_ARRAY_TASK_ID]}
mkdir -p "$root/results"
[[ $(sha256sum "$binary" | awk '{print $1}') == "$expected_binary_sha" ]]
grep -q 'Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz' /proc/cpuinfo
timeout -k 5 300 "$binary" profile "$corpus/ore_ont_${ont}.owl" \
  > "$root/results/ore_${ont}.profile.json"
python3 -c 'import json,sys; json.load(open(sys.argv[1]))' "$root/results/ore_${ont}.profile.json"
printf 'PROFILE_OK\tontology=%s\n' "$ont"
