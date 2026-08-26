#!/usr/bin/env bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --time=00:04:00
#SBATCH --array=0-1
#SBATCH --output=/ibex/scratch/hohndor/km/v12-bridge-profile-trace-20260826/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v12-bridge-profile-trace-20260826
binary=/ibex/scratch/hohndor/km/v1-cert-overhead-v11-20260826/km
expected_binary_sha=decd89c157e8bcd9f8182589f0db03f606b8fc09fd6ce169525887a53533102c
onts=(3215 14817); ont=${onts[$SLURM_ARRAY_TASK_ID]}
mkdir -p "$root/results"
[[ $(sha256sum "$binary" | awk '{print $1}') == "$expected_binary_sha" ]]
grep -q 'Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz' /proc/cpuinfo
timeout -k 5 240 /usr/bin/time -f '%e\t%M\t%x' -o "$root/results/ore_${ont}.measure" \
  env KM_ROUTE=auto KM_TIMING=1 KM_HT_TRACE=1 KM_BRIDGE_PROGRESS=1 KM_BRIDGE_PHASES=1 \
  "$binary" classify "/ibex/scratch/hohndor/km/corpus/ore_ont_${ont}.owl" \
  > "$root/results/ore_${ont}.json" 2> "$root/results/ore_${ont}.stderr"
read -r wall rss rc < "$root/results/ore_${ont}.measure"; [[ $rc == 0 ]]
printf 'PROFILE_RESULT\tontology=%s\twall_s=%s\trss_kib=%s\n' "$ont" "$wall" "$rss"
