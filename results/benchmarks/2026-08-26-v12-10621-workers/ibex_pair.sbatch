#!/usr/bin/env bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --time=00:06:00
#SBATCH --output=/ibex/scratch/hohndor/km/v12-10621-workers-20260826/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v12-10621-workers-20260826
binary=/ibex/scratch/hohndor/km/v1-cert-overhead-v11-20260826/km
input=/ibex/scratch/hohndor/km/corpus/ore_ont_10621.owl
expected_binary_sha=decd89c157e8bcd9f8182589f0db03f606b8fc09fd6ce169525887a53533102c
work=$root/work-$SLURM_JOB_ID
mkdir -p "$root/results" "$work"; trap 'rm -rf "$work"' EXIT
[[ $(sha256sum "$binary" | awk '{print $1}') == "$expected_binary_sha" ]]
grep -q 'Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz' /proc/cpuinfo
for repetition in 1 2 3; do
  if (( repetition % 2 )); then order=(default workers8); else order=(workers8 default); fi
  for arm in "${order[@]}"; do
    stem=ore_10621-r${repetition}-${arm}; envs=(KM_ROUTE=auto)
    [[ $arm == workers8 ]] && envs+=(KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=8)
    timeout -k 5 240 /usr/bin/time -f '%e\t%M\t%x' -o "$work/$stem.measure" \
      env "${envs[@]}" "$binary" classify "$input" > "$work/$stem.json" 2> "$work/$stem.stderr"
    read -r wall rss rc < "$work/$stem.measure"; [[ $rc == 0 ]]
    for ext in measure json stderr; do install -m 644 "$work/$stem.$ext" "$root/results/$stem.$ext"; done
    printf 'RESULT\trepetition=%s\tarm=%s\twall_s=%s\trss_kib=%s\n' "$repetition" "$arm" "$wall" "$rss"
  done
  cmp "$work/ore_10621-r${repetition}-default.json" "$work/ore_10621-r${repetition}-workers8.json"
done
echo 'EXACT ontology=10621 workers=8 repetitions=3'
