#!/usr/bin/env bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --time=00:05:00
#SBATCH --array=0-1
#SBATCH --output=/ibex/scratch/hohndor/km/v12-bridge-recovery-20260826/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v12-bridge-recovery-20260826
binary=/ibex/scratch/hohndor/km/v1-cert-overhead-v11-20260826/km
corpus=/ibex/scratch/hohndor/km/corpus
expected_binary_sha=decd89c157e8bcd9f8182589f0db03f606b8fc09fd6ce169525887a53533102c
onts=(9944 11311)
ont=${onts[$SLURM_ARRAY_TASK_ID]}
work=$root/work-${SLURM_ARRAY_JOB_ID}-${SLURM_ARRAY_TASK_ID}
mkdir -p "$root/results" "$work"
trap 'rm -rf "$work"' EXIT
[[ $(sha256sum "$binary" | awk '{print $1}') == "$expected_binary_sha" ]]
grep -q 'Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz' /proc/cpuinfo
for repetition in 1 2 3; do
  if (( repetition % 2 )); then order=(auto bridge); else order=(bridge auto); fi
  for arm in "${order[@]}"; do
    route=auto; [[ $arm == bridge ]] && route=ht_bridge
    stem=ore_${ont}-r${repetition}-${arm}
    timeout -k 5 240 /usr/bin/time -f '%e\t%M\t%x' -o "$work/$stem.measure" \
      env KM_ROUTE="$route" "$binary" classify "$corpus/ore_ont_${ont}.owl" \
      > "$work/$stem.json" 2> "$work/$stem.stderr"
    read -r wall rss rc < "$work/$stem.measure"; [[ $rc == 0 ]]
    for ext in measure json stderr; do install -m 644 "$work/$stem.$ext" "$root/results/$stem.$ext"; done
    printf 'RESULT\tontology=%s\trepetition=%s\tarm=%s\twall_s=%s\trss_kib=%s\n' "$ont" "$repetition" "$arm" "$wall" "$rss"
  done
  cmp "$work/ore_${ont}-r${repetition}-auto.json" "$work/ore_${ont}-r${repetition}-bridge.json"
done
echo "EXACT ontology=$ont route=ht_bridge repetitions=3"
