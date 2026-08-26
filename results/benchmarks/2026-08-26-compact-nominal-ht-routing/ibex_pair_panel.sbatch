#!/bin/bash
#SBATCH --job-name=km-v110-v8-nominal-pair
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --array=0-24%6
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --time=00:05:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1-cert-overhead-v8-20260826/panel/slurm-%A_%a.out

set -euo pipefail
v5_root=/ibex/scratch/hohndor/km/v1-cert-overhead-v5-20260825
root=/ibex/scratch/hohndor/km/v1-cert-overhead-v8-20260826
corpus=/ibex/scratch/hohndor/km/corpus
v5_hash=e9f06cda45e0e9256984167b650ec6664754b81a837628d3ff63bcd0a6d06620
v8_hash=e8e8f1a69978035f173ec47ddaa86ba4ea20d33f4b2ae89f3195ed3ebd357950
selected=(148 960 1790 3050 3795 4834 5943 6060 6765 7025 7320 7474 8322 8999 9668 10242 10594 13621 14194 14896)
controls=(1340 14450 3905 15615 9014)
ids=("${selected[@]}" "${controls[@]}")
id=${ids[$SLURM_ARRAY_TASK_ID]}
input=$corpus/ore_ont_${id}.owl
cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]
[[ $(sha256sum "$v5_root/km" | cut -d' ' -f1) == "$v5_hash" ]]
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$v8_hash" ]]
work=${SLURM_TMPDIR:-/tmp}/km-v110-v8-panel-${SLURM_JOB_ID}
mkdir -p "$work" "$root/panel/results"
trap 'rm -rf "$work"' EXIT

for arm in v5 v8; do
  if [[ $arm == v5 ]]; then bin=$v5_root/km; else bin=$root/km; fi
  timeout 240 /usr/bin/time -f '%e %M %x' -o "$work/$arm.measure" \
    env KM_ROUTE=auto KM_TIMING=1 "$bin" classify "$input" \
      > "$work/$arm.json" 2> "$work/$arm.stderr"
  read -r wall rss exit_code < "$work/$arm.measure"
  [[ $exit_code == 0 ]]
  echo "MEASURE ontology=$id arm=$arm wall=$wall rss_kib=$rss exit=$exit_code"
done

cmp "$work/v5.json" "$work/v8.json"
if (( SLURM_ARRAY_TASK_ID < ${#selected[@]} )); then
  grep -q 'route=ht_general' "$work/v8.stderr"
  expected_route=ht_general
else
  ! grep -q 'route=ht_general' "$work/v8.stderr"
  expected_route=unchanged-control
fi
sha256sum "$work/v8.json"
install -m 644 "$work/v5.measure" "$root/panel/results/${id}.v5.measure"
install -m 644 "$work/v8.measure" "$root/panel/results/${id}.v8.measure"
install -m 644 "$work/v8.stderr" "$root/panel/results/${id}.v8.stderr"
echo "EXACT_PAIR ontology=$id route=$expected_route"
