#!/usr/bin/env bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --time=00:08:00
#SBATCH --array=0-8
#SBATCH --output=/ibex/scratch/hohndor/km/v12-safe-route-screen-20260826/slurm-%A_%a.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/v12-safe-route-screen-20260826
binary=/ibex/scratch/hohndor/km/v1-cert-overhead-v11-20260826/km
corpus=/ibex/scratch/hohndor/km/corpus
expected_binary_sha=decd89c157e8bcd9f8182589f0db03f606b8fc09fd6ce169525887a53533102c
onts=(9654 9944 9944 11311 11311 10908 10908 9881 9881)
routes=(cb_plain16 elc ht_general elc ht_general ht_general certified_nominals ht_general certified_nominals)
ont=${onts[$SLURM_ARRAY_TASK_ID]}
candidate_route=${routes[$SLURM_ARRAY_TASK_ID]}
input=$corpus/ore_ont_${ont}.owl
work=$root/work-${SLURM_ARRAY_JOB_ID}-${SLURM_ARRAY_TASK_ID}

mkdir -p "$root/results" "$work"
trap 'rm -rf "$work"' EXIT
[[ $(sha256sum "$binary" | awk '{print $1}') == "$expected_binary_sha" ]]
grep -q 'Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz' /proc/cpuinfo

run_arm() {
  local arm=$1 stem="ore_${ont}-${candidate_route}-$1"
  local route=auto
  [[ $arm == candidate ]] && route=$candidate_route
  timeout -k 5 240 /usr/bin/time -f '%e\t%M\t%x' -o "$work/$stem.measure" \
    env KM_TIMING=1 KM_ROUTE="$route" "$binary" classify "$input" \
    > "$work/$stem.json" 2> "$work/$stem.stderr"
  read -r wall rss_kib rc < "$work/$stem.measure"
  [[ $rc == 0 ]]
  for ext in measure json stderr; do
    install -m 644 "$work/$stem.$ext" "$root/results/$stem.$ext"
  done
  printf 'RESULT\tontology=%s\tarm=%s\troute=%s\twall_s=%s\trss_kib=%s\n' \
    "$ont" "$arm" "$candidate_route" "$wall" "$rss_kib"
}

if (( SLURM_ARRAY_TASK_ID % 2 == 0 )); then order=(auto candidate); else order=(candidate auto); fi
for arm in "${order[@]}"; do run_arm "$arm"; done
cmp "$work/ore_${ont}-${candidate_route}-auto.json" \
    "$work/ore_${ont}-${candidate_route}-candidate.json"
echo "EXACT ontology=$ont candidate_route=$candidate_route"
