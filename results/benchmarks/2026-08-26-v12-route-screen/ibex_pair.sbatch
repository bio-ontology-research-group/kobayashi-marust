#!/usr/bin/env bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --time=00:08:00
#SBATCH --array=0-8
#SBATCH --output=/ibex/scratch/hohndor/km/v12-route-screen-20260826/slurm-%A_%a.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/v12-route-screen-20260826
binary=/ibex/scratch/hohndor/km/v1-cert-overhead-v11-20260826/km
corpus=/ibex/scratch/hohndor/km/corpus
expected_binary_sha=decd89c157e8bcd9f8182589f0db03f606b8fc09fd6ce169525887a53533102c
onts=(9654 10073 9881 9944 15846 11311 1579 16596 10908)
routes=(ht_rules tab_race cb_absorb8 ht_full cb_plain8 ht_full seq_on elc htforce_race)
ont=${onts[$SLURM_ARRAY_TASK_ID]}
candidate_route=${routes[$SLURM_ARRAY_TASK_ID]}
input=$corpus/ore_ont_${ont}.owl
work=$root/work-${SLURM_ARRAY_JOB_ID}-${SLURM_ARRAY_TASK_ID}

mkdir -p "$root/results" "$work"
trap 'rm -rf "$work"' EXIT
[[ $(sha256sum "$binary" | awk '{print $1}') == "$expected_binary_sha" ]]
grep -q 'Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz' /proc/cpuinfo

run_arm() {
  local arm=$1
  local stem="ore_${ont}-${arm}"
  local -a environment=(KM_TIMING=1)
  if [[ $arm == auto ]]; then
    environment+=(KM_ROUTE=auto)
  elif [[ $candidate_route == htforce_race ]]; then
    environment+=(KM_ROUTE=manual KM_THREADS=16 KM_PAR_MEM_GB=18 KM_HT_MEM_GB=18)
    environment+=(KM_KEEP_CHAIN_AXIOMS=1 KM_ABSORB=1 KM_ABSORB_PORTFOLIO=1)
    environment+=(KM_HT_FORCE=1 KM_HT_MODE=race)
  else
    environment+=(KM_ROUTE="$candidate_route")
  fi
  timeout -k 5 240 /usr/bin/time -f '%e\t%M\t%x' \
    -o "$work/${stem}.measure" \
    env "${environment[@]}" "$binary" classify "$input" \
    > "$work/${stem}.json" 2> "$work/${stem}.stderr"
  read -r wall rss_kib rc < "$work/${stem}.measure"
  [[ $rc == 0 ]]
  install -m 644 "$work/${stem}.measure" "$root/results/${stem}.measure"
  install -m 644 "$work/${stem}.stderr" "$root/results/${stem}.stderr"
  install -m 644 "$work/${stem}.json" "$root/results/${stem}.json"
  printf 'RESULT\tontology=%s\tarm=%s\troute=%s\twall_s=%s\trss_kib=%s\n' \
    "$ont" "$arm" "$candidate_route" "$wall" "$rss_kib"
}

if (( SLURM_ARRAY_TASK_ID % 2 == 0 )); then order=(auto candidate); else order=(candidate auto); fi
for arm in "${order[@]}"; do run_arm "$arm"; done
cmp "$work/ore_${ont}-auto.json" "$work/ore_${ont}-candidate.json"
echo "EXACT ontology=$ont candidate_route=$candidate_route"
