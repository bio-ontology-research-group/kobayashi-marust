#!/usr/bin/env bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --time=00:04:00
#SBATCH --array=0-10
#SBATCH --output=/ibex/scratch/hohndor/km/v12-top-route-screen-20260826/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v12-top-route-screen-20260826
binary=/ibex/scratch/hohndor/km/v1-cert-overhead-v11-20260826/km
corpus=/ibex/scratch/hohndor/km/corpus
expected_binary_sha=decd89c157e8bcd9f8182589f0db03f606b8fc09fd6ce169525887a53533102c
onts=(3215 3215 4669 4669 4669 9724 10621 15703 15703 15703 15703)
routes=(auto_w4 auto_w8 production_all ht_bridge elc ht_bridge auto_w8 elc elc_cert ht_bridge production_all8)
ont=${onts[$SLURM_ARRAY_TASK_ID]}; candidate=${routes[$SLURM_ARRAY_TASK_ID]}
work=$root/work-${SLURM_ARRAY_JOB_ID}-${SLURM_ARRAY_TASK_ID}
mkdir -p "$root/results" "$work"; trap 'rm -rf "$work"' EXIT
[[ $(sha256sum "$binary" | awk '{print $1}') == "$expected_binary_sha" ]]
grep -q 'Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz' /proc/cpuinfo

run_arm() {
  local arm=$1 stem=ore_${ont}-${candidate}-$1
  local -a envs=(KM_TIMING=1 KM_ROUTE=auto)
  if [[ $arm == candidate ]]; then
    case $candidate in
      auto_w4) envs+=(KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=4) ;;
      auto_w8) envs+=(KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=8) ;;
      *) envs=(KM_TIMING=1 KM_ROUTE="$candidate") ;;
    esac
  fi
  timeout -k 5 110 /usr/bin/time -f '%e\t%M\t%x' -o "$work/$stem.measure" \
    env "${envs[@]}" "$binary" classify "$corpus/ore_ont_${ont}.owl" \
    > "$work/$stem.json" 2> "$work/$stem.stderr"
  read -r wall rss rc < "$work/$stem.measure"; [[ $rc == 0 ]]
  for ext in measure json stderr; do install -m 644 "$work/$stem.$ext" "$root/results/$stem.$ext"; done
  printf 'RESULT\tontology=%s\tarm=%s\tcandidate=%s\twall_s=%s\trss_kib=%s\n' "$ont" "$arm" "$candidate" "$wall" "$rss"
}

if (( SLURM_ARRAY_TASK_ID % 2 )); then order=(candidate auto); else order=(auto candidate); fi
for arm in "${order[@]}"; do run_arm "$arm"; done
cmp "$work/ore_${ont}-${candidate}-auto.json" "$work/ore_${ont}-${candidate}-candidate.json"
echo "EXACT ontology=$ont candidate=$candidate"
