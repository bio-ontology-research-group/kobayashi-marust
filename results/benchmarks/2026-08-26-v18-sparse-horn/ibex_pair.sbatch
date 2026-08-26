#!/usr/bin/env bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:05:00
#SBATCH --array=0-2
#SBATCH --output=/ibex/scratch/hohndor/km/v18-sparse-horn-20260826/pair-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v18-sparse-horn-20260826
baseline=/ibex/scratch/hohndor/km/v13-flat-disjoint-20260826/km
candidate=$root/km
baseline_sha=86815df10d1cd90528fb7316005207e285fee7b02abbcb7ba9e68a4225060559
candidate_sha=$(awk '{print $1}' "$root/km.sha256")
ont=3377
input=/ibex/scratch/hohndor/km/corpus/ore_ont_${ont}.owl
work=${SLURM_TMPDIR:-/tmp}/km-v18-pair-${SLURM_JOB_ID}-${SLURM_ARRAY_TASK_ID}
mkdir -p "$root/results" "$work"
trap 'rm -rf "$work"' EXIT
[[ $(sha256sum "$baseline" | awk '{print $1}') == "$baseline_sha" ]]
[[ $(sha256sum "$candidate" | awk '{print $1}') == "$candidate_sha" ]]
grep -q 'Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz' /proc/cpuinfo

for arm in baseline candidate; do
  if [[ $arm == baseline ]]; then binary=$baseline; else binary=$candidate; fi
  stem="ore_${ont}-rep_${SLURM_ARRAY_TASK_ID}-${arm}"
  /usr/bin/time -f '%e\t%M\t%x' -o "$work/${stem}.measure" \
    env KM_ROUTE=auto KM_TIMING=1 "$binary" classify "$input" \
    > "$work/${stem}.json" 2> "$work/${stem}.stderr"
  read -r wall rss rc < "$work/${stem}.measure"
  [[ $rc == 0 && -s "$work/${stem}.json" ]]
  for suffix in measure stderr json; do
    install -m 644 "$work/${stem}.$suffix" "$root/results/${stem}.$suffix"
  done
  printf 'RESULT\tontology=%s\trep=%s\tarm=%s\twall_s=%s\trss_kib=%s\n' \
    "$ont" "$SLURM_ARRAY_TASK_ID" "$arm" "$wall" "$rss"
done
cmp "$work/ore_${ont}-rep_${SLURM_ARRAY_TASK_ID}-baseline.json" \
    "$work/ore_${ont}-rep_${SLURM_ARRAY_TASK_ID}-candidate.json"
echo EXACT_MATCH
