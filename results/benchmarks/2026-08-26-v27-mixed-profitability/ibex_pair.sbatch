#!/usr/bin/env bash
#SBATCH --job-name=km-v27-mixed-pair
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodelist=gpu510-32
#SBATCH --nodes=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:10:00
#SBATCH --array=0-1%1
#SBATCH --output=/ibex/scratch/hohndor/km/v27-mixed-profitability-20260826/pair-%A_%a.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v27-mixed-profitability-20260826
baseline=/ibex/scratch/hohndor/km/v20-expanded-direct-20260826/km
candidate=$root/km
onts=(4604 15803)
ont=${onts[$SLURM_ARRAY_TASK_ID]}
input=/ibex/scratch/hohndor/km/corpus/ore_ont_${ont}.owl
work=${SLURM_TMPDIR:-/tmp}/km-v27-pair-${SLURM_JOB_ID}-${SLURM_ARRAY_TASK_ID}
mkdir -p "$root/results" "$work"
trap 'rm -rf "$work"' EXIT
grep -q BUILD_COMPLETE "$root"/build-*.out
[[ $(sha256sum "$baseline" | awk '{print $1}') == 33b536962de62789387d98479d9d4f5d28edc142eb9e7260e9805eb7d79b2c97 ]]
[[ $(sha256sum "$candidate" | awk '{print $1}') == $(awk '{print $1}' "$root/km.sha256") ]]
grep -q 'Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz' /proc/cpuinfo
for rep in 0 1 2; do
  if (( rep % 2 == 0 )); then arms=(baseline candidate); else arms=(candidate baseline); fi
  for arm in "${arms[@]}"; do
    [[ $arm == baseline ]] && binary=$baseline || binary=$candidate
    stem="ore_${ont}-rep_${rep}-${arm}"
    /usr/bin/time -f '%e\t%M\t%x' -o "$work/$stem.measure" \
      env KM_ROUTE=auto KM_TIMING=1 "$binary" classify "$input" \
      > "$work/$stem.json" 2> "$work/$stem.stderr"
    read -r wall rss rc < "$work/$stem.measure"
    [[ $rc == 0 && -s "$work/$stem.json" ]]
    printf 'RESULT\tontology=%s\trep=%s\tarm=%s\twall_s=%s\trss_kib=%s\tsha256=%s\n' \
      "$ont" "$rep" "$arm" "$wall" "$rss" "$(sha256sum "$work/$stem.json" | awk '{print $1}')"
    grep 'KM_TIMING.*route=' "$work/$stem.stderr" || true
  done
  cmp "$work/ore_${ont}-rep_${rep}-baseline.json" "$work/ore_${ont}-rep_${rep}-candidate.json"
  echo "EXACT_MATCH ontology=$ont rep=$rep"
done
echo "TASK_COMPLETE ontology=$ont"
