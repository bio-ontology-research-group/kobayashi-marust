#!/usr/bin/env bash
#SBATCH --job-name=km-v26-15803-pair
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodelist=gpu510-32
#SBATCH --nodes=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:08:00
#SBATCH --output=/ibex/scratch/hohndor/km/v26-mixed-sparse-20260826/pair-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v26-mixed-sparse-20260826
baseline=/ibex/scratch/hohndor/km/v20-expanded-direct-20260826/km
candidate=$root/km
input=/ibex/scratch/hohndor/km/corpus/ore_ont_15803.owl
work=${SLURM_TMPDIR:-/tmp}/km-v26-15803-${SLURM_JOB_ID}
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
    stem="rep_${rep}-${arm}"
    /usr/bin/time -f '%e\t%M\t%x' -o "$work/$stem.measure" \
      env KM_ROUTE=auto KM_TIMING=1 "$binary" classify "$input" \
      > "$work/$stem.json" 2> "$work/$stem.stderr"
    read -r wall rss rc < "$work/$stem.measure"
    [[ $rc == 0 && -s "$work/$stem.json" ]]
    printf 'RESULT\trep=%s\tarm=%s\twall_s=%s\trss_kib=%s\tsha256=%s\n' \
      "$rep" "$arm" "$wall" "$rss" "$(sha256sum "$work/$stem.json" | awk '{print $1}')"
    cat "$work/$stem.stderr"
  done
  cmp "$work/rep_${rep}-baseline.json" "$work/rep_${rep}-candidate.json"
  echo "EXACT_MATCH rep=$rep"
done
echo TASK_COMPLETE
