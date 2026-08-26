#!/usr/bin/env bash
#SBATCH --job-name=km-v21-abox-pair
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodelist=gpu510-32
#SBATCH --nodes=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:08:00
#SBATCH --array=0-7%1
#SBATCH --output=/ibex/scratch/hohndor/km/v21-abox-direct-20260826/pair-%A_%a.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v21-abox-direct-20260826
baseline=/ibex/scratch/hohndor/km/v20-expanded-direct-20260826/km
candidate=$root/km
onts=(3560 5519 6477 7246 10073 11315 9400 9499)
ont=${onts[$SLURM_ARRAY_TASK_ID]}
input=/ibex/scratch/hohndor/km/corpus/ore_ont_${ont}.owl
work=${SLURM_TMPDIR:-/tmp}/km-v21-pair-${SLURM_JOB_ID}-${SLURM_ARRAY_TASK_ID}
mkdir -p "$root/results" "$work"
trap 'rm -rf "$work"' EXIT
grep -qx 'BUILD_COMPLETE' "$root/build-50876935.out"
[[ $(sha256sum "$baseline" | awk '{print $1}') == 33b536962de62789387d98479d9d4f5d28edc142eb9e7260e9805eb7d79b2c97 ]]
[[ $(sha256sum "$candidate" | awk '{print $1}') == $(awk '{print $1}' "$root/km.sha256") ]]
grep -q 'Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz' /proc/cpuinfo

for rep in 0 1 2; do
  if (( rep % 2 == 0 )); then arms=(baseline candidate); else arms=(candidate baseline); fi
  for arm in "${arms[@]}"; do
    if [[ $arm == baseline ]]; then binary=$baseline; else binary=$candidate; fi
    stem="ore_${ont}-rep_${rep}-${arm}"
    /usr/bin/time -f '%e\t%M\t%x' -o "$work/${stem}.measure" \
      env KM_ROUTE=auto KM_TIMING=1 "$binary" classify "$input" \
      > "$work/${stem}.json" 2> "$work/${stem}.stderr"
    read -r wall rss rc < "$work/${stem}.measure"
    [[ $rc == 0 && -s "$work/${stem}.json" ]]
    sha=$(sha256sum "$work/${stem}.json" | awk '{print $1}')
    printf 'RESULT\tontology=%s\trep=%s\tarm=%s\twall_s=%s\trss_kib=%s\tsha256=%s\n' \
      "$ont" "$rep" "$arm" "$wall" "$rss" "$sha"
    install -m 644 "$work/${stem}.measure" "$root/results/${stem}.measure"
    install -m 644 "$work/${stem}.stderr" "$root/results/${stem}.stderr"
  done
  cmp "$work/ore_${ont}-rep_${rep}-baseline.json" "$work/ore_${ont}-rep_${rep}-candidate.json"
  echo "EXACT_MATCH ontology=$ont rep=$rep"
done
echo "TASK_COMPLETE ontology=$ont"
