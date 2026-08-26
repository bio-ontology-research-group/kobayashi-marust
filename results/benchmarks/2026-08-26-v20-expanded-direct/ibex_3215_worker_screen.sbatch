#!/usr/bin/env bash
#SBATCH --job-name=km-v20-3215-workers
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodelist=gpu510-32
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:08:00
#SBATCH --output=/ibex/scratch/hohndor/km/v20-expanded-direct-20260826/worker-3215-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v20-expanded-direct-20260826
binary=$root/km
input=/ibex/scratch/hohndor/km/corpus/ore_ont_3215.owl
work=${SLURM_TMPDIR:-/tmp}/km-v20-3215-${SLURM_JOB_ID}
mkdir -p "$work" "$root/worker-3215-results"
trap 'rm -rf "$work"' EXIT
grep -qx 'BUILD_COMPLETE' "$root/build-50876082.out"
[[ $(sha256sum "$binary" | awk '{print $1}') == 33b536962de62789387d98479d9d4f5d28edc142eb9e7260e9805eb7d79b2c97 ]]
grep -q 'Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz' /proc/cpuinfo

for workers in 2 4 8; do
  stem=workers_${workers}
  /usr/bin/time -f '%e\t%M\t%x' -o "$work/${stem}.measure" \
    env KM_ROUTE=auto KM_TIMING=1 KM_BRIDGE_SUBJECT_WORKERS=$workers \
    "$binary" classify "$input" > "$work/${stem}.json" 2> "$work/${stem}.stderr"
  read -r wall rss rc < "$work/${stem}.measure"
  [[ $rc == 0 && -s "$work/${stem}.json" ]]
  sha=$(sha256sum "$work/${stem}.json" | awk '{print $1}')
  printf 'RESULT\tontology=3215\tworkers=%s\twall_s=%s\trss_kib=%s\tsha256=%s\n' \
    "$workers" "$wall" "$rss" "$sha"
  install -m 644 "$work/${stem}.measure" "$root/worker-3215-results/${stem}.measure"
  install -m 644 "$work/${stem}.stderr" "$root/worker-3215-results/${stem}.stderr"
  if [[ $workers != 2 ]]; then
    cmp "$work/workers_2.json" "$work/${stem}.json"
    echo "EXACT_MATCH workers=2/$workers"
  fi
done
echo SCREEN_COMPLETE
