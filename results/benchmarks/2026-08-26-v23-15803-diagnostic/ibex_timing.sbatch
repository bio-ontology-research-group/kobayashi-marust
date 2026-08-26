#!/usr/bin/env bash
#SBATCH --job-name=km-15803-timing
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodelist=gpu510-32
#SBATCH --nodes=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:08:00
#SBATCH --output=/ibex/scratch/hohndor/km/v23-15803-diagnostic-20260826/timing-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/v23-15803-diagnostic-20260826
binary=/ibex/scratch/hohndor/km/v20-expanded-direct-20260826/km
input=/ibex/scratch/hohndor/km/corpus/ore_ont_15803.owl
expected=33b536962de62789387d98479d9d4f5d28edc142eb9e7260e9805eb7d79b2c97
[[ $(sha256sum "$binary" | awk '{print $1}') == "$expected" ]]
grep -q 'Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz' /proc/cpuinfo
work=${SLURM_TMPDIR:-/tmp}/km-15803-timing-${SLURM_JOB_ID}
mkdir -p "$root/results" "$work"
trap 'rm -rf "$work"' EXIT
for rep in 0 1; do
  stem=ore_15803-rep_${rep}
  /usr/bin/time -f '%e\t%M\t%x' -o "$work/${stem}.measure" \
    env KM_ROUTE=auto KM_TIMING=1 KM_PROF_TIME=1 KM_BRIDGE_PHASES=1 \
      "$binary" classify "$input" > "$work/${stem}.json" 2> "$work/${stem}.stderr"
  read -r wall rss rc < "$work/${stem}.measure"
  [[ $rc == 0 && -s "$work/${stem}.json" ]]
  printf 'RESULT\trep=%s\twall_s=%s\trss_kib=%s\tsha256=%s\n' \
    "$rep" "$wall" "$rss" "$(sha256sum "$work/${stem}.json" | awk '{print $1}')"
  install -m 644 "$work/${stem}.measure" "$root/results/${stem}.measure"
  install -m 644 "$work/${stem}.stderr" "$root/results/${stem}.stderr"
done
echo TASK_COMPLETE
