#!/usr/bin/env bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --time=00:10:00
#SBATCH --output=/ibex/scratch/hohndor/km/v12-mirror-workers-20260826/slurm-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/v12-mirror-workers-20260826
candidate=/ibex/scratch/hohndor/km/v12-combined-candidate-20260826/km-candidate
candidate_sha=6313469c48e07ff7003eeb635fc6c6b3b9055dea12000f85a96deddbf563c55e
input=/ibex/scratch/hohndor/km/corpus/ore_ont_4669.owl
work=$root/work-${SLURM_JOB_ID}

mkdir -p "$root/results" "$work"
trap 'rm -rf "$work"' EXIT
[[ $(sha256sum "$candidate" | awk '{print $1}') == "$candidate_sha" ]]
[[ -s "$input" ]]
grep -q 'Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz' /proc/cpuinfo

for workers in 1 2 4; do
  stem="workers-${workers}"
  set +e
  timeout -k 5 240 /usr/bin/time -f '%e\t%M\t%x' -o "$work/${stem}.measure" \
    env KM_ROUTE=auto KM_TIMING=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE="$workers" \
    "$candidate" classify "$input" > "$work/${stem}.json" 2> "$work/${stem}.stderr"
  command_rc=$?
  set -e
  install -m 644 "$work/${stem}.measure" "$root/results/${stem}.measure"
  install -m 644 "$work/${stem}.stderr" "$root/results/${stem}.stderr"
  install -m 644 "$work/${stem}.json" "$root/results/${stem}.json"
  read -r wall rss_kib rc < "$work/${stem}.measure"
  [[ $command_rc == 0 && $rc == 0 && -s "$work/${stem}.json" ]]
  python3 - "$work/${stem}.json" <<'PY'
import json, pathlib, sys
value = json.loads(pathlib.Path(sys.argv[1]).read_text())
assert isinstance(value, dict) and value
PY
  printf 'RESULT\tworkers=%s\twall_s=%s\trss_kib=%s\n' "$workers" "$wall" "$rss_kib"
done

cmp "$work/workers-1.json" "$work/workers-2.json"
cmp "$work/workers-1.json" "$work/workers-4.json"
