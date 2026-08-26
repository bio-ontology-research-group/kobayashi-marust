#!/usr/bin/env bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --time=00:08:00
#SBATCH --array=0-5
#SBATCH --output=/ibex/scratch/hohndor/km/v16-mirror-query-split-20260826/pair-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v16-mirror-query-split-20260826
baseline=/ibex/scratch/hohndor/km/v13-flat-disjoint-20260826/km
candidate=$root/km
baseline_sha=86815df10d1cd90528fb7316005207e285fee7b02abbcb7ba9e68a4225060559
candidate_sha=$(awk '{print $1}' "$root/km.sha256")
onts=(4669 4669 4669 4669 4669 4669)
ont=${onts[$SLURM_ARRAY_TASK_ID]}
input=/ibex/scratch/hohndor/km/corpus/ore_ont_${ont}.owl
work=${SLURM_TMPDIR:-/tmp}/km-v16-pair-${SLURM_JOB_ID}-${SLURM_ARRAY_TASK_ID}
mkdir -p "$root/results" "$work"
trap 'rm -rf "$work"' EXIT
[[ $(sha256sum "$baseline" | awk '{print $1}') == "$baseline_sha" ]]
[[ $(sha256sum "$candidate" | awk '{print $1}') == "$candidate_sha" ]]
[[ -s "$input" ]]
grep -q 'Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz' /proc/cpuinfo

for arm in baseline candidate; do
  if [[ $arm == baseline ]]; then binary=$baseline; else binary=$candidate; fi
  stem="ore_${ont}-rep_${SLURM_ARRAY_TASK_ID}-${arm}"
  set +e
  timeout -k 5 240 /usr/bin/time -f '%e\t%M\t%x' -o "$work/${stem}.measure" \
    env KM_ROUTE=auto KM_TIMING=1 "$binary" classify "$input" \
    > "$work/${stem}.json" 2> "$work/${stem}.stderr"
  command_rc=$?
  set -e
  install -m 644 "$work/${stem}.measure" "$root/results/${stem}.measure"
  install -m 644 "$work/${stem}.stderr" "$root/results/${stem}.stderr"
  install -m 644 "$work/${stem}.json" "$root/results/${stem}.json"
  read -r wall rss_kib rc < "$work/${stem}.measure"
  [[ $command_rc == 0 && $rc == 0 && -s "$work/${stem}.json" ]]
  /usr/bin/python3 - "$work/${stem}.json" <<'PY'
import json, pathlib, sys
value = json.loads(pathlib.Path(sys.argv[1]).read_text())
assert isinstance(value, dict) and value
PY
  printf 'RESULT\tontology=%s\trep=%s\tarm=%s\twall_s=%s\trss_kib=%s\n' \
    "$ont" "$SLURM_ARRAY_TASK_ID" "$arm" "$wall" "$rss_kib"
done
cmp "$work/ore_${ont}-rep_${SLURM_ARRAY_TASK_ID}-baseline.json" \
    "$work/ore_${ont}-rep_${SLURM_ARRAY_TASK_ID}-candidate.json"
