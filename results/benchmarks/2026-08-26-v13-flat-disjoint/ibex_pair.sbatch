#!/usr/bin/env bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --time=00:10:00
#SBATCH --array=0-1
#SBATCH --output=/ibex/scratch/hohndor/km/v13-flat-disjoint-20260826/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v13-flat-disjoint-20260826
baseline=/ibex/scratch/hohndor/km/v12-combined-candidate-20260826/km-candidate
candidate=$root/km
baseline_sha=6313469c48e07ff7003eeb635fc6c6b3b9055dea12000f85a96deddbf563c55e
candidate_sha=86815df10d1cd90528fb7316005207e285fee7b02abbcb7ba9e68a4225060559
onts=(6212 4205)
ont=${onts[$SLURM_ARRAY_TASK_ID]}
input=/ibex/scratch/hohndor/km/corpus/ore_ont_${ont}.owl
work=$root/work-${SLURM_ARRAY_JOB_ID}-${SLURM_ARRAY_TASK_ID}
mkdir -p "$root/results" "$work"
trap 'rm -rf "$work"' EXIT
[[ $(sha256sum "$baseline" | awk '{print $1}') == "$baseline_sha" ]]
[[ $(sha256sum "$candidate" | awk '{print $1}') == "$candidate_sha" ]]
[[ -s "$input" ]]
grep -q 'Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz' /proc/cpuinfo

for repetition in 1 2 3; do
  if (( repetition % 2 == 1 )); then order=(baseline candidate); else order=(candidate baseline); fi
  for arm in "${order[@]}"; do
    if [[ $arm == baseline ]]; then binary=$baseline; else binary=$candidate; fi
    stem="ore_${ont}-r${repetition}-${arm}"
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
    python3 - "$work/${stem}.json" <<'PY'
import json, pathlib, sys
value = json.loads(pathlib.Path(sys.argv[1]).read_text())
assert isinstance(value, dict) and value
PY
    printf 'RESULT\tontology=%s\trepetition=%s\tarm=%s\twall_s=%s\trss_kib=%s\n' \
      "$ont" "$repetition" "$arm" "$wall" "$rss_kib"
  done
  cmp "$work/ore_${ont}-r${repetition}-baseline.json" "$work/ore_${ont}-r${repetition}-candidate.json"
done
