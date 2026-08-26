#!/usr/bin/env bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --time=00:08:00
#SBATCH --array=0-9
#SBATCH --output=/ibex/scratch/hohndor/km/v15-combined-screen-20260826/screen-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v15-combined-screen-20260826
baseline=/ibex/scratch/hohndor/km/v13-flat-disjoint-20260826/km
candidate=$root/km
baseline_sha=86815df10d1cd90528fb7316005207e285fee7b02abbcb7ba9e68a4225060559
candidate_sha=bd36a49c9f47dd6a593d62b3b4183c1c1d5ae3d2fee19b50a8b43c9b1884fd34
onts=(3377 15803 6682 7246 11745 14817 10621 9663 11460 4604)
ont=${onts[$SLURM_ARRAY_TASK_ID]}
input=/ibex/scratch/hohndor/km/corpus/ore_ont_${ont}.owl
work=${SLURM_TMPDIR:-/tmp}/km-v15-screen-${SLURM_JOB_ID}-${SLURM_ARRAY_TASK_ID}
mkdir -p "$root/results" "$work"
trap 'rm -rf "$work"' EXIT
[[ $(sha256sum "$baseline" | awk '{print $1}') == "$baseline_sha" ]]
[[ $(sha256sum "$candidate" | awk '{print $1}') == "$candidate_sha" ]]
[[ -s "$input" ]]
grep -q 'Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz' /proc/cpuinfo

for arm in baseline candidate; do
  if [[ $arm == baseline ]]; then binary=$baseline; else binary=$candidate; fi
  stem="ore_${ont}-${arm}"
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
  printf 'RESULT\tontology=%s\tarm=%s\twall_s=%s\trss_kib=%s\n' \
    "$ont" "$arm" "$wall" "$rss_kib"
done
cmp "$work/ore_${ont}-baseline.json" "$work/ore_${ont}-candidate.json"
