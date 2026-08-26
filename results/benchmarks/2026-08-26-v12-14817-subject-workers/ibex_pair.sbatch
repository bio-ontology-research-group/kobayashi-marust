#!/usr/bin/env bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --time=00:15:00
#SBATCH --output=/ibex/scratch/hohndor/km/v12-14817-subject-workers-20260826/slurm-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/v12-14817-subject-workers-20260826
binary=/ibex/scratch/hohndor/km/v1-cert-overhead-v11-20260826/km
input=/ibex/scratch/hohndor/km/corpus/ore_ont_14817.owl
expected_binary_sha=decd89c157e8bcd9f8182589f0db03f606b8fc09fd6ce169525887a53533102c
work=$root/work-${SLURM_JOB_ID}

mkdir -p "$root/results" "$work"
trap 'rm -rf "$work"' EXIT
[[ $(sha256sum "$binary" | awk '{print $1}') == "$expected_binary_sha" ]]
grep -q 'Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz' /proc/cpuinfo

for repetition in 1 2 3; do
  if (( repetition % 2 == 1 )); then order=(4 8); else order=(8 4); fi
  for workers in "${order[@]}"; do
    stem="r${repetition}-w${workers}"
    timeout -k 5 240 /usr/bin/time -f '%e\t%M\t%x' \
      -o "$work/${stem}.measure" \
      env KM_ROUTE=auto KM_TIMING=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE="$workers" \
      "$binary" classify "$input" \
      > "$work/${stem}.json" 2> "$work/${stem}.stderr"
    read -r wall rss_kib rc < "$work/${stem}.measure"
    [[ $rc == 0 ]]
    grep -q 'route=production_all' "$work/${stem}.stderr"
    install -m 644 "$work/${stem}.measure" "$root/results/${stem}.measure"
    install -m 644 "$work/${stem}.stderr" "$root/results/${stem}.stderr"
    install -m 644 "$work/${stem}.json" "$root/results/${stem}.json"
    printf 'RESULT\trepetition=%s\tworkers=%s\twall_s=%s\trss_kib=%s\trc=%s\n' \
      "$repetition" "$workers" "$wall" "$rss_kib" "$rc"
  done
  cmp "$work/r${repetition}-w4.json" "$work/r${repetition}-w8.json"
done

python3 - "$root/results" <<'PY'
from pathlib import Path
import statistics
import sys

root = Path(sys.argv[1])
for workers in (4, 8):
    walls = []
    rss = []
    for path in sorted(root.glob(f"r*-w{workers}.measure")):
        wall, rss_kib, rc = path.read_text().split()
        assert rc == "0"
        walls.append(float(wall))
        rss.append(int(rss_kib) / 1024)
    assert len(walls) == 3
    print(
        f"SUMMARY workers={workers} median_wall_s={statistics.median(walls):.4f} "
        f"median_peak_mib={statistics.median(rss):.2f} samples={walls}"
    )
PY
