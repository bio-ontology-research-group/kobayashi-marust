#!/usr/bin/env bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --time=00:10:00
#SBATCH --array=0-1
#SBATCH --output=/ibex/scratch/hohndor/km/v12-route-recovery-20260826/slurm-%A_%a.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/v12-route-recovery-20260826
binary=/ibex/scratch/hohndor/km/v1-cert-overhead-v11-20260826/km
corpus=/ibex/scratch/hohndor/km/corpus
expected_binary_sha=decd89c157e8bcd9f8182589f0db03f606b8fc09fd6ce169525887a53533102c
onts=(8480 6682)
routes=(production_all elc_cert)
ont=${onts[$SLURM_ARRAY_TASK_ID]}
candidate_route=${routes[$SLURM_ARRAY_TASK_ID]}
input=$corpus/ore_ont_${ont}.owl
work=$root/work-${SLURM_ARRAY_JOB_ID}-${SLURM_ARRAY_TASK_ID}

mkdir -p "$root/results" "$work"
trap 'rm -rf "$work"' EXIT
[[ $(sha256sum "$binary" | awk '{print $1}') == "$expected_binary_sha" ]]
grep -q 'Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz' /proc/cpuinfo

for repetition in 1 2 3; do
  if (( repetition % 2 == 1 )); then order=(auto candidate); else order=(candidate auto); fi
  for arm in "${order[@]}"; do
    if [[ $arm == auto ]]; then route=auto; else route=$candidate_route; fi
    stem="ore_${ont}-r${repetition}-${arm}"
    timeout -k 5 240 /usr/bin/time -f '%e\t%M\t%x' \
      -o "$work/${stem}.measure" \
      env KM_ROUTE="$route" KM_TIMING=1 "$binary" classify "$input" \
      > "$work/${stem}.json" 2> "$work/${stem}.stderr"
    read -r wall rss_kib rc < "$work/${stem}.measure"
    [[ $rc == 0 ]]
    install -m 644 "$work/${stem}.measure" "$root/results/${stem}.measure"
    install -m 644 "$work/${stem}.stderr" "$root/results/${stem}.stderr"
    install -m 644 "$work/${stem}.json" "$root/results/${stem}.json"
    printf 'RESULT\tontology=%s\trepetition=%s\tarm=%s\troute=%s\twall_s=%s\trss_kib=%s\n' \
      "$ont" "$repetition" "$arm" "$route" "$wall" "$rss_kib"
  done
  cmp "$work/ore_${ont}-r${repetition}-auto.json" \
      "$work/ore_${ont}-r${repetition}-candidate.json"
done

python3 - "$root/results" "$ont" <<'PY'
from pathlib import Path
import statistics
import sys

root, ont = Path(sys.argv[1]), sys.argv[2]
for arm in ("auto", "candidate"):
    walls = []
    rss = []
    for path in sorted(root.glob(f"ore_{ont}-r*-{arm}.measure")):
        wall, rss_kib, rc = path.read_text().split()
        assert rc == "0"
        walls.append(float(wall))
        rss.append(int(rss_kib) / 1024)
    assert len(walls) == 3
    print(
        f"SUMMARY ontology={ont} arm={arm} "
        f"median_wall_s={statistics.median(walls):.4f} "
        f"median_peak_mib={statistics.median(rss):.2f} samples={walls}"
    )
PY
