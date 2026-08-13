#!/bin/bash
#SBATCH --job-name=km-14817-thread-panel
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:25:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/14817-thread-panel-20260813/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/14817-thread-panel-20260813
binary=/ibex/scratch/hohndor/km/3215-sequential-bridge-candidate-20260813/km
binary_sha=31ecdbc74174e371f1f55805af8de382f517b0ab1960ed81553f6fa249c4bea5
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
ont=ore_ont_14817.owl
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$binary_sha" ]]
cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]
mkdir -p "$root/results" "$root/failures"
work=${SLURM_TMPDIR:-/tmp}/km-14817-threads-${SLURM_JOB_ID}
for rep in 1 2 3; do
  for route in production_all production_all8; do
    out="$root/results/${route}-${rep}.json"
    /usr/bin/python3 "$harness/full_panel_run_one.py" \
      --kind km --arm "14817_${route}_${rep}" \
      --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
      --binary "$binary" --workers 16 --timeout 240 --memcap-mb 20480 \
      --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
      --gold-kind konclude --workdir "$work/$route-$rep" --failures-dir "$root/failures" \
      --checkpoint "$root/results/${route}-${rep}.checkpoint.json" \
      --capture-km-route --env "KM_ROUTE=$route" > "$out.tmp"
    /usr/bin/python3 - "$out.tmp" "$binary_sha" "$route" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2]
assert r["checkpointed"] and r["status"] == "ok" and r["verdict"] == "match", r
assert r["selected_route_trace"] == sys.argv[3], r
PY
    mv "$out.tmp" "$out"
  done
done
/usr/bin/python3 - "$root/results" <<'PY'
import glob,json,statistics,sys
root=sys.argv[1]
for route in ("production_all","production_all8"):
 rows=[json.load(open(p)) for p in sorted(glob.glob(f"{root}/{route}-[123].json"))]
 print(route,{"wall_mean":statistics.mean(r["wall_s"] for r in rows),
              "peak_mean":statistics.mean(r["peak_mb"] for r in rows)})
PY
echo ROUTE_PANEL_COMPLETE
