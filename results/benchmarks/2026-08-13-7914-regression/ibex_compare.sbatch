#!/bin/bash
#SBATCH --job-name=km-7914-reg-compare
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-2%3
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/7914-regression-20260813/compare-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/7914-regression-20260813
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
revs=(a639ab5 cff26d2-parent cff26d2)
rev=${revs[${SLURM_ARRAY_TASK_ID:?}]}
bin="$root/bin/km-$rev"
expected=$(cut -d' ' -f1 "$bin.sha256")
[[ $(sha256sum "$bin" | cut -d' ' -f1) == "$expected" ]]
mkdir -p "$root/results" "$root/failures"
work=${SLURM_TMPDIR:-/tmp}/km-7914-reg-${SLURM_JOB_ID}-${SLURM_ARRAY_TASK_ID}
PYTHONPATH="$harness" /usr/bin/python3 -c 'import full_panel_run_one, ore_canon, tree_watchdog'
for route in production_all ht_bridge; do
  out="$root/results/${rev}__${route}.json"
  /usr/bin/python3 "$harness/full_panel_run_one.py" \
    --kind km --arm "7914_${rev}_${route}" \
    --ontology /ibex/scratch/hohndor/km/corpus/ore_ont_7914.owl \
    --binary "$bin" --workers 16 --timeout 240 --memcap-mb 20480 \
    --gold /ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__ore_ont_7914.owl.sig.gz \
    --gold-kind konclude --workdir "$work/$route" --failures-dir "$root/failures" \
    --checkpoint "$root/results/${rev}__${route}.checkpoint.json" \
    --capture-km-route --env "KM_ROUTE=$route" > "$out.tmp"
  /usr/bin/python3 - "$out.tmp" "$route" "$expected" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[3]
assert r["checkpointed"]
assert r["selected_route_trace"] == sys.argv[2]
assert r["status"] == "ok" and r["verdict"] == "match", r
PY
  mv "$out.tmp" "$out"
done
/usr/bin/python3 - "$root/results/${rev}__production_all.json" "$root/results/${rev}__ht_bridge.json" <<'PY'
import json,sys
rows=[json.load(open(p)) for p in sys.argv[1:]]
assert len({r["signature_sha256"] for r in rows}) == 1
print([(r["selected_route_trace"],r["wall_s"],r["peak_mb"]) for r in rows])
PY
echo COMPARE_COMPLETE revision=$rev
