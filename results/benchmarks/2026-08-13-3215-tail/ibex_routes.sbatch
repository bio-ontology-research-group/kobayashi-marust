#!/bin/bash
#SBATCH --job-name=km-3215-routes
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/candidate-78d5674-atomic-abox-20260813/3215-routes-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/candidate-78d5674-atomic-abox-20260813
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
expected=$(cut -d' ' -f1 "$root/km.sha256")
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$expected" ]]
mkdir -p "$root/3215-routes" "$root/3215-failures"
for route in elc_cert ht_bridge ht_full; do
  work=${SLURM_TMPDIR:-/tmp}/km-3215-$route-$SLURM_JOB_ID
  /usr/bin/python3 "$harness/full_panel_run_one.py" \
    --kind km --arm "3215_$route" \
    --ontology /ibex/scratch/hohndor/km/corpus/ore_ont_3215.owl \
    --binary "$root/km" --workers 16 --timeout 240 --memcap-mb 20480 \
    --gold /ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__ore_ont_3215.owl.sig.gz \
    --gold-kind konclude --workdir "$work" --failures-dir "$root/3215-failures" \
    --checkpoint "$root/3215-routes/$route.checkpoint.json" --capture-km-route \
    --env "KM_ROUTE=$route" > "$root/3215-routes/$route.json.tmp"
  /usr/bin/python3 - "$root/3215-routes/$route.json.tmp" "$expected" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2] and r["checkpointed"], r
assert r["status"] in {"ok","timeout","memout","error","unsupported"}, r
PY
  mv "$root/3215-routes/$route.json.tmp" "$root/3215-routes/$route.json"
done
echo ROUTES_COMPLETE
