#!/bin/bash
#SBATCH --job-name=km-flat-rbox-functional
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --array=0-3%2
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-direct-flat-rbox-20260825/functional-%A_%a.out

set -euo pipefail
ids=(868 15059 14459 16008)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/v110-direct-flat-rbox-20260825
harness=/ibex/scratch/hohndor/km/v110-baseline-20260825/full-sweep
ont=ore_ont_${id}.owl
mkdir -p "$root/functional/results" "$root/functional/failures"
out="$root/functional/results/${id}.json"
/usr/bin/python3 "$harness/full_panel_run_one.py" \
  --kind km --arm flat_rbox_functional \
  --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
  --binary "$root/km" --workers 4 --timeout 240 --memcap-mb 20480 \
  --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
  --gold-kind konclude --workdir "${SLURM_TMPDIR:-/tmp}/km-flat-rbox-${SLURM_JOB_ID}-${id}" \
  --failures-dir "$root/functional/failures" \
  --checkpoint "$root/functional/results/${id}.checkpoint.json" \
  --capture-km-route --env KM_ROUTE=auto > "$out.tmp"
/usr/bin/python3 - "$out.tmp" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["checkpointed"] and r["status"] == "ok" and r["verdict"] == "match", r
assert r["selected_route_trace"] == "elc", r
print(json.dumps({k:r[k] for k in ["binary_sha256","wall_s","peak_mb","signature_sha256","selected_route_trace"]},sort_keys=True))
PY
mv "$out.tmp" "$out"
echo FUNCTIONAL_COMPLETE ontology="$id"
