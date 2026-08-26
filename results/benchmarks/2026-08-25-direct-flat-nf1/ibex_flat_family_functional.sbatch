#!/bin/bash
#SBATCH --job-name=km-flat-family-functional
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --array=0-4%2
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-direct-flat-source-20260825/family-%A_%a.out

set -euo pipefail
ids=(868 9674 15059 14459 16008)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/v110-direct-flat-source-20260825
harness=/ibex/scratch/hohndor/km/v110-baseline-20260825/full-sweep
ont=ore_ont_${id}.owl
mkdir -p "$root/family/results" "$root/family/failures"
out="$root/family/results/${id}.json"
/usr/bin/python3 "$harness/full_panel_run_one.py" \
  --kind km --arm flat_family_functional \
  --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
  --binary "$root/km" --workers 4 --timeout 240 --memcap-mb 20480 \
  --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
  --gold-kind konclude --workdir "${SLURM_TMPDIR:-/tmp}/km-flat-family-${SLURM_JOB_ID}-${id}" \
  --failures-dir "$root/family/failures" \
  --checkpoint "$root/family/results/${id}.checkpoint.json" \
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
