#!/bin/bash
#SBATCH --job-name=km-flat-disjoint-868
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:06:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-direct-flat-disjoint-20260825/functional-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v110-direct-flat-disjoint-20260825
harness=/ibex/scratch/hohndor/km/v110-baseline-20260825/full-sweep
ont=ore_ont_868.owl
mkdir -p "$root/functional/failures"
/usr/bin/python3 "$harness/full_panel_run_one.py" \
  --kind km --arm flat_disjoint_868 \
  --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
  --binary "$root/km" --workers 4 --timeout 240 --memcap-mb 20480 \
  --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
  --gold-kind konclude --workdir "${SLURM_TMPDIR:-/tmp}/km-flat-disjoint-${SLURM_JOB_ID}" \
  --failures-dir "$root/functional/failures" \
  --checkpoint "$root/functional/checkpoint.json" \
  --capture-km-route --env KM_ROUTE=auto > "$root/functional/result.json.tmp"
/usr/bin/python3 - "$root/functional/result.json.tmp" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["checkpointed"] and r["status"] == "ok" and r["verdict"] == "match", r
assert r["selected_route_trace"] == "flat_nf1", r
print(json.dumps({k:r[k] for k in ["binary_sha256","wall_s","peak_mb","signature_sha256","selected_route_trace"]},sort_keys=True))
PY
mv "$root/functional/result.json.tmp" "$root/functional/result.json"
echo FUNCTIONAL_COMPLETE
