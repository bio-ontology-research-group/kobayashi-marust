#!/bin/bash
#SBATCH --job-name=km-nominal-global-diag
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --array=0-8
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-nominal-global-diagnostic-20260825/slurm-%A_%a.out

set -euo pipefail
ids=(148 1790 3050 6765 7474 8322 8480 8999 16462)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/v110-nominal-global-diagnostic-20260825
binary=/ibex/scratch/hohndor/km/v110-abox-elision-v7-20260825/km
harness=/ibex/scratch/hohndor/km/v110-baseline-20260825/full-sweep
ont=ore_ont_${id}.owl
mkdir -p "$root/results" "$root/failures"
work=${SLURM_TMPDIR:-/tmp}/km-nominal-global-${SLURM_JOB_ID}-${id}
out="$root/results/${id}.json"
/usr/bin/python3 "$harness/full_panel_run_one.py" \
  --kind km --arm nominal_global_diagnostic \
  --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
  --binary "$binary" --workers 4 --timeout 240 --memcap-mb 20480 \
  --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
  --gold-kind konclude --workdir "$work" \
  --failures-dir "$root/failures" \
  --checkpoint "$root/results/${id}.checkpoint.json" \
  --capture-km-route --env KM_ROUTE=ht_general --env KM_HT_GLOBAL=1 \
  --env KM_ENGINE_BIN=/bin/false > "$out.tmp"
mv "$out.tmp" "$out"
/usr/bin/python3 - "$out" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
print(json.dumps({k:r.get(k) for k in ["ont","status","verdict","wall_s","peak_mb","selected_route_trace","subsumptions","unsatisfiable","consistent"]},sort_keys=True))
PY
echo NOMINAL_GLOBAL_DIAGNOSTIC_COMPLETE ontology="$id"
