#!/bin/bash
# Recheck documented current mechanisms for residuals first exposed late in
# the v4 sweep, using the accepted v9 binary and frozen Konclude signatures.
#SBATCH --job-name=km-v9-new-residuals
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-3%4
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v9-20260731/new-residuals/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v9-20260731
km_root=/ibex/scratch/hohndor/km
cases=(
  "10702 htforce_race"
  "10908 production_all"
  "12653 production_all"
  "13503 production_all"
)
read -r number route <<< "${cases[${SLURM_ARRAY_TASK_ID:?}]}"
ontology=ore_ont_${number}.owl
probe=$root/new-residuals
work=${SLURM_TMPDIR:-/tmp}/km-v9-residual-$number-$route-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work" "$probe/results" "$probe/failures"

env_args=(--env KM_ROUTE=production_all)
if [[ $route == htforce_race ]]; then
  env_args=(
    --env KM_ROUTE=manual
    --env KM_THREADS=16
    --env KM_PAR_MEM_GB=18
    --env KM_HT_MEM_GB=18
    --env KM_KEEP_CHAIN_AXIOMS=1
    --env KM_ABSORB=1
    --env KM_ABSORB_PORTFOLIO=1
    --env KM_HT_FORCE=1
    --env KM_HT_MODE=race
  )
fi

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm "km_route_${route}_v9" \
  --ontology "$km_root/corpus/$ontology" \
  --binary "$root/km" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$probe/failures/$number/$route" \
  --checkpoint "$probe/results/$number-$route.checkpoint.json" \
  "${env_args[@]}" \
  > "$probe/results/$number-$route.json.tmp"

/usr/bin/python3 - "$probe/results/$number-$route.json.tmp" "$ontology" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[2] or not row.get("checkpointed"):
    raise SystemExit(f"invalid terminal row: {row}")
if row.get("status") not in {"ok", "timeout", "memout", "error", "unsupported"}:
    raise SystemExit(f"invalid terminal status: {row}")
PY
/usr/bin/mv "$probe/results/$number-$route.json.tmp" \
  "$probe/results/$number-$route.json"
