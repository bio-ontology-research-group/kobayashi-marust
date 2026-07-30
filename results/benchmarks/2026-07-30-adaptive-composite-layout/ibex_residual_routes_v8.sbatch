#!/bin/bash
# Current-v8 exact-route search for the first newly verified residuals.
#SBATCH --job-name=km-v8-residual-routes
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-16%10
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v8-20260731/residual-routes/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v8-20260731
km_root=/ibex/scratch/hohndor/km
cases=(
  "4669 production_all8"
  "4669 production_all1"
  "4669 cb_absorb16"
  "4669 elc_cert"
  "6934 ht_features"
  "6934 ht_full"
  "6934 certified_nominals"
  "6934 production_all"
  "7499 certified_card_nominals"
  "7499 certified_card_proxy_abox"
  "7499 ht_card"
  "7499 production_all"
  "9654 production_all"
  "9654 certified_nominals"
  "9724 production_all8"
  "9724 production_all1"
  "9724 cb_plain1"
)
read -r number route <<< "${cases[${SLURM_ARRAY_TASK_ID:?}]}"
ontology=ore_ont_${number}.owl
probe=$root/residual-routes
work=${SLURM_TMPDIR:-/tmp}/km-v8-residual-$number-$route-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work" "$probe/results" "$probe/failures"

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm "km_route_${route}_v8" \
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
  --env "KM_ROUTE=$route" \
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
echo "TASK_COMPLETE ontology=$ontology route=$route"
