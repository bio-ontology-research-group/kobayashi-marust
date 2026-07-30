#!/bin/bash
# Isolate the suspected general-bottom-prepass blow-up on 3524.
#SBATCH --job-name=km-v7-3524-no-bottom
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=32G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v7-20260731/diagnostic-3524-no-bottom/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v7-20260731
km_root=/ibex/scratch/hohndor/km
probe=$root/diagnostic-3524-no-bottom
work=${SLURM_TMPDIR:-/tmp}/km-v7-3524-no-bottom-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work" "$probe/results" "$probe/failures"

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm km_route_elc_v7_no_bottom_prepass \
  --ontology "$km_root/corpus/ore_ont_3524.owl" \
  --binary "$root/km" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__ore_ont_3524.owl.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$probe/failures" \
  --checkpoint "$probe/results/elc.checkpoint.json" \
  --env KM_ROUTE=elc \
  --env KM_NO_BOTTOM_PREPASS=1 \
  > "$probe/results/elc.json.tmp"

/usr/bin/python3 - "$probe/results/elc.json.tmp" <<'PY'
import json

row = json.load(open("/ibex/scratch/hohndor/km/adaptive-composite-layout-v7-20260731/diagnostic-3524-no-bottom/results/elc.json.tmp"))
if row.get("ont") != "ore_ont_3524.owl" or not row.get("checkpointed"):
    raise SystemExit(f"invalid terminal row: {row}")
if row.get("status") != "ok" or row.get("verdict") != "match":
    raise SystemExit(f"no-bottom ELC failed exactness diagnostic: {row}")
PY
/usr/bin/mv "$probe/results/elc.json.tmp" "$probe/results/elc.json"
echo "TASK_COMPLETE route=elc no_bottom_prepass=1"
