#!/bin/bash
#SBATCH --job-name=km-ceb6f16-elccert
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=2
#SBATCH --mem=20G
#SBATCH --time=00:08:00
#SBATCH --array=0-3%1
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/stale-repair-ceb6f16/focus-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/routing_20260715/stale-repair-ceb6f16
km_root=/ibex/scratch/hohndor/km
runner=/ibex/scratch/hohndor/km/routing_20260715/rule-clash-4703045/full_panel_run_one.py
onts=(ore_ont_1034.owl ore_ont_2237.owl ore_ont_6999.owl ore_ont_1194.owl)
ont=${onts[${SLURM_ARRAY_TASK_ID:?}]}
work=${SLURM_TMPDIR:-/tmp}/km-ceb6f16-elccert-${SLURM_JOB_ID}
mkdir -p "$work" "$root/focus-results" "$root/focus-failures"

PYTHONPATH=/ibex/scratch/hohndor/km/routing_20260715/rule-clash-4703045 \
/usr/bin/python3 "$runner" \
  --kind km \
  --arm km_route_elc_cert_ceb6f16 \
  --ontology "$km_root/corpus/$ont" \
  --binary "$root/km" \
  --workers 2 \
  --timeout 240 \
  --memcap-mb 18432 \
  --gold "$km_root/cmp2/out/konclude/konclude__$ont.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$root/focus-failures" \
  --checkpoint "$root/focus-results/$ont.checkpoint.json" \
  --capture-km-route \
  --env KM_ROUTE=elc_cert \
  > "$root/focus-results/$ont.json.tmp"

/usr/bin/python3 - "$root/focus-results/$ont.json.tmp" "$ont" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[2]:
    raise SystemExit(f"ontology mismatch: {row}")
if not row.get("checkpointed"):
    raise SystemExit(f"missing terminal checkpoint: {row}")
if row.get("status") not in {"ok", "timeout", "memout", "error", "unsupported"}:
    raise SystemExit(f"invalid status: {row}")
if sys.argv[2] != "ore_ont_1194.owl" and (
    row.get("status") != "ok" or row.get("verdict") != "match"
):
    raise SystemExit(f"exactness control failed: {row}")
print(json.dumps(row, sort_keys=True))
PY
mv "$root/focus-results/$ont.json.tmp" "$root/focus-results/$ont.json"
