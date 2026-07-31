#!/bin/bash
# Reproduce the documented htforce_race environment with the accepted v9
# binary before expressing it as a feature-certified automatic route.
#SBATCH --job-name=km-v9-6934-htforce
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v9-20260731/6934-historical/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v9-20260731
km_root=/ibex/scratch/hohndor/km
probe=$root/6934-historical
ontology=ore_ont_6934.owl
work=${SLURM_TMPDIR:-/tmp}/km-v9-6934-htforce-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work" "$probe/failures"

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm km_historical_htforce_race_v9 \
  --ontology "$km_root/corpus/$ontology" \
  --binary "$root/km" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$probe/failures" \
  --checkpoint "$probe/result.checkpoint.json" \
  --env KM_ROUTE=manual \
  --env KM_THREADS=16 \
  --env KM_PAR_MEM_GB=18 \
  --env KM_HT_MEM_GB=18 \
  --env KM_KEEP_CHAIN_AXIOMS=1 \
  --env KM_ABSORB=1 \
  --env KM_ABSORB_PORTFOLIO=1 \
  --env KM_HT_FORCE=1 \
  --env KM_HT_MODE=race \
  > "$probe/result.json.tmp"

/usr/bin/python3 - "$probe/result.json.tmp" "$ontology" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[2] or not row.get("checkpointed"):
    raise SystemExit(f"invalid terminal row: {row}")
if row.get("status") not in {"ok", "timeout", "memout", "error", "unsupported"}:
    raise SystemExit(f"invalid terminal status: {row}")
PY
/usr/bin/mv "$probe/result.json.tmp" "$probe/result.json"
