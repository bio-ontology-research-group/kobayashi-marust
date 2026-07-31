#!/bin/bash
# Automatic-route closure/performance gate for query-equivalence collapse.
#SBATCH --job-name=km-query-eq-gate
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-4
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/query-equivalence-20260731/gate/slurm-%A_%a.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/query-equivalence-20260731
km_root=/ibex/scratch/hohndor/km
ontologies=(
  ore_ont_1194.owl
  ore_ont_15846.owl
  ore_ont_6999.owl
  ore_ont_1034.owl
  ore_ont_2237.owl
)
ontology=${ontologies[${SLURM_ARRAY_TASK_ID:?}]}
work=${SLURM_TMPDIR:-/tmp}/km-query-eq-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work" "$root/gate/results" "$root/gate/failures"

PYTHONPATH="$root" /usr/bin/python3 -c \
  'import ore_canon, tree_watchdog; print("HARNESS_IMPORTS_OK")'

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm km_query_equivalence \
  --ontology "$km_root/corpus/$ontology" \
  --binary "$root/km" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$root/gate/failures" \
  --checkpoint "$root/gate/results/$ontology.checkpoint.json" \
  --env KM_ROUTE=auto \
  --env KM_PROF=1 \
  >"$root/gate/results/$ontology.json.tmp"

/usr/bin/python3 - "$root/gate/results/$ontology.json.tmp" "$ontology" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[2] or not row.get("checkpointed"):
    raise SystemExit(f"invalid terminal row: {row}")
if sys.argv[2] == "ore_ont_1194.owl":
    if row.get("status") == "ok" and not row.get("signature_sha256"):
        raise SystemExit(f"1194 completed without a signature: {row}")
elif row.get("status") != "ok" or row.get("verdict") != "match":
    raise SystemExit(f"exact control failed: {row}")
PY

/usr/bin/mv "$root/gate/results/$ontology.json.tmp" \
  "$root/gate/results/$ontology.json"
echo "TASK_COMPLETE ontology=$ontology"
