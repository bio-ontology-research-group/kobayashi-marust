#!/bin/bash
# Isolated exact control for the near-budget 15846 route. The broad gate ran
# this concurrently with 1194 on an AMD node and enabled profiling, so it did
# not provide an admissible regression comparison.
#SBATCH --job-name=km-query-eq-15846
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/query-equivalence-20260731/control-15846/slurm-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/query-equivalence-20260731
km_root=/ibex/scratch/hohndor/km
ontology=ore_ont_15846.owl
work=${SLURM_TMPDIR:-/tmp}/km-query-eq-15846-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work" "$root/control-15846"

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm km_query_equivalence_15846_control \
  --ontology "$km_root/corpus/$ontology" \
  --binary "$root/km" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$root/control-15846" \
  --checkpoint "$root/control-15846/result.checkpoint.json" \
  --env KM_ROUTE=auto \
  >"$root/control-15846/result.json.tmp"

/usr/bin/python3 - "$root/control-15846/result.json.tmp" <<'PY'
import json
import sys
row = json.load(open(sys.argv[1]))
if row.get("status") != "ok" or row.get("verdict") != "match":
    raise SystemExit(f"15846 isolated exact control failed: {row}")
PY
/usr/bin/mv "$root/control-15846/result.json.tmp" "$root/control-15846/result.json"
