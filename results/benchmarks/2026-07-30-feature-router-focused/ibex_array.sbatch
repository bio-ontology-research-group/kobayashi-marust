#!/bin/bash
# Focused proof run for the source-routed independent large-ABox candidate.
# The complete 592-ontology sweep remains the acceptance gate.
#SBATCH --job-name=km-router-abox3
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --array=0-2
#SBATCH --output=/ibex/scratch/hohndor/km/router-20260730-v2/slurm-%A_%a.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/router-20260730-v2
corpus=/ibex/scratch/hohndor/km/corpus
gold=/ibex/scratch/hohndor/km/cmp2/out/konclude
ontologies=(ore_ont_3560.owl ore_ont_6477.owl ore_ont_7914.owl)
expected_routes=(elc elc ht_bridge)
ontology=${ontologies[${SLURM_ARRAY_TASK_ID:?}]}
expected_route=${expected_routes[${SLURM_ARRAY_TASK_ID:?}]}
work=${SLURM_TMPDIR:-/tmp}/km-router-${SLURM_JOB_ID}
mkdir -p "$work" "$root/results" "$root/profiles"
/usr/bin/cp "$corpus/$ontology" "$work/$ontology"

"$root/km" profile "$work/$ontology" > "$root/profiles/$ontology.json.tmp"
/usr/bin/mv "$root/profiles/$ontology.json.tmp" "$root/profiles/$ontology.json"
/usr/bin/python3 - "$root/profiles/$ontology.json" "$expected_route" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("status") != "ok":
    raise SystemExit(f"profile failed: {row}")
if row.get("selected_route") != sys.argv[2]:
    raise SystemExit(
        f"route mismatch: expected={sys.argv[2]} actual={row.get('selected_route')}"
    )
PY

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm km_route_auto_independent_abox \
  --ontology "$work/$ontology" \
  --binary "$root/km" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$gold/konclude__$ontology.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$root/failures" \
  --checkpoint "$root/results/$ontology.checkpoint.json" \
  --env KM_ROUTE=auto \
  > "$root/results/$ontology.json.tmp"
/usr/bin/mv "$root/results/$ontology.json.tmp" "$root/results/$ontology.json"
