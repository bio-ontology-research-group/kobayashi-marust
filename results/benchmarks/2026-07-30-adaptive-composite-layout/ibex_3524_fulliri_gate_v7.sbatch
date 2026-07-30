#!/bin/bash
# Exact 3524 gate using the collision-safe full-IRI benchmark path.
#SBATCH --job-name=km-v7-3524-fulliri
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v7-20260731/fulliri-3524/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v7-20260731
km_root=/ibex/scratch/hohndor/km
gate=$root/fulliri-3524
work=${SLURM_TMPDIR:-/tmp}/km-v7-3524-fulliri-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$gate/results" "$gate/failures" "$gate/fingerprint" "$work"

PYTHONPATH="$root" /usr/bin/python3 "$root/full_panel_run_one_fulliri_only.py" \
  --kind km \
  --arm km_route_elc_v7_fulliri \
  --ontology "$km_root/corpus/ore_ont_3524.owl" \
  --binary "$root/km" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__ore_ont_3524.owl.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$gate/failures" \
  --checkpoint "$gate/results/runner.checkpoint.json" \
  --retain-output \
  --env KM_ROUTE=elc \
  --env KM_NO_BOTTOM_PREPASS=1 \
  > "$gate/results/runner.json.tmp"

output=$(/usr/bin/python3 - "$gate/results/runner.json.tmp" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("status") != "ok":
    raise SystemExit(f"classification failed: {row}")
if row.get("verdict") != "localname_not_applicable_fulliri_only":
    raise SystemExit(f"collision-unsafe local projection was not deferred: {row}")
if not row.get("output_path"):
    raise SystemExit(f"classification output was not retained: {row}")
print(row["output_path"])
PY
)

/usr/bin/python3 "$root/full_panel_fingerprint.py" \
  --input "$output" \
  --format json \
  --source-ontology "$km_root/corpus/ore_ont_3524.owl" \
  --output-prefix "$gate/fingerprint/km" \
  > "$gate/fingerprint/stdout.json"

/usr/bin/python3 - "$gate/fingerprint/km.json" <<'PY'
import json
import sys

expected = "090129a7fbaa14652ada3408dd1f160e7dd4a09a3502cc3323d8dad734e8893a"
row = json.load(open(sys.argv[1]))
if row.get("status") != "ok" or row.get("taxonomy_sha256") != expected:
    raise SystemExit(f"full-IRI exactness gate failed: {row}")
PY
/usr/bin/mv "$gate/results/runner.json.tmp" "$gate/results/runner.json"
/usr/bin/rm -f "$output"
echo "FULLIRI_GATE_COMPLETE ontology=ore_ont_3524.owl"
