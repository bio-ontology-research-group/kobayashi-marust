#!/bin/bash
#SBATCH --job-name=km-iri-bulk-reverse
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:09:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-17%9
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/declaration-seed-20260814/reverse-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/declaration-seed-20260814
baseline=/ibex/scratch/hohndor/km/parallel-nf4-frontier-20260814/km
candidate=$root/km
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
ids=(13482 15280 8486 9674 10689 1012 10750 14459 1559 16008 15059 14042 1306 11395 6233 3377 3524 3836)
id=${ids[${SLURM_ARRAY_TASK_ID:?}]}
mkdir -p "$root/reverse-results" "$root/reverse-failures"
work=${SLURM_TMPDIR:-/tmp}/km-iri-bulk-reverse-${SLURM_JOB_ID}
for label in candidate baseline; do
  binary=$baseline
  [[ $label == candidate ]] && binary=$candidate
  ont=ore_ont_${id}.owl
  /usr/bin/python3 "$harness/full_panel_run_one.py" \
    --kind km --arm "${id}_${label}_iri_bulk_reverse" \
    --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
    --binary "$binary" --workers 16 --timeout 240 --memcap-mb 20480 \
    --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
    --gold-kind konclude --workdir "$work/$label" \
    --failures-dir "$root/reverse-failures" --capture-km-route \
    --env KM_ROUTE=auto \
    > "$root/reverse-results/${id}-${label}.json.tmp"
  mv "$root/reverse-results/${id}-${label}.json.tmp" "$root/reverse-results/${id}-${label}.json"
done
/usr/bin/python3 - "$root/reverse-results" "$id" <<'PY'
import json,sys
root,id=sys.argv[1:]
b=json.load(open(f"{root}/{id}-baseline.json")); c=json.load(open(f"{root}/{id}-candidate.json"))
assert b["status"]==c["status"]=="ok" and b["signature_sha256"]==c["signature_sha256"]
print(id,"wall",b["wall_s"],c["wall_s"],"peak",b["peak_mb"],c["peak_mb"])
PY
