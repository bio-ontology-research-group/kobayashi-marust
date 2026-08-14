#!/bin/bash
#SBATCH --job-name=km-nf4-8737-rep
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --time=00:06:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-2
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/parallel-nf4-frontier-20260814/repeat-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/parallel-nf4-frontier-20260814
baseline=/ibex/scratch/hohndor/km/certified-el-typed-handoff-20260814/km
candidate=$root/km
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
rep=${SLURM_ARRAY_TASK_ID:?}
mkdir -p "$root/repeat-results" "$root/repeat-failures"
work=${SLURM_TMPDIR:-/tmp}/km-nf4-8737-repeat-${SLURM_JOB_ID}
if (( rep % 2 == 0 )); then labels=(baseline candidate); else labels=(candidate baseline); fi
for label in "${labels[@]}"; do
  binary=$baseline
  [[ $label == candidate ]] && binary=$candidate
  /usr/bin/python3 "$harness/full_panel_run_one.py" \
    --kind km --arm "8737_${label}_repeat_${rep}" \
    --ontology /ibex/scratch/hohndor/km/corpus/ore_ont_8737.owl \
    --binary "$binary" --workers 16 --timeout 240 --memcap-mb 20480 \
    --gold /ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__ore_ont_8737.owl.sig.gz \
    --gold-kind konclude --workdir "$work/$label" \
    --failures-dir "$root/repeat-failures" --capture-km-route \
    --env KM_ROUTE=auto \
    > "$root/repeat-results/${rep}-${label}.json.tmp"
  mv "$root/repeat-results/${rep}-${label}.json.tmp" "$root/repeat-results/${rep}-${label}.json"
done
/usr/bin/python3 - "$root/repeat-results" "$rep" <<'PY'
import json,sys
root,rep=sys.argv[1:]
b=json.load(open(f"{root}/{rep}-baseline.json")); c=json.load(open(f"{root}/{rep}-candidate.json"))
assert b["status"]==c["status"]=="ok" and b["signature_sha256"]==c["signature_sha256"]
print(rep,"wall",b["wall_s"],c["wall_s"],"peak",b["peak_mb"],c["peak_mb"])
PY
