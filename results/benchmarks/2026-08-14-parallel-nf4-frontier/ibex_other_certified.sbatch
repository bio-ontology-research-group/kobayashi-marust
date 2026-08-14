#!/bin/bash
#SBATCH --job-name=km-par-nf4-other
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-2
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/parallel-nf4-frontier-20260814/other-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/parallel-nf4-frontier-20260814
baseline=/ibex/scratch/hohndor/km/certified-el-typed-handoff-20260814/km
candidate=$root/km
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
ids=(6682 15803 7246)
id=${ids[${SLURM_ARRAY_TASK_ID:?}]}
mkdir -p "$root/other-results" "$root/other-failures"
work=${SLURM_TMPDIR:-/tmp}/km-par-nf4-other-${SLURM_JOB_ID}
for label in baseline candidate; do
  binary=$baseline; envs=(--env KM_ROUTE=auto)
  if [[ $label == candidate ]]; then
    binary=$candidate; envs=(--env KM_ROUTE=auto --env KM_ELC_PAR_NF4=1)
  fi
  ont=ore_ont_${id}.owl
  /usr/bin/python3 "$harness/full_panel_run_one.py" \
    --kind km --arm "${id}_${label}" \
    --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
    --binary "$binary" --workers 16 --timeout 240 --memcap-mb 20480 \
    --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
    --gold-kind konclude --workdir "$work/$label" \
    --failures-dir "$root/other-failures" --capture-km-route "${envs[@]}" \
    > "$root/other-results/${id}-${label}.json.tmp"
  mv "$root/other-results/${id}-${label}.json.tmp" "$root/other-results/${id}-${label}.json"
done
python3 - "$root/other-results" "$id" <<'PY'
import json,sys
root,id=sys.argv[1:]
b=json.load(open(f"{root}/{id}-baseline.json")); c=json.load(open(f"{root}/{id}-candidate.json"))
assert b["status"]==c["status"]=="ok" and b["signature_sha256"]==c["signature_sha256"]
print(id,"wall",b["wall_s"],c["wall_s"],"peak",b["peak_mb"],c["peak_mb"])
PY
