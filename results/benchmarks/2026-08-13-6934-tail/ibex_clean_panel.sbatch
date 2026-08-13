#!/bin/bash
#SBATCH --job-name=km-6934-clean-panel
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/6934-clean-snapshot-20260813/panel-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/6934-clean-snapshot-20260813
base=/ibex/scratch/hohndor/km/candidate-78d5674-atomic-abox-20260813
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
mkdir -p "$root/results" "$root/failures"
for arm in baseline candidate; do
  if [[ $arm == baseline ]]; then bin=$base/km; else bin=$root/km; fi
  expected=$(sha256sum "$bin" | cut -d' ' -f1)
  work=${SLURM_TMPDIR:-/tmp}/km-6934-clean-$arm-$SLURM_JOB_ID
  /usr/bin/python3 "$harness/full_panel_run_one.py" \
    --kind km --arm "6934_clean_$arm" \
    --ontology /ibex/scratch/hohndor/km/corpus/ore_ont_6934.owl \
    --binary "$bin" --workers 16 --timeout 240 --memcap-mb 20480 \
    --gold /ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__ore_ont_6934.owl.sig.gz \
    --gold-kind konclude --workdir "$work" --failures-dir "$root/failures" \
    --checkpoint "$root/results/$arm.checkpoint.json" --capture-km-route \
    --env KM_ROUTE=auto > "$root/results/$arm.json.tmp"
  python3 - "$root/results/$arm.json.tmp" "$expected" <<'PY'
import json,sys
r=json.load(open(sys.argv[1])); assert r["binary_sha256"]==sys.argv[2] and r["checkpointed"]
assert r["status"]=="ok" and r["verdict"]=="match",r
PY
  mv "$root/results/$arm.json.tmp" "$root/results/$arm.json"
done
python3 - "$root/results/baseline.json" "$root/results/candidate.json" <<'PY'
import json,sys
a,b=map(lambda p:json.load(open(p)),sys.argv[1:])
assert a["signature_sha256"]==b["signature_sha256"]
print({"baseline_wall":a["wall_s"],"candidate_wall":b["wall_s"],
       "baseline_peak":a["peak_mb"],"candidate_peak":b["peak_mb"]})
PY
echo PANEL_COMPLETE
