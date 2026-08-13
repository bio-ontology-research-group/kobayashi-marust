#!/bin/bash
#SBATCH --job-name=km-positive-el-reuse
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-7
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v0215-next-profile/panel-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v0215-next-profile
baseline=/ibex/scratch/hohndor/km/large-inproc-elc-candidate-20260813/km
candidate=$root/km-candidate-ibex
baseline_sha=2b811f8586ee6e6775db5b6ed76f7d98eefd51519f21a9ca6ead06f0514eec99
candidate_sha=16a0d2cea74e29267ec2a37d1c8da48ac6ac29cc2ba2799eaae08e8a070f26a7
[[ $(sha256sum "$baseline" | cut -d' ' -f1) == "$baseline_sha" ]]
[[ $(sha256sum "$candidate" | cut -d' ' -f1) == "$candidate_sha" ]]
onts=(13482 15280 10750 1012 6233 1306 3377 5519)
ont=ore_ont_${onts[${SLURM_ARRAY_TASK_ID:?}]}.owl
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
work=${SLURM_TMPDIR:-/tmp}/km-positive-el-reuse-${SLURM_JOB_ID}
mkdir -p "$work" "$root/results" "$root/failures"
for label in baseline candidate; do
  binary=$baseline
  expected=$baseline_sha
  if [[ $label == candidate ]]; then binary=$candidate; expected=$candidate_sha; fi
  out="$root/results/${label}__$ont.json"
  /usr/bin/python3 "$harness/full_panel_run_one.py" \
    --kind km --arm "positive_el_reuse_${label}" \
    --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
    --binary "$binary" --workers 16 --timeout 240 --memcap-mb 20480 \
    --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
    --gold-kind konclude --workdir "$work/$label" --failures-dir "$root/failures" \
    --checkpoint "$root/results/${label}__$ont.checkpoint.json" \
    --capture-km-route --env KM_ROUTE=auto > "$out.tmp"
  /usr/bin/python3 - "$out.tmp" "$expected" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2], r
assert r["checkpointed"] and r["status"] == "ok" and r["verdict"] == "match", r
assert r["selected_route_trace"] == "elc", r
PY
  mv "$out.tmp" "$out"
done
echo "PANEL_COMPLETE ontology=$ont"
