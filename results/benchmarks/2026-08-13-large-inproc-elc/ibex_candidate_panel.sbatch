#!/bin/bash
#SBATCH --job-name=km-inproc-elc-panel
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-11
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/large-inproc-elc-candidate-20260813/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/large-inproc-elc-candidate-20260813
baseline=/ibex/scratch/hohndor/km/14817-thread-candidate-20260813/km
candidate=$root/km
baseline_sha=c2947579daf2fff7fb723eb5e8f7d27bc021e0ee6e80878445d727c1b7eaaac2
candidate_sha=$(cut -d' ' -f1 < "$root/km.sha256")
[[ $(sha256sum "$baseline" | cut -d' ' -f1) == "$baseline_sha" ]]
[[ $(sha256sum "$candidate" | cut -d' ' -f1) == "$candidate_sha" ]]
onts=(1559 1012 10750 13482 15280 15059 9674 8486 14042 11395 6233 16008)
ont=ore_ont_${onts[${SLURM_ARRAY_TASK_ID:?}]}.owl
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
work=${SLURM_TMPDIR:-/tmp}/km-inproc-elc-panel-${SLURM_JOB_ID}
mkdir -p "$work" "$root/results" "$root/failures"
for label in baseline candidate; do
  binary=$baseline
  expected=$baseline_sha
  if [[ $label == candidate ]]; then binary=$candidate; expected=$candidate_sha; fi
  out="$root/results/${label}__$ont.json"
  /usr/bin/python3 "$harness/full_panel_run_one.py" \
    --kind km --arm "inproc_elc_${label}" \
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
