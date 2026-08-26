#!/bin/bash
#SBATCH --job-name=km-abox-functional
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --array=0-9
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-abox-elision-v7-20260825/functional/slurm-%A_%a.out

set -euo pipefail
ids=(1012 1306 3164 3658 4187 9958 10750 13482 15280 15725)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/v110-abox-elision-v7-20260825
candidate="$root/km"
candidate_sha=$(cut -d' ' -f1 < "$root/km.sha256")
harness=/ibex/scratch/hohndor/km/v110-baseline-20260825/full-sweep
ont=ore_ont_${id}.owl

[[ $(sha256sum "$candidate" | cut -d' ' -f1) == "$candidate_sha" ]]
mkdir -p "$root/functional/results" "$root/functional/failures"
work=${SLURM_TMPDIR:-/tmp}/km-abox-functional-${SLURM_JOB_ID}-${id}
for label in baseline candidate; do
  out="$root/functional/results/${id}-${label}.json"
  env_args=(--env KM_ROUTE=auto)
  if [[ $label == baseline ]]; then
    env_args+=(--env KM_NO_SEPARABLE_ABOX_ELISION=1)
  fi
  /usr/bin/python3 "$harness/full_panel_run_one.py" \
    --kind km --arm "abox_functional_${label}" \
    --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
    --binary "$candidate" --workers 4 --timeout 240 --memcap-mb 20480 \
    --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
    --gold-kind konclude --workdir "$work/$label" \
    --failures-dir "$root/functional/failures" \
    --checkpoint "$root/functional/results/${id}-${label}.checkpoint.json" \
    --capture-km-route "${env_args[@]}" > "$out.tmp"
  /usr/bin/python3 - "$out.tmp" "$candidate_sha" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2], r
assert r["checkpointed"] and r["status"] == "ok" and r["verdict"] == "match", r
PY
  mv "$out.tmp" "$out"
done

/usr/bin/python3 - "$root/functional/results" "$id" <<'PY'
import json,sys
root,id=sys.argv[1:]
b=json.load(open(f"{root}/{id}-baseline.json"))
c=json.load(open(f"{root}/{id}-candidate.json"))
assert b["signature_sha256"] == c["signature_sha256"]
print(json.dumps({
  "ontology":int(id),
  "baseline_wall_s":b["wall_s"], "candidate_wall_s":c["wall_s"],
  "baseline_peak_mb":b["peak_mb"], "candidate_peak_mb":c["peak_mb"],
  "baseline_route":b["selected_route_trace"],
  "candidate_route":c["selected_route_trace"],
  "signature_sha256":c["signature_sha256"],
},sort_keys=True))
PY
echo FUNCTIONAL_GATE_COMPLETE ontology="$id"
