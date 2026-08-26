#!/bin/bash
#SBATCH --job-name=km-bridge-workers
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --array=0-2%1
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-bridge-workers-20260825/functional/slurm-%A_%a.out

set -euo pipefail
ids=(3215 14817 10621)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/v110-bridge-workers-20260825
harness=/ibex/scratch/hohndor/km/v110-baseline-20260825/full-sweep
ont=ore_ont_${id}.owl
sha=$(cut -d' ' -f1 < "$root/km.sha256")
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$sha" ]]
mkdir -p "$root/functional/results" "$root/functional/failures"
workers=(baseline 8)
if [[ $id == 3215 ]]; then workers=(baseline 4 8); fi
for label in "${workers[@]}"; do
  out="$root/functional/results/${id}-${label}.json"
  env_args=(--env KM_ROUTE=auto)
  if [[ $label != baseline ]]; then
    env_args+=(--env KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE="$label")
  fi
  /usr/bin/python3 "$harness/full_panel_run_one.py" \
    --kind km --arm "bridge_workers_${label}" \
    --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
    --binary "$root/km" --workers 16 --timeout 240 --memcap-mb 20480 \
    --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
    --gold-kind konclude \
    --workdir "${SLURM_TMPDIR:-/tmp}/km-bridge-workers-${SLURM_JOB_ID}-${id}/$label" \
    --failures-dir "$root/functional/failures" \
    --checkpoint "$root/functional/results/${id}-${label}.checkpoint.json" \
    --capture-km-route "${env_args[@]}" > "$out.tmp"
  /usr/bin/python3 - "$out.tmp" "$sha" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2], r
assert r["checkpointed"] and r["status"] == "ok" and r["verdict"] == "match", r
PY
  mv "$out.tmp" "$out"
done
/usr/bin/python3 - "$root/functional/results" "$id" "${workers[@]}" <<'PY'
import json,sys
root,id,*labels=sys.argv[1:]
rows=[json.load(open(f"{root}/{id}-{label}.json")) for label in labels]
assert len({r["signature_sha256"] for r in rows}) == 1
print(json.dumps({label:{"wall_s":r["wall_s"],"peak_mb":r["peak_mb"],"route":r["selected_route_trace"]} for label,r in zip(labels,rows)},sort_keys=True))
PY
echo FUNCTIONAL_COMPLETE ontology="$id"
