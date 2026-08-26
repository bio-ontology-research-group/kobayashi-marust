#!/bin/bash
#SBATCH --job-name=km-abox-project-v2-any
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --array=0-8%4
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-nominal-projection-v2-20260825/functional-any/slurm-%A_%a.out

set -euo pipefail
ids=(148 1790 3050 6765 7474 8322 8480 8999 16462)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/v110-nominal-projection-v2-20260825
harness=/ibex/scratch/hohndor/km/v110-baseline-20260825/full-sweep
ont=ore_ont_${id}.owl
sha=$(cut -d' ' -f1 < "$root/km.sha256")
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$sha" ]]
mkdir -p "$root/functional-any/results" "$root/functional-any/failures"
out="$root/functional-any/results/${id}.json"
/usr/bin/python3 "$harness/full_panel_run_one.py" \
  --kind km --arm nominal_projection_v2_functional_any \
  --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
  --binary "$root/km" --workers 4 --timeout 240 --memcap-mb 20480 \
  --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
  --gold-kind konclude \
  --workdir "${SLURM_TMPDIR:-/tmp}/km-abox-project-v2-any-${SLURM_JOB_ID}-${id}" \
  --failures-dir "$root/functional-any/failures" \
  --checkpoint "$root/functional-any/results/${id}.checkpoint.json" \
  --capture-km-route --env KM_ROUTE=auto \
  --env KM_ABOX_DISJOINT_UNION_CHECK=1 > "$out.tmp"
/usr/bin/python3 - "$out.tmp" "$sha" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2], r
assert r["checkpointed"] and r["status"] == "ok" and r["verdict"] == "match", r
PY
mv "$out.tmp" "$out"
/usr/bin/python3 - "$out" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
print({k:r[k] for k in
       ("ont","wall_s","peak_mb","selected_route_trace","signature_sha256")})
PY
echo FUNCTIONAL_V2_COMPLETE ontology="$id"
