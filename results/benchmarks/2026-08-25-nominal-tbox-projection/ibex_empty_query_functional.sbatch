#!/bin/bash
#SBATCH --job-name=km-empty-query-any
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --array=0-8%4
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-empty-query-v8-20260825/functional/slurm-%A_%a.out

set -euo pipefail
ids=(148 1790 3050 6765 7474 8322 8480 8999 16462)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/v110-empty-query-v8-20260825
harness=/ibex/scratch/hohndor/km/v110-baseline-20260825/full-sweep
ont=ore_ont_${id}.owl
sha=$(cut -d' ' -f1 < "$root/km.sha256")
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$sha" ]]
mkdir -p "$root/functional/results" "$root/functional/failures"
out="$root/functional/results/${id}.json"
/usr/bin/python3 "$harness/full_panel_run_one.py" \
  --kind km --arm empty_taxonomy_projection_functional \
  --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
  --binary "$root/km" --workers 4 --timeout 240 --memcap-mb 20480 \
  --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
  --gold-kind konclude \
  --workdir "${SLURM_TMPDIR:-/tmp}/km-empty-query-any-${SLURM_JOB_ID}-${id}" \
  --failures-dir "$root/functional/failures" \
  --checkpoint "$root/functional/results/${id}.checkpoint.json" \
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
echo EMPTY_QUERY_FUNCTIONAL_COMPLETE ontology="$id"
