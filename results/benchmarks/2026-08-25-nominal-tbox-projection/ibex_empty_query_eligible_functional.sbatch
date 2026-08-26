#!/bin/bash
#SBATCH --job-name=km-empty-query-eligible
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --array=0-48%8
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-empty-query-v8-20260825/eligible/slurm-%A_%a.out

set -euo pipefail
ids=(
  443 1325 1340 1555 1902 2313 2361 2678 2860 3560
  3905 4572 4755 5292 5549 5572 5781 6223 6477 6682
  6720 6855 7052 7195 7417 7914 8068 8641 8941 9002
  9014 9400 9499 10073 10123 10781 11311 11315 11316 11502
  11523 11745 12414 13503 13912 14450 14848 15172 15288
)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/v110-empty-query-v8-20260825
harness=/ibex/scratch/hohndor/km/v110-baseline-20260825/full-sweep
ont=ore_ont_${id}.owl
sha=$(cut -d' ' -f1 < "$root/km.sha256")
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$sha" ]]
mkdir -p "$root/eligible/results" "$root/eligible/failures"
out="$root/eligible/results/${id}.json"
/usr/bin/python3 "$harness/full_panel_run_one.py" \
  --kind km --arm empty_taxonomy_projection_eligible_functional \
  --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
  --binary "$root/km" --workers 4 --timeout 240 --memcap-mb 20480 \
  --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
  --gold-kind konclude \
  --workdir "${SLURM_TMPDIR:-/tmp}/km-empty-query-eligible-${SLURM_JOB_ID}-${id}" \
  --failures-dir "$root/eligible/failures" \
  --checkpoint "$root/eligible/results/${id}.checkpoint.json" \
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
echo EMPTY_QUERY_ELIGIBLE_COMPLETE ontology="$id"
