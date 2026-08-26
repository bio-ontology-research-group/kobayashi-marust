#!/bin/bash
#SBATCH --job-name=km-flat-leaf-any
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --array=0-10%4
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-flat-leaf-20260825/functional-any/slurm-%A_%a.out

set -euo pipefail
ids=(8737 15059 16744 14042 9794 2243 10445 11389 14607 1559 868)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/v110-flat-leaf-20260825
harness=/ibex/scratch/hohndor/km/v110-baseline-20260825/full-sweep
ont=ore_ont_${id}.owl
sha=$(cut -d' ' -f1 < "$root/km.sha256")
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$sha" ]]
mkdir -p "$root/functional-any/results" "$root/functional-any/failures"
out="$root/functional-any/results/${id}.json"
/usr/bin/python3 "$harness/full_panel_run_one.py" \
  --kind km --arm flat_leaf_functional_any \
  --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
  --binary "$root/km" --workers 4 --timeout 240 --memcap-mb 20480 \
  --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
  --gold-kind konclude \
  --workdir "${SLURM_TMPDIR:-/tmp}/km-flat-leaf-any-${SLURM_JOB_ID}-${id}" \
  --failures-dir "$root/functional-any/failures" \
  --checkpoint "$root/functional-any/results/${id}.checkpoint.json" \
  --capture-km-route --env KM_ROUTE=auto > "$out.tmp"
/usr/bin/python3 - "$out.tmp" "$sha" "$id" <<'PY'
import json,sys
r=json.load(open(sys.argv[1])); expected=sys.argv[2]; ontology=int(sys.argv[3])
assert r["binary_sha256"] == expected, r
assert r["checkpointed"] and r["status"] == "ok" and r["verdict"] == "match", r
if ontology in {1559,868}:
    assert r["selected_route_trace"] != "flat_nf1", r
else:
    assert r["selected_route_trace"] == "flat_nf1", r
PY
mv "$out.tmp" "$out"
/usr/bin/python3 - "$out" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
print(json.dumps({k:r[k] for k in ["ont","wall_s","peak_mb","selected_route_trace","signature_sha256"]},sort_keys=True))
PY
echo FUNCTIONAL_ANY_COMPLETE ontology="$id"
