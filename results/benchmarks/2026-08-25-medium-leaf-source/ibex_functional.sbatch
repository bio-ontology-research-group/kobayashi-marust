#!/bin/bash
#SBATCH --job-name=km-medium-leaf-functional
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --array=0-16%4
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-medium-leaf-20260825/functional/slurm-%A_%a.out

set -euo pipefail
ids=(269 5815 7256 7343 7831 8145 8557 13902 13964 14508 15099 15178 16559 16684 868 3836 7499)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/v110-medium-leaf-20260825
harness=/ibex/scratch/hohndor/km/v110-baseline-20260825/full-sweep
ont=ore_ont_${id}.owl
sha=$(cut -d' ' -f1 < "$root/km.sha256")
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$sha" ]]
mkdir -p "$root/functional/results" "$root/functional/failures"
out="$root/functional/results/${id}.json"
/usr/bin/python3 "$harness/full_panel_run_one.py" \
  --kind km --arm medium_leaf_functional \
  --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
  --binary "$root/km" --workers 4 --timeout 240 --memcap-mb 20480 \
  --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
  --gold-kind konclude \
  --workdir "${SLURM_TMPDIR:-/tmp}/km-medium-leaf-${SLURM_JOB_ID}-${id}" \
  --failures-dir "$root/functional/failures" \
  --checkpoint "$root/functional/results/${id}.checkpoint.json" \
  --capture-km-route --env KM_ROUTE=auto > "$out.tmp"
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
print({k:r[k] for k in ("ont","wall_s","peak_mb","selected_route_trace","signature_sha256")})
PY
echo MEDIUM_LEAF_FUNCTIONAL_COMPLETE ontology="$id"
