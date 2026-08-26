#!/bin/bash
#SBATCH --job-name=km-flat-screen-functional
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --array=0-1%1
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-direct-flat-screen-20260825/functional/slurm-%A_%a.out

set -euo pipefail
ids=(10689 868)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/v110-direct-flat-screen-20260825
harness=/ibex/scratch/hohndor/km/v110-baseline-20260825/full-sweep
ont=ore_ont_${id}.owl
sha=$(cut -d' ' -f1 < "$root/km.sha256")
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$sha" ]]
mkdir -p "$root/functional/results" "$root/functional/failures"
/usr/bin/python3 "$harness/full_panel_run_one.py" \
  --kind km --arm flat_screen \
  --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
  --binary "$root/km" --workers 4 --timeout 240 --memcap-mb 20480 \
  --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
  --gold-kind konclude \
  --workdir "${SLURM_TMPDIR:-/tmp}/km-flat-screen-${SLURM_JOB_ID}-${id}" \
  --failures-dir "$root/functional/failures" \
  --checkpoint "$root/functional/results/${id}.checkpoint.json" \
  --capture-km-route --env KM_ROUTE=auto > "$root/functional/results/${id}.json.tmp"
/usr/bin/python3 - "$root/functional/results/${id}.json.tmp" "$sha" "$id" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2], r
assert r["checkpointed"] and r["status"] == "ok" and r["verdict"] == "match", r
expected="flat_nf1" if sys.argv[3] == "10689" else "elc"
assert r["selected_route_trace"] == expected, r
print(json.dumps({k:r[k] for k in ["binary_sha256","wall_s","peak_mb","signature_sha256","selected_route_trace"]},sort_keys=True))
PY
mv "$root/functional/results/${id}.json.tmp" "$root/functional/results/${id}.json"
echo FUNCTIONAL_COMPLETE ontology="$id"
