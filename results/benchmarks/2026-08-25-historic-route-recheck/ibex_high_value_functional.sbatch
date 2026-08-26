#!/bin/bash
#SBATCH --job-name=km-high-route-functional
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:06:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --array=0-2%3
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-historic-route-20260825/high-value/slurm-%A_%a.out

set -euo pipefail
ids=(10908 10908 7499)
routes=(ht_shoq ht_bridge ht_bridge)
id=${ids[$SLURM_ARRAY_TASK_ID]}
route=${routes[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/v110-historic-route-20260825
baseline_root=/ibex/scratch/hohndor/km/v110-baseline-20260825
harness=$baseline_root/full-sweep
binary=$baseline_root/km
sha=3f313fe954e2fc779364a4999ba1d0ee6118aaeef0e1bf6e1cbc49ed7a196087
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$sha" ]]
mkdir -p "$root/high-value/results" "$root/high-value/failures"
ont=ore_ont_${id}.owl
out="$root/high-value/results/${id}-${route}.json"
/usr/bin/python3 "$harness/full_panel_run_one.py" \
  --kind km --arm "high_value_${route}" \
  --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
  --binary "$binary" --workers 4 --timeout 240 --memcap-mb 20480 \
  --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
  --gold-kind konclude \
  --workdir "${SLURM_TMPDIR:-/tmp}/km-high-route-${SLURM_JOB_ID}-${id}-${route}" \
  --failures-dir "$root/high-value/failures" \
  --checkpoint "$root/high-value/results/${id}-${route}.checkpoint.json" \
  --capture-km-route --env "KM_ROUTE=$route" > "$out.tmp"
/usr/bin/python3 - "$out.tmp" "$sha" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2] and r["checkpointed"], r
PY
mv "$out.tmp" "$out"
/usr/bin/python3 - "$out" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
print({k:r.get(k) for k in ("ont","status","verdict","wall_s","peak_mb","selected_route_trace","signature_sha256")})
PY
echo HIGH_VALUE_ROUTE_COMPLETE ontology="$id" route="$route"
