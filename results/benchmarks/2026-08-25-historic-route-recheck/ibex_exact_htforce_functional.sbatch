#!/bin/bash
#SBATCH --job-name=km-exact-htforce
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:06:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --array=0-1%2
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-historic-route-20260825/exact-htforce/slurm-%A_%a.out

set -euo pipefail
ids=(10908 7499)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/v110-historic-route-20260825
baseline_root=/ibex/scratch/hohndor/km/v110-baseline-20260825
harness=$baseline_root/full-sweep
binary=$baseline_root/km
sha=3f313fe954e2fc779364a4999ba1d0ee6118aaeef0e1bf6e1cbc49ed7a196087
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$sha" ]]
mkdir -p "$root/exact-htforce/results" "$root/exact-htforce/failures"
ont=ore_ont_${id}.owl
out="$root/exact-htforce/results/${id}.json"
/usr/bin/python3 "$harness/full_panel_run_one.py" \
  --kind km --arm exact_historic_htforce \
  --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
  --binary "$binary" --workers 16 --timeout 240 --memcap-mb 20480 \
  --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
  --gold-kind konclude \
  --workdir "${SLURM_TMPDIR:-/tmp}/km-exact-htforce-${SLURM_JOB_ID}-${id}" \
  --failures-dir "$root/exact-htforce/failures" \
  --checkpoint "$root/exact-htforce/results/${id}.checkpoint.json" \
  --capture-km-route \
  --env KM_ROUTE=manual --env KM_THREADS=16 --env KM_PAR_MEM_GB=18 \
  --env KM_HT_MEM_GB=18 --env KM_KEEP_CHAIN_AXIOMS=1 --env KM_ABSORB=1 \
  --env KM_ABSORB_PORTFOLIO=1 --env KM_HT_FORCE=1 --env KM_HT_MODE=race > "$out.tmp"
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
echo EXACT_HTFORCE_COMPLETE ontology="$id"
