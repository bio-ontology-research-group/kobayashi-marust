#!/bin/bash
#SBATCH --job-name=km-historic-route-pair
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-19%2
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-historic-route-20260825/slurm-%A_%a.out

set -euo pipefail
ids=(1272 6682 7246 12087 16596 4604 7581 9663 11460 11745)
routes=(elc_cert elc_cert elc_cert elc elc ht_bridge ht_bridge ht_bridge ht_bridge ht_bridge)
task=$SLURM_ARRAY_TASK_ID
slot=$((task / 2))
rep=$((task % 2))
id=${ids[$slot]}
forced=${routes[$slot]}
root=/ibex/scratch/hohndor/km/v110-historic-route-20260825
baseline_root=/ibex/scratch/hohndor/km/v110-baseline-20260825
harness=$baseline_root/full-sweep
binary=$baseline_root/km
sha=3f313fe954e2fc779364a4999ba1d0ee6118aaeef0e1bf6e1cbc49ed7a196087
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$sha" ]]
mkdir -p "$root/results" "$root/failures"
ont=ore_ont_${id}.owl
if (( rep == 0 )); then arms=(auto forced); else arms=(forced auto); fi
for arm in "${arms[@]}"; do
  if [[ $arm == auto ]]; then route=auto; else route=$forced; fi
  out="$root/results/${id}-${rep}-${arm}.json"
  /usr/bin/python3 "$harness/full_panel_run_one.py" \
    --kind km --arm "historic_${arm}_${route}" \
    --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
    --binary "$binary" --workers 16 --timeout 240 --memcap-mb 20480 \
    --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
    --gold-kind konclude \
    --workdir "${SLURM_TMPDIR:-/tmp}/km-historic-${SLURM_JOB_ID}-${id}-${rep}-${arm}" \
    --failures-dir "$root/failures" \
    --checkpoint "$root/results/${id}-${rep}-${arm}.checkpoint.json" \
    --capture-km-route --env "KM_ROUTE=$route" > "$out.tmp"
  /usr/bin/python3 - "$out.tmp" "$sha" "$arm" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2], r
assert r["checkpointed"], r
if sys.argv[3] == "auto":
    assert r["status"] == "ok" and r["verdict"] == "match", r
PY
  mv "$out.tmp" "$out"
done
/usr/bin/python3 - "$root/results/${id}-${rep}-auto.json" "$root/results/${id}-${rep}-forced.json" <<'PY'
import json,sys
a,f=(json.load(open(path)) for path in sys.argv[1:])
same=all(a.get(k)==f.get(k) for k in
         ("status","verdict","consistent","signature_sha256","subsumptions","unsatisfiable"))
print({"ont":a["ont"],"auto_wall":a["wall_s"],"auto_peak":a["peak_mb"],
       "forced_status":f["status"],"forced_verdict":f["verdict"],
       "forced_wall":f["wall_s"],"forced_peak":f["peak_mb"],
       "forced_route":f.get("selected_route_trace"),"semantic_equal":same})
PY
echo HISTORIC_ROUTE_PAIR_COMPLETE ontology="$id" route="$forced" repeat="$rep"
