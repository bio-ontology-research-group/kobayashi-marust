#!/bin/bash
#SBATCH --job-name=km-stream-flat-gold
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-7%1
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-stream-flat-20260825/gold-pair/slurm-%A_%a.out

set -euo pipefail
ids=(868 11395 3836 1559)
task=$SLURM_ARRAY_TASK_ID
id=${ids[$((task / 2))]}
rep=$((task % 2))
root=/ibex/scratch/hohndor/km/v110-stream-flat-20260825
baseline_root=/ibex/scratch/hohndor/km/v110-baseline-20260825
harness=$baseline_root/full-sweep
base=$baseline_root/km
cand=$root/km
base_sha=3f313fe954e2fc779364a4999ba1d0ee6118aaeef0e1bf6e1cbc49ed7a196087
cand_sha=ae629a04cbe37cf3a75e39946125d9a09d66876d07ef1bfceb7cef8a734c35a6
[[ $(sha256sum "$base" | cut -d' ' -f1) == "$base_sha" ]]
[[ $(sha256sum "$cand" | cut -d' ' -f1) == "$cand_sha" ]]
mkdir -p "$root/gold-pair/results" "$root/gold-pair/failures"
ont=ore_ont_${id}.owl
if (( rep == 0 )); then arms=(baseline candidate); else arms=(candidate baseline); fi
for arm in "${arms[@]}"; do
  if [[ $arm == baseline ]]; then binary=$base; expected=$base_sha; else binary=$cand; expected=$cand_sha; fi
  out="$root/gold-pair/results/${id}-${rep}-${arm}.json"
  /usr/bin/python3 "$harness/full_panel_run_one.py" \
    --kind km --arm "stream_flat_${arm}" \
    --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
    --binary "$binary" --workers 16 --timeout 240 --memcap-mb 20480 \
    --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
    --gold-kind konclude \
    --workdir "${SLURM_TMPDIR:-/tmp}/km-stream-flat-gold-${SLURM_JOB_ID}-${id}-${rep}-${arm}" \
    --failures-dir "$root/gold-pair/failures" \
    --checkpoint "$root/gold-pair/results/${id}-${rep}-${arm}.checkpoint.json" \
    --capture-km-route --env KM_ROUTE=auto > "$out.tmp"
  /usr/bin/python3 - "$out.tmp" "$expected" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2], r
assert r["checkpointed"] and r["status"] == "ok" and r["verdict"] == "match", r
PY
  mv "$out.tmp" "$out"
done
/usr/bin/python3 - "$root/gold-pair/results/${id}-${rep}-baseline.json" "$root/gold-pair/results/${id}-${rep}-candidate.json" <<'PY'
import json,sys
b,c=(json.load(open(path)) for path in sys.argv[1:])
for key in ("status","verdict","consistent","signature_sha256","subsumptions","unsatisfiable"):
    assert b.get(key) == c.get(key), (key,b.get(key),c.get(key))
print({"ont":b["ont"],"baseline_wall":b["wall_s"],"candidate_wall":c["wall_s"],
       "baseline_peak":b["peak_mb"],"candidate_peak":c["peak_mb"],
       "candidate_route":c.get("selected_route_trace")})
PY
echo STREAM_FLAT_GOLD_PAIR_COMPLETE ontology="$id" repeat="$rep"
