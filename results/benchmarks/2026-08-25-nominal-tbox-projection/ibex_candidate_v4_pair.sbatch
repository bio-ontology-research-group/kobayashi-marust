#!/bin/bash
#SBATCH --job-name=km-abox-project-v4-pair
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --array=0-8%2
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-nominal-projection-v4-20260825/pairs/slurm-%A_%a.out

set -euo pipefail
ids=(148 1790 3050 6765 7474 8322 8480 8999 16462)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/v110-nominal-projection-v4-20260825
harness=/ibex/scratch/hohndor/km/v110-baseline-20260825/full-sweep
ont=ore_ont_${id}.owl
sha=$(cut -d' ' -f1 < "$root/km.sha256")
[[ "$sha" == 69fe6f20b41d688c63032e093087032a64d39152ef4f6417d77dd12be44b5b35 ]]
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$sha" ]]
mkdir -p "$root/pairs/results" "$root/pairs/failures"

run_arm() {
  local arm=$1
  shift
  local out="$root/pairs/results/${id}.${arm}.json"
  /usr/bin/python3 "$harness/full_panel_run_one.py" \
    --kind km --arm "$arm" \
    --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
    --binary "$root/km" --workers 4 --timeout 240 --memcap-mb 20480 \
    --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
    --gold-kind konclude \
    --workdir "${SLURM_TMPDIR:-/tmp}/km-abox-project-v4-${SLURM_JOB_ID}-${id}-${arm}" \
    --failures-dir "$root/pairs/failures" \
    --checkpoint "$root/pairs/results/${id}.${arm}.checkpoint.json" \
    --capture-km-route --env KM_ROUTE=auto "$@" > "$out.tmp"
  /usr/bin/python3 - "$out.tmp" "$sha" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2], r
assert r["checkpointed"] and r["status"] == "ok" and r["verdict"] == "match", r
PY
  mv "$out.tmp" "$out"
}

if (( SLURM_ARRAY_TASK_ID % 2 )); then
  run_arm candidate --env KM_ABOX_DISJOINT_UNION_CHECK=1
  run_arm baseline
else
  run_arm baseline
  run_arm candidate --env KM_ABOX_DISJOINT_UNION_CHECK=1
fi

/usr/bin/python3 - "$root/pairs/results/${id}.baseline.json" "$root/pairs/results/${id}.candidate.json" <<'PY'
import json,sys
b,c=(json.load(open(p)) for p in sys.argv[1:])
for key in ("status","verdict","consistent","solved","subsumptions","unsatisfiable","signature_sha256"):
    assert b[key] == c[key], (key,b[key],c[key])
print({"ont":b["ont"],"baseline_wall":b["wall_s"],"candidate_wall":c["wall_s"],
       "baseline_peak":b["peak_mb"],"candidate_peak":c["peak_mb"],
       "baseline_route":b["selected_route_trace"],"candidate_route":c["selected_route_trace"]})
PY
echo CANDIDATE_V4_PAIR_COMPLETE ontology="$id"
