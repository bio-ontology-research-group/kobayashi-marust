#!/bin/bash
#SBATCH --job-name=km-inproc-cb-specialist
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-39%20
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/inproc-cb-specialist-20260815/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/inproc-cb-specialist-20260815
harness=/ibex/scratch/hohndor/km/intersection-inproc-20260815/full-sweep
binary=/ibex/scratch/hohndor/km/median-overhead-20260815/km
sha=4aa2370c8cebac9b78fcd64cfbfa6d4be0af2bd87bb6b5c0f351c478d88056af
index=${SLURM_ARRAY_TASK_ID:?}
ontology_index=$((index / 2))
repeat=$((index % 2))
ontology=$(sed -n "$((ontology_index + 1))p" "$root/panel.txt")
[[ -n $ontology ]]
[[ $(sha256sum "$binary" | cut -d' ' -f1) == $sha ]]
mkdir -p "$root/results" "$root/failures"
runner=$harness/full_panel_run_one.py
case "$ontology" in
  ore_ont_3524.owl|ore_ont_13503.owl|ore_ont_4669.owl|ore_ont_15703.owl)
    runner=$harness/full_panel_run_one_collision_safe.py ;;
esac
if (( (ontology_index + repeat) % 2 == 0 )); then
  order=(baseline disabled)
else
  order=(disabled baseline)
fi
for sequence in 0 1; do
  arm=${order[$sequence]}
  final=$root/results/${ontology}.r${repeat}-${sequence}-${arm}.json
  checkpoint=${final}.checkpoint.json
  args=(--kind km --arm "$arm" --ontology "/ibex/scratch/hohndor/km/corpus/$ontology"
    --binary "$binary" --binary-sha "$sha" --workers 16 --timeout 240 --memcap-mb 20480
    --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ontology.sig.gz"
    --gold-kind konclude --workdir "${SLURM_TMPDIR:-/tmp}/km-inproc-probe-${index}-${arm}"
    --failures-dir "$root/failures" --checkpoint "$checkpoint" --capture-km-route
    --env KM_ROUTE=auto)
  if [[ $arm == disabled ]]; then args+=(--env KM_NO_INPROC_ENGINE=1); fi
  /usr/bin/python3 "$runner" "${args[@]}" > "${final}.tmp"
  /usr/bin/python3 - "${final}.tmp" "$ontology" "$sha" <<'PY'
import json, sys
r=json.load(open(sys.argv[1]))
assert r["ont"] == sys.argv[2] and r["binary_sha256"] == sys.argv[3], r
assert r["status"] == "ok", r
PY
  mv "${final}.tmp" "$final"
done
/usr/bin/python3 - "$root/results/${ontology}.r${repeat}-0-${order[0]}.json" "$root/results/${ontology}.r${repeat}-1-${order[1]}.json" <<'PY'
import json, sys
a,b=(json.load(open(p)) for p in sys.argv[1:])
keys=("status","verdict","signature_sha256","consistent","missing","extra","missing_unsat","extra_unsat","subsumptions","unsatisfiable","selected_route_trace")
assert all(a.get(k)==b.get(k) for k in keys),(a,b)
PY
echo "PAIR_COMPLETE ontology=$ontology repeat=$repeat order=${order[*]}"
