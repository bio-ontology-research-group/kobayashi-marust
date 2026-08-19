#!/bin/bash
#SBATCH --job-name=km-bridge-closed-pair
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-19%10
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/bridge-closed-20260815/pair/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/bridge-closed-20260815
pair=$root/pair
harness=/ibex/scratch/hohndor/km/intersection-inproc-20260815/full-sweep
baseline=/ibex/scratch/hohndor/km/median-overhead-20260815/km
candidate=$root/km
baseline_sha=4aa2370c8cebac9b78fcd64cfbfa6d4be0af2bd87bb6b5c0f351c478d88056af
candidate_sha=c5b85fea05cae73db5f66ec3a0b86c8439fd58ec207a612b07e85c91d08081dd
index=${SLURM_ARRAY_TASK_ID:?}
ontology_index=$((index / 2))
repeat=$((index % 2))
ontology=$(sed -n "$((ontology_index + 1))p" "$pair/panel.txt")
[[ -n $ontology ]]
[[ $(sha256sum "$baseline" | cut -d' ' -f1) == $baseline_sha ]]
[[ $(sha256sum "$candidate" | cut -d' ' -f1) == $candidate_sha ]]
mkdir -p "$pair/results" "$pair/failures"
runner=$harness/full_panel_run_one.py
case "$ontology" in
  ore_ont_3524.owl|ore_ont_13503.owl|ore_ont_4669.owl|ore_ont_15703.owl)
    runner=$harness/full_panel_run_one_collision_safe.py ;;
esac
if (( (ontology_index + repeat) % 2 == 0 )); then order=(baseline candidate); else order=(candidate baseline); fi
for sequence in 0 1; do
  arm=${order[$sequence]}; binary=$baseline; sha=$baseline_sha
  if [[ $arm == candidate ]]; then binary=$candidate; sha=$candidate_sha; fi
  final=$pair/results/${ontology}.r${repeat}-${sequence}-${arm}.json
  checkpoint=${final}.checkpoint.json
  /usr/bin/python3 "$runner" --kind km --arm "$arm" \
    --ontology "/ibex/scratch/hohndor/km/corpus/$ontology" --binary "$binary" --binary-sha "$sha" \
    --workers 16 --timeout 240 --memcap-mb 20480 \
    --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ontology.sig.gz" --gold-kind konclude \
    --workdir "${SLURM_TMPDIR:-/tmp}/km-bridge-closed-${index}-${arm}" \
    --failures-dir "$pair/failures" --checkpoint "$checkpoint" --capture-km-route --env KM_ROUTE=auto \
    > "${final}.tmp"
  /usr/bin/python3 - "${final}.tmp" "$ontology" "$sha" <<'PY'
import json,sys
r=json.load(open(sys.argv[1])); assert r["ont"]==sys.argv[2] and r["binary_sha256"]==sys.argv[3],r
assert r["status"]=="ok",r
PY
  mv "${final}.tmp" "$final"
done
/usr/bin/python3 - "$pair/results/${ontology}.r${repeat}-0-${order[0]}.json" "$pair/results/${ontology}.r${repeat}-1-${order[1]}.json" <<'PY'
import json,sys
a,b=(json.load(open(p)) for p in sys.argv[1:])
keys=("status","verdict","signature_sha256","consistent","missing","extra","missing_unsat","extra_unsat","subsumptions","unsatisfiable","selected_route_trace")
assert all(a.get(k)==b.get(k) for k in keys),(a,b)
PY
echo "PAIR_COMPLETE ontology=$ontology repeat=$repeat order=${order[*]}"
