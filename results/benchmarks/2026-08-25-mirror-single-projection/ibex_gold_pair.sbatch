#!/bin/bash
#SBATCH --job-name=km-mirror-integrated-gold
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-1%1
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-cyclic-flat-20260825/mirror-gold-pair/slurm-%A_%a.out

set -euo pipefail
task=$SLURM_ARRAY_TASK_ID
root=/ibex/scratch/hohndor/km/v110-cyclic-flat-20260825
harness=/ibex/scratch/hohndor/km/v110-baseline-20260825/full-sweep
binary=$root/km
expected=$(cut -d' ' -f1 < "$root/km.sha256")
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected" ]]
mkdir -p "$root/mirror-gold-pair/results" "$root/mirror-gold-pair/failures"
if (( task == 0 )); then arms=(double single); else arms=(single double); fi
for arm in "${arms[@]}"; do
  out="$root/mirror-gold-pair/results/${task}-${arm}.json"
  env_args=(--env KM_ROUTE=auto)
  if [[ $arm == double ]]; then env_args+=(--env KM_MIRROR_DOUBLE_CHECK=1); fi
  /usr/bin/python3 "$harness/full_panel_run_one_collision_safe.py" \
    --kind km --arm "mirror_${arm}" \
    --ontology /ibex/scratch/hohndor/km/corpus/ore_ont_4669.owl \
    --binary "$binary" --workers 16 --timeout 240 --memcap-mb 20480 \
    --gold /ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__ore_ont_4669.owl.sig.gz \
    --gold-kind konclude \
    --workdir "${SLURM_TMPDIR:-/tmp}/km-mirror-single-${SLURM_JOB_ID}-${task}-${arm}" \
    --failures-dir "$root/mirror-gold-pair/failures" \
    --checkpoint "$root/mirror-gold-pair/results/${task}-${arm}.checkpoint.json" \
    --capture-km-route "${env_args[@]}" > "$out.tmp"
  /usr/bin/python3 - "$out.tmp" "$expected" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2], r
assert r["checkpointed"] and r["status"] == "ok" and r["verdict"] == "match", r
assert r["selected_route_trace"] == "mirror_private", r
assert r["fulliri_taxonomy_sha256"] == "a482e066a22110df593bf3a4c1fdd0ef4404f7141903b2101b85aae49811cb30", r
PY
  mv "$out.tmp" "$out"
done
/usr/bin/python3 - "$root/mirror-gold-pair/results/${task}-double.json" "$root/mirror-gold-pair/results/${task}-single.json" <<'PY'
import json,sys
d,s=(json.load(open(path)) for path in sys.argv[1:])
for key in ("status","verdict","consistent","fulliri_taxonomy_sha256","fulliri_subsumptions","fulliri_unsatisfiable"):
    assert d.get(key) == s.get(key), (key,d.get(key),s.get(key))
print({"double_wall":d["wall_s"],"single_wall":s["wall_s"],
       "double_peak":d["peak_mb"],"single_peak":s["peak_mb"]})
PY
echo MIRROR_SINGLE_GOLD_PAIR_COMPLETE repeat="$task"
