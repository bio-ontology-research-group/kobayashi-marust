#!/bin/bash
#SBATCH --job-name=km-cyclic-flat-gold
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-2%1
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-cyclic-flat-20260825/gold-pair/slurm-%A_%a.out

set -euo pipefail
task=$SLURM_ARRAY_TASK_ID
root=/ibex/scratch/hohndor/km/v110-cyclic-flat-20260825
harness=/ibex/scratch/hohndor/km/v110-baseline-20260825/full-sweep
candidate=$root/km
baseline=/ibex/scratch/hohndor/km/v110-baseline-20260825/km
candidate_sha=$(cut -d' ' -f1 < "$root/km.sha256")
baseline_sha=3f313fe954e2fc779364a4999ba1d0ee6118aaeef0e1bf6e1cbc49ed7a196087
[[ $(sha256sum "$candidate" | cut -d' ' -f1) == "$candidate_sha" ]]
[[ $(sha256sum "$baseline" | cut -d' ' -f1) == "$baseline_sha" ]]
mkdir -p "$root/gold-pair/results" "$root/gold-pair/failures"
case $task in
  0) arms=(v1 fallback direct) ;;
  1) arms=(direct v1 fallback) ;;
  2) arms=(fallback direct v1) ;;
esac
for arm in "${arms[@]}"; do
  out="$root/gold-pair/results/${task}-${arm}.json"
  binary=$candidate
  expected=$candidate_sha
  env_args=(--env KM_ROUTE=auto)
  expected_route=flat_nf1
  if [[ $arm == fallback ]]; then
    env_args+=(--env KM_NO_DIRECT_FLAT_NF1=1)
    expected_route=elc
  elif [[ $arm == v1 ]]; then
    binary=$baseline
    expected=$baseline_sha
    expected_route=elc
  fi
  /usr/bin/python3 "$harness/full_panel_run_one_collision_safe.py" \
    --kind km --arm "cyclic_flat_${arm}" \
    --ontology /ibex/scratch/hohndor/km/corpus/ore_ont_3524.owl \
    --binary "$binary" --workers 16 --timeout 240 --memcap-mb 20480 \
    --gold /ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__ore_ont_3524.owl.sig.gz \
    --gold-kind konclude \
    --workdir "${SLURM_TMPDIR:-/tmp}/km-cyclic-flat-${SLURM_JOB_ID}-${task}-${arm}" \
    --failures-dir "$root/gold-pair/failures" \
    --checkpoint "$root/gold-pair/results/${task}-${arm}.checkpoint.json" \
    --capture-km-route "${env_args[@]}" > "$out.tmp"
  /usr/bin/python3 - "$out.tmp" "$expected" "$expected_route" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2], r
assert r["checkpointed"] and r["status"] == "ok" and r["verdict"] == "match", r
assert r["selected_route_trace"] == sys.argv[3], r
assert r["fulliri_taxonomy_sha256"] == "090129a7fbaa14652ada3408dd1f160e7dd4a09a3502cc3323d8dad734e8893a", r
assert r["fulliri_subsumptions"] == 1604386 and r["fulliri_unsatisfiable"] == 0, r
PY
  mv "$out.tmp" "$out"
done
/usr/bin/python3 - "$root/gold-pair/results/${task}-v1.json" "$root/gold-pair/results/${task}-fallback.json" "$root/gold-pair/results/${task}-direct.json" <<'PY'
import json,sys
v,f,d=(json.load(open(path)) for path in sys.argv[1:])
for key in ("status","verdict","consistent","fulliri_taxonomy_sha256","fulliri_subsumptions","fulliri_unsatisfiable"):
    assert v.get(key) == f.get(key) == d.get(key), (key,v.get(key),f.get(key),d.get(key))
print({"v1_wall":v["wall_s"],"fallback_wall":f["wall_s"],"direct_wall":d["wall_s"],
       "v1_peak":v["peak_mb"],"fallback_peak":f["peak_mb"],"direct_peak":d["peak_mb"]})
PY
echo CYCLIC_FLAT_GOLD_PAIR_COMPLETE repeat="$task"
