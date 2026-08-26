#!/bin/bash
#SBATCH --job-name=km-simple-hierarchy-gate
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-3
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-simple-hierarchy-20260825/focused/slurm-%A_%a.out

set -euo pipefail
ids=(868 8486 9674 10689)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/v110-simple-hierarchy-20260825
baseline_root=/ibex/scratch/hohndor/km/v110-baseline-20260825
harness=/ibex/scratch/hohndor/km/v110-baseline-20260825/full-sweep
baseline="$baseline_root/km"
candidate="$root/km"
baseline_sha=3f313fe954e2fc779364a4999ba1d0ee6118aaeef0e1bf6e1cbc49ed7a196087
candidate_sha=$(cut -d' ' -f1 < "$root/km.sha256")
ont=ore_ont_${id}.owl

[[ $(sha256sum "$baseline" | cut -d' ' -f1) == "$baseline_sha" ]]
[[ $(sha256sum "$candidate" | cut -d' ' -f1) == "$candidate_sha" ]]
cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]
PYTHONPATH="$harness" /usr/bin/python3 -c \
  'import full_panel_fingerprint, full_panel_run_one, full_panel_run_one_collision_safe, full_panel_run_one_fulliri_only, ore_canon, tree_watchdog'

mkdir -p "$root/focused/results" "$root/focused/failures"
work=${SLURM_TMPDIR:-/tmp}/km-simple-hierarchy-${SLURM_JOB_ID}-${id}
for rep in 1 2 3; do
  if (( rep % 2 == 1 )); then order=(baseline candidate); else order=(candidate baseline); fi
  for label in "${order[@]}"; do
    binary=$baseline; expected=$baseline_sha
    if [[ $label == candidate ]]; then binary=$candidate; expected=$candidate_sha; fi
    out="$root/focused/results/${id}-${label}-${rep}.json"
    /usr/bin/python3 "$harness/full_panel_run_one.py" \
      --kind km --arm "simple_hierarchy_${label}_${rep}" \
      --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
      --binary "$binary" --workers 16 --timeout 240 --memcap-mb 20480 \
      --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
      --gold-kind konclude --workdir "$work/$label-$rep" \
      --failures-dir "$root/focused/failures" \
      --checkpoint "$root/focused/results/${id}-${label}-${rep}.checkpoint.json" \
      --capture-km-route --env KM_ROUTE=auto > "$out.tmp"
    /usr/bin/python3 - "$out.tmp" "$expected" "$label" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2], r
assert r["checkpointed"] and r["status"] == "ok" and r["verdict"] == "match", r
if sys.argv[3] == "candidate":
    assert r["selected_route_trace"] == "simple_hierarchy", r
PY
    mv "$out.tmp" "$out"
  done
done

/usr/bin/python3 - "$root/focused/results" "$id" <<'PY'
import glob,json,statistics,sys
root,id=sys.argv[1:]
def rows(label):
    return [json.load(open(p)) for p in sorted(glob.glob(f"{root}/{id}-{label}-[123].json"))]
b=rows("baseline"); c=rows("candidate")
assert len(b)==len(c)==3
assert len({r["signature_sha256"] for r in b+c})==1
summary={
 "ontology":id,
 "baseline_wall_median":statistics.median(r["wall_s"] for r in b),
 "candidate_wall_median":statistics.median(r["wall_s"] for r in c),
 "baseline_peak_median":statistics.median(r["peak_mb"] for r in b),
 "candidate_peak_median":statistics.median(r["peak_mb"] for r in c),
}
summary["wall_change_pct"]=100*(summary["candidate_wall_median"]/summary["baseline_wall_median"]-1)
summary["peak_change_pct"]=100*(summary["candidate_peak_median"]/summary["baseline_peak_median"]-1)
print(json.dumps(summary,sort_keys=True))
assert summary["candidate_wall_median"] < summary["baseline_wall_median"], summary
assert summary["candidate_peak_median"] < summary["baseline_peak_median"], summary
PY
echo FOCUSED_GATE_COMPLETE ontology="$id"
