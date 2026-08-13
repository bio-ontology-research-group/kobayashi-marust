#!/bin/bash
#SBATCH --job-name=km-10621-seq-gate
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/10621-sequential-bridge-candidate-20260813/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/10621-sequential-bridge-candidate-20260813
baseline=/ibex/scratch/hohndor/km/candidate-78d5674-atomic-abox-20260813/km
candidate=$root/km
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
baseline_sha=d19938110369da96167feddf2a257550bf80aca1793afd40154d18d303663f8e
candidate_sha=$(cut -d' ' -f1 < "$root/km.sha256")
ont=ore_ont_10621.owl
[[ $(sha256sum "$baseline" | cut -d" " -f1) == "$baseline_sha" ]]
[[ $(sha256sum "$candidate" | cut -d" " -f1) == "$candidate_sha" ]]
cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]
PYTHONPATH="$harness" /usr/bin/python3 -c \
  'import full_panel_fingerprint, full_panel_run_one, full_panel_run_one_collision_safe, full_panel_run_one_fulliri_only, ore_canon, tree_watchdog'

mkdir -p "$root/results" "$root/failures"
work=${SLURM_TMPDIR:-/tmp}/km-10621-gate-${SLURM_JOB_ID}
for rep in 1 2 3; do
  for label in baseline candidate; do
    binary=$baseline; expected=$baseline_sha
    if [[ $label == candidate ]]; then binary=$candidate; expected=$candidate_sha; fi
    out="$root/results/${label}-${rep}.json"
    /usr/bin/python3 "$harness/full_panel_run_one.py" \
      --kind km --arm "10621_${label}_${rep}" \
      --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
      --binary "$binary" --workers 16 --timeout 240 --memcap-mb 20480 \
      --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
      --gold-kind konclude --workdir "$work/$label-$rep" --failures-dir "$root/failures" \
      --checkpoint "$root/results/${label}-${rep}.checkpoint.json" \
      --capture-km-route --env KM_ROUTE=auto > "$out.tmp"
    /usr/bin/python3 - "$out.tmp" "$expected" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2]
assert r["checkpointed"] and r["status"] == "ok" and r["verdict"] == "match", r
assert r["selected_route_trace"] == "certified_nominals", r
PY
    mv "$out.tmp" "$out"
  done
done
/usr/bin/python3 - "$root/results" <<'PY'
import glob,json,statistics,sys
root=sys.argv[1]
def rows(label): return [json.load(open(p)) for p in sorted(glob.glob(f"{root}/{label}-[123].json"))]
b=rows("baseline"); c=rows("candidate")
assert len(b)==len(c)==3
assert {r["signature_sha256"] for r in b+c}.__len__()==1
summary={
 "baseline_wall_mean":statistics.mean(r["wall_s"] for r in b),
 "candidate_wall_mean":statistics.mean(r["wall_s"] for r in c),
 "baseline_peak_mean":statistics.mean(r["peak_mb"] for r in b),
 "candidate_peak_mean":statistics.mean(r["peak_mb"] for r in c),
}
summary["wall_change_pct"]=100*(summary["candidate_wall_mean"]/summary["baseline_wall_mean"]-1)
summary["peak_change_pct"]=100*(summary["candidate_peak_mean"]/summary["baseline_peak_mean"]-1)
print(summary)
assert summary["candidate_wall_mean"] <= summary["baseline_wall_mean"] * 1.03, summary
assert summary["candidate_peak_mean"] <= summary["baseline_peak_mean"] * 0.25, summary
PY
echo CANDIDATE_GATE_COMPLETE
