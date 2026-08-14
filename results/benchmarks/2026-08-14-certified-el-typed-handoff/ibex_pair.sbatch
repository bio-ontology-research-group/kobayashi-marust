#!/bin/bash
#SBATCH --job-name=km-cert-el-typed
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:35:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/certified-el-typed-handoff-20260814/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/certified-el-typed-handoff-20260814
baseline=/ibex/scratch/hohndor/km/prod1-narrow-pidfd-20260814/km
candidate=$root/km
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
baseline_sha=4379bd61e853869c81148633365740d058e1f768b3320c69334f64e3cf88127f
candidate_sha=$(cut -d' ' -f1 < "$root/km.sha256")
[[ $(sha256sum "$baseline" | cut -d' ' -f1) == "$baseline_sha" ]]
[[ $(sha256sum "$candidate" | cut -d' ' -f1) == "$candidate_sha" ]]
cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]

mkdir -p "$root/results" "$root/failures"
work=${SLURM_TMPDIR:-/tmp}/km-cert-el-typed-${SLURM_JOB_ID}
for ont_id in 8737 16744; do
  for rep in 1 2 3; do
    order=(baseline candidate)
    if [[ $rep == 2 ]]; then order=(candidate baseline); fi
    for label in "${order[@]}"; do
      binary=$baseline; expected=$baseline_sha
      if [[ $label == candidate ]]; then binary=$candidate; expected=$candidate_sha; fi
      ont=ore_ont_${ont_id}.owl
      out="$root/results/${ont_id}-${label}-${rep}.json"
      /usr/bin/python3 "$harness/full_panel_run_one.py" \
        --kind km --arm "${ont_id}_${label}_${rep}" \
        --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
        --binary "$binary" --workers 16 --timeout 240 --memcap-mb 20480 \
        --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
        --gold-kind konclude --workdir "$work/$ont_id/$label-$rep" \
        --failures-dir "$root/failures" \
        --checkpoint "$root/results/${ont_id}-${label}-${rep}.checkpoint.json" \
        --capture-km-route --env KM_ROUTE=auto > "$out.tmp"
      /usr/bin/python3 - "$out.tmp" "$expected" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2]
assert r["checkpointed"] and r["status"] == "ok" and r["verdict"] == "match", r
assert r["selected_route_trace"] == "certified_el_production", r
PY
      mv "$out.tmp" "$out"
    done
  done
done

/usr/bin/python3 - "$root/results" <<'PY'
import glob,json,statistics,sys
root=sys.argv[1]
summary={}
for ont in (8737,16744):
    def rows(label):
        return [json.load(open(p)) for p in sorted(glob.glob(f"{root}/{ont}-{label}-[123].json"))]
    b=rows("baseline"); c=rows("candidate")
    assert len(b)==len(c)==3
    assert len({r["signature_sha256"] for r in b+c})==1
    summary[str(ont)]={
      "baseline_wall_mean":statistics.mean(r["wall_s"] for r in b),
      "candidate_wall_mean":statistics.mean(r["wall_s"] for r in c),
      "baseline_peak_mean":statistics.mean(r["peak_mb"] for r in b),
      "candidate_peak_mean":statistics.mean(r["peak_mb"] for r in c),
      "baseline_peak_max":max(r["peak_mb"] for r in b),
      "candidate_peak_max":max(r["peak_mb"] for r in c),
    }
print(json.dumps(summary,indent=2,sort_keys=True))
assert sum(v["candidate_wall_mean"] for v in summary.values()) < sum(v["baseline_wall_mean"] for v in summary.values()) - 5.0, summary
assert all(v["candidate_peak_mean"] <= v["baseline_peak_mean"] for v in summary.values()), summary
assert all(v["candidate_peak_max"] <= v["baseline_peak_max"] for v in summary.values()), summary
PY
echo CERTIFIED_EL_TYPED_HANDOFF_PAIR_COMPLETE
