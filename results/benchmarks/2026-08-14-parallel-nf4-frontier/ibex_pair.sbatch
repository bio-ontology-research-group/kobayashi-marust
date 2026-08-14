#!/bin/bash
#SBATCH --job-name=km-par-nf4-pair
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:25:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/parallel-nf4-frontier-20260814/pair-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/parallel-nf4-frontier-20260814
baseline=/ibex/scratch/hohndor/km/certified-el-typed-handoff-20260814/km
candidate=$root/km
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
baseline_sha=13b4d406aaddb4b94d1d9f9740cfd5839df851193d049bd76f911a3f1ab84e30
candidate_sha=$(cut -d' ' -f1 < "$root/km.sha256")
[[ $(sha256sum "$baseline" | cut -d' ' -f1) == "$baseline_sha" ]]
[[ $(sha256sum "$candidate" | cut -d' ' -f1) == "$candidate_sha" ]]
mkdir -p "$root/results" "$root/failures"
work=${SLURM_TMPDIR:-/tmp}/km-par-nf4-${SLURM_JOB_ID}
for ont_id in 8737 16744; do
  for rep in 1 2 3; do
    order=(baseline candidate)
    if [[ $rep == 2 ]]; then order=(candidate baseline); fi
    for label in "${order[@]}"; do
      binary=$baseline; expected=$baseline_sha; envs=(--env KM_ROUTE=auto)
      if [[ $label == candidate ]]; then
        binary=$candidate; expected=$candidate_sha
        envs=(--env KM_ROUTE=auto --env KM_ELC_PAR_NF4=1)
      fi
      ont=ore_ont_${ont_id}.owl
      out="$root/results/${ont_id}-${label}-${rep}.json"
      /usr/bin/python3 "$harness/full_panel_run_one.py" \
        --kind km --arm "${ont_id}_${label}_${rep}" \
        --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
        --binary "$binary" --workers 16 --timeout 240 --memcap-mb 20480 \
        --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
        --gold-kind konclude --workdir "$work/$ont_id/$label-$rep" \
        --failures-dir "$root/failures" --capture-km-route "${envs[@]}" > "$out.tmp"
      /usr/bin/python3 - "$out.tmp" "$expected" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2]
assert r["status"] == "ok" and r["verdict"] == "match", r
assert r["selected_route_trace"] == "certified_el_production", r
PY
      mv "$out.tmp" "$out"
    done
  done
done
python3 - "$root/results" <<'PY'
import glob,json,statistics,sys
root=sys.argv[1]; summary={}
for ont in (8737,16744):
 def rows(label): return [json.load(open(p)) for p in sorted(glob.glob(f"{root}/{ont}-{label}-[123].json"))]
 b=rows("baseline"); c=rows("candidate")
 assert len(b)==len(c)==3 and len({r["signature_sha256"] for r in b+c})==1
 summary[str(ont)]={
  "baseline_wall":statistics.mean(r["wall_s"] for r in b),
  "candidate_wall":statistics.mean(r["wall_s"] for r in c),
  "baseline_peak":statistics.mean(r["peak_mb"] for r in b),
  "candidate_peak":statistics.mean(r["peak_mb"] for r in c),
 }
print(json.dumps(summary,indent=2,sort_keys=True))
PY
echo PARALLEL_NF4_PAIR_COMPLETE
