#!/bin/bash
#SBATCH --job-name=km-cert-el-v2
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/certified-el-typed-handoff-20260814/v2-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/certified-el-typed-handoff-20260814
baseline=/ibex/scratch/hohndor/km/prod1-narrow-pidfd-20260814/km
candidate=$root/km
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
baseline_sha=4379bd61e853869c81148633365740d058e1f768b3320c69334f64e3cf88127f
candidate_sha=$(cut -d' ' -f1 < "$root/km.sha256")
mkdir -p "$root/v2-results" "$root/v2-failures"
work=${SLURM_TMPDIR:-/tmp}/km-cert-el-v2-${SLURM_JOB_ID}
for ont_id in 8737 16744; do
  for label in baseline candidate; do
    binary=$baseline; expected=$baseline_sha
    if [[ $label == candidate ]]; then binary=$candidate; expected=$candidate_sha; fi
    ont=ore_ont_${ont_id}.owl
    out="$root/v2-results/${ont_id}-${label}.json"
    /usr/bin/python3 "$harness/full_panel_run_one.py" \
      --kind km --arm "${ont_id}_${label}_v2" \
      --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
      --binary "$binary" --workers 16 --timeout 240 --memcap-mb 20480 \
      --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
      --gold-kind konclude --workdir "$work/$ont_id/$label" \
      --failures-dir "$root/v2-failures" --capture-km-route --env KM_ROUTE=auto > "$out.tmp"
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
python3 - "$root/v2-results" <<'PY'
import json,sys
root=sys.argv[1]
for ont in (8737,16744):
 b=json.load(open(f"{root}/{ont}-baseline.json")); c=json.load(open(f"{root}/{ont}-candidate.json"))
 assert b["signature_sha256"] == c["signature_sha256"]
 print(ont,"wall",b["wall_s"],c["wall_s"],"peak",b["peak_mb"],c["peak_mb"])
PY
echo CERTIFIED_EL_TYPED_HANDOFF_V2_COMPLETE
