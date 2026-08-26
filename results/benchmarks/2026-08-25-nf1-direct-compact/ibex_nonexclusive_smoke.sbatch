#!/bin/bash
#SBATCH --job-name=km-nf1-compact-smoke
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-nf1-compact-20260825/smoke-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v110-nf1-compact-20260825
baseline=/ibex/scratch/hohndor/km/v110-acyclic-nf1-20260825/km
candidate="$root/km"
harness=/ibex/scratch/hohndor/km/v110-baseline-20260825/full-sweep
ont=ore_ont_10689.owl
mkdir -p "$root/smoke/results" "$root/smoke/failures"
work=${SLURM_TMPDIR:-/tmp}/km-nf1-compact-smoke-${SLURM_JOB_ID}

for arm in baseline candidate; do
  binary=$baseline
  [[ $arm == candidate ]] && binary=$candidate
  out="$root/smoke/results/${arm}.json"
  /usr/bin/python3 "$harness/full_panel_run_one.py" \
    --kind km --arm "nf1_compact_smoke_$arm" \
    --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
    --binary "$binary" --workers 4 --timeout 240 --memcap-mb 20480 \
    --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
    --gold-kind konclude --workdir "$work/$arm" \
    --failures-dir "$root/smoke/failures" \
    --checkpoint "$root/smoke/results/${arm}.checkpoint.json" \
    --capture-km-route --env KM_ROUTE=auto > "$out.tmp"
  /usr/bin/python3 - "$out.tmp" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["checkpointed"] and r["status"] == "ok" and r["verdict"] == "match", r
PY
  mv "$out.tmp" "$out"
done

/usr/bin/python3 - "$root/smoke/results" <<'PY'
import json,sys
root=sys.argv[1]
b=json.load(open(root+"/baseline.json")); c=json.load(open(root+"/candidate.json"))
assert b["binary_sha256"] != c["binary_sha256"]
assert b["signature_sha256"] == c["signature_sha256"]
print(json.dumps({
 "baseline_binary":b["binary_sha256"], "candidate_binary":c["binary_sha256"],
 "baseline_wall_s":b["wall_s"], "candidate_wall_s":c["wall_s"],
 "baseline_peak_mb":b["peak_mb"], "candidate_peak_mb":c["peak_mb"],
 "signature_sha256":c["signature_sha256"],
}, sort_keys=True))
PY
echo SMOKE_COMPLETE
