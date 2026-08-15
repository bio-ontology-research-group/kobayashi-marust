#!/bin/bash
#SBATCH --job-name=km-3215-labeltags-reverse
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:09:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/3215-label-tags-20260815/reverse-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/3215-label-tags-20260815
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
baseline=/ibex/scratch/hohndor/km/6934-general-isolation-20260814/km
candidate=$root/km
baseline_sha=4d8d81378d565d6b5d0b33b8fe352d2e6aa076b7c82a0c196bb58bc167401071
candidate_sha=eb2f4335500dd4c6621676f4c87636a30867fe0d5484a3b879841f423adc4c84
ont=ore_ont_3215.owl
mkdir -p "$root/reverse-results" "$root/failures"
[[ $(sha256sum "$baseline" | cut -d' ' -f1) == "$baseline_sha" ]]
[[ $(sha256sum "$candidate" | cut -d' ' -f1) == "$candidate_sha" ]]
cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]
work=${SLURM_TMPDIR:-/tmp}/km-3215-labeltags-reverse-$SLURM_JOB_ID
for label in candidate baseline; do
  binary=$baseline; expected=$baseline_sha
  if [[ $label == candidate ]]; then binary=$candidate; expected=$candidate_sha; fi
  out="$root/reverse-results/${label}-${SLURM_JOB_ID}.json"
  /usr/bin/python3 "$harness/full_panel_run_one.py" --kind km \
    --arm "3215_labeltags_reverse_${label}" --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
    --binary "$binary" --workers 16 --timeout 240 --memcap-mb 20480 \
    --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
    --gold-kind konclude --workdir "$work/$label" --failures-dir "$root/failures" \
    --checkpoint "$out.checkpoint.json" --capture-km-route --env KM_ROUTE=auto > "$out.tmp"
  /usr/bin/python3 - "$out.tmp" "$expected" <<'PY'
import json,sys
r=json.load(open(sys.argv[1])); assert r["binary_sha256"]==sys.argv[2]
assert r["checkpointed"] and r["status"]=="ok" and r["verdict"]=="match",r
assert r["selected_route_trace"]=="production_all",r
PY
  mv "$out.tmp" "$out"
done
/usr/bin/python3 - "$root/reverse-results" "$SLURM_JOB_ID" <<'PY'
import json,sys
root,job=sys.argv[1:]; b=json.load(open(f"{root}/baseline-{job}.json")); c=json.load(open(f"{root}/candidate-{job}.json"))
assert b["signature_sha256"]==c["signature_sha256"]
print(json.dumps({"baseline_wall_s":b["wall_s"],"candidate_wall_s":c["wall_s"],"wall_change_pct":100*(c["wall_s"]/b["wall_s"]-1),"baseline_peak_mb":b["peak_mb"],"candidate_peak_mb":c["peak_mb"],"peak_change_pct":100*(c["peak_mb"]/b["peak_mb"]-1)},sort_keys=True))
PY
echo REVERSE_COMPLETE
