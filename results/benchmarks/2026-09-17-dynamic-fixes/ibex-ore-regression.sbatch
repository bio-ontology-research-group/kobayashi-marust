#!/bin/bash
#SBATCH --job-name=km-abox-candidate-ore592
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/dynamic-benchmark-20260917/abox-candidate-v1/slurm-%A_%a.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/dynamic-benchmark-20260917/abox-candidate-v1
harness=/ibex/scratch/hohndor/km/v1.4-15672-refined-20260902/full-sweep
general_runner=/ibex/scratch/hohndor/km/v12-sparse-horn-16-20260827/full-v3/full_panel_run_one.py
collision_runner=/ibex/scratch/hohndor/km/v1.4-source-bridge-20260902/full-sweep/full_panel_run_one_collision_safe.py
binary=$root/km.ibex
[[ $(awk -F'\t' '$1 == "source_archive_sha256" {print $2}' "$root/build-receipt.tsv") == 9a77671d75ed4d72e5cf4786610da1daeedb4054058e9b7c13177d10e691204d ]]
expected=$(awk -F'\t' '$1 == "binary_sha256" {print $2}' "$root/build-receipt.tsv")
/ibex/scratch/hohndor/km/v1.4-1194-default-20260903/check-km-deployment.sh "$binary" "$expected" >/dev/null
cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]
i=${SLURM_ARRAY_TASK_ID:?}
ont=$(sed -n "$((i + 1))p" "$harness/ore592.txt")
[[ $ont == ore_ont_*.owl ]]
case "$ont" in
  ore_ont_13503.owl|ore_ont_15703.owl|ore_ont_3524.owl|ore_ont_4669.owl) runner=$collision_runner ;;
  *) runner=$general_runner ;;
esac
panel=$root/full-sweep
work=$panel/work/${SLURM_JOB_ID}_${i}
mkdir -p "$panel/results" "$panel/failures" "$work/run"
out=$panel/results/$ont.json
PYTHONPATH="$(dirname "$runner")" /usr/bin/python3 "$runner" \
  --kind km --arm km_abox_candidate_v1 \
  --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
  --binary "$binary" --workers 16 --timeout 240 --memcap-mb 20480 \
  --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
  --gold-kind konclude --workdir "$work/run" \
  --failures-dir "$panel/failures" --checkpoint "$out.checkpoint.json" \
  --capture-km-route --env KM_ROUTE=auto > "$out.tmp"
/usr/bin/python3 - "$out.tmp" "$ont" "$expected" <<'PY'
import json, sys
r = json.load(open(sys.argv[1]))
assert r["ont"] == sys.argv[2], r
assert r["binary_sha256"] == sys.argv[3], r
assert r.get("checkpointed") is True, r
assert r["status"] in {"ok", "timeout", "memout", "error", "unsupported"}, r
assert r.get("selected_route_trace") is not None or r["status"] != "ok", r
print(r["ont"], r["status"], r.get("verdict"), r.get("wall_s"), r.get("peak_mb"), r.get("selected_route_trace"))
PY
mv "$out.tmp" "$out"
find "$work" -type f -delete
find "$work" -depth -type d -empty -delete
echo TASK_COMPLETE
