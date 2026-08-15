#!/bin/bash
#SBATCH --job-name=km-v026-candidate-paired
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-591%30
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/intersection-inproc-20260815/paired-v026/slurm-%A_%a.out

set -euo pipefail
candidate_root=/ibex/scratch/hohndor/km/intersection-inproc-20260815
root=$candidate_root/paired-v026
harness=$candidate_root/full-sweep
baseline=/ibex/scratch/hohndor/km/6934-general-isolation-20260814/km
candidate=$candidate_root/km
baseline_sha=4d8d81378d565d6b5d0b33b8fe352d2e6aa076b7c82a0c196bb58bc167401071
candidate_sha=628b11d8e95dcedf2394afac53a35399ba1e9106b0e844aae3dbbad41852875a
[[ $(sha256sum "$baseline" | cut -d' ' -f1) == $baseline_sha ]]
[[ $(sha256sum "$candidate" | cut -d' ' -f1) == $candidate_sha ]]
index=${SLURM_ARRAY_TASK_ID:?}
ontology=$(sed -n "$((index + 1))p" "$harness/ore592.txt")
[[ $ontology =~ ^ore_ont_[0-9]+\.owl$ ]]
km_root=/ibex/scratch/hohndor/km
mkdir -p "$root/results-baseline" "$root/results-candidate" "$root/failures"

complete=1
for arm in baseline candidate; do
    row=$root/results-$arm/$ontology.json
    [[ -f $row ]] || complete=0
done
if (( complete )); then
    /usr/bin/python3 - "$root/results-baseline/$ontology.json" "$root/results-candidate/$ontology.json" "$ontology" "$index" <<'PY'
import json
import sys
for path in sys.argv[1:3]:
    row = json.load(open(path))
    if row.get("ont") != sys.argv[3] or row.get("slurm_array_task_id") != sys.argv[4]:
        raise SystemExit(f"invalid retained row: {row}")
    if row.get("status") not in {"ok", "timeout", "memout", "error", "unsupported"}:
        raise SystemExit(f"invalid terminal status: {row}")
print("ALREADY_COMPLETE", sys.argv[3])
PY
    exit 0
fi

if (( index % 2 == 0 )); then
    order=(baseline candidate)
else
    order=(candidate baseline)
fi
for arm in "${order[@]}"; do
    binary=$baseline
    sha=$baseline_sha
    [[ $arm == candidate ]] && binary=$candidate && sha=$candidate_sha
    runner=$harness/full_panel_run_one.py
    if [[ $ontology == ore_ont_3524.owl || $ontology == ore_ont_13503.owl || $ontology == ore_ont_4669.owl || $ontology == ore_ont_15703.owl ]]; then
        runner=$harness/full_panel_run_one_collision_safe.py
    fi
    work=${SLURM_TMPDIR:-/tmp}/km-paired-${index}-${arm}
    tmp=$root/results-$arm/$ontology.json.tmp
    checkpoint=$root/results-$arm/$ontology.checkpoint.json
    /usr/bin/python3 "$runner" \
      --kind km --arm "$arm" --ontology "$km_root/corpus/$ontology" \
      --binary "$binary" --binary-sha "$sha" --workers 16 \
      --timeout 240 --memcap-mb 20480 \
      --gold "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz" \
      --gold-kind konclude --workdir "$work" --failures-dir "$root/failures" \
      --checkpoint "$checkpoint" --capture-km-route --env KM_ROUTE=auto > "$tmp"
    /usr/bin/python3 - "$tmp" "$ontology" "$index" "$sha" <<'PY'
import json
import sys
row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[2] or row.get("slurm_array_task_id") != sys.argv[3]:
    raise SystemExit(f"identity mismatch: {row}")
if row.get("binary_sha256") != sys.argv[4] or not row.get("checkpointed"):
    raise SystemExit(f"binary/checkpoint mismatch: {row}")
if row.get("status") not in {"ok", "timeout", "memout", "error", "unsupported"}:
    raise SystemExit(f"invalid status: {row}")
PY
    mv "$tmp" "$root/results-$arm/$ontology.json"
done
echo "PAIR_COMPLETE index=$index ontology=$ontology order=${order[*]}"
