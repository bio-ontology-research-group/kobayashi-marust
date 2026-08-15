#!/bin/bash
#SBATCH --job-name=km-el-binary-final-pair
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-591%40
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/el-binary-final-pair-20260815/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/el-binary-final-pair-20260815
harness=/ibex/scratch/hohndor/km/intersection-inproc-20260815/full-sweep
baseline=/ibex/scratch/hohndor/km/intersection-inproc-20260815/km
candidate=/ibex/scratch/hohndor/km/el-binary-final-20260815/km
baseline_sha=628b11d8e95dcedf2394afac53a35399ba1e9106b0e844aae3dbbad41852875a
candidate_sha=1cd7dcbeea96e39b4b4b50eec48e42a9005e223a26515661b6329e746578033c
index=${SLURM_ARRAY_TASK_ID:?}
ontology=$(sed -n "$((index + 1))p" "$root/ore592.txt")
[[ -n $ontology ]]
[[ $(sha256sum "$baseline" | cut -d' ' -f1) == $baseline_sha ]]
[[ $(sha256sum "$candidate" | cut -d' ' -f1) == $candidate_sha ]]
mkdir -p "$root/results" "$root/failures"
runner=$harness/full_panel_run_one.py
case "$ontology" in
  ore_ont_3524.owl|ore_ont_13503.owl|ore_ont_4669.owl|ore_ont_15703.owl)
    runner=$harness/full_panel_run_one_collision_safe.py ;;
esac
if (( index % 2 == 0 )); then
  order=(baseline candidate)
else
  order=(candidate baseline)
fi
for sequence in 0 1; do
  arm=${order[$sequence]}
  binary=$baseline
  sha=$baseline_sha
  if [[ $arm == candidate ]]; then
    binary=$candidate
    sha=$candidate_sha
  fi
  label=${sequence}-${arm}
  final=$root/results/${ontology}.${label}.json
  checkpoint=${final}.checkpoint.json
  if [[ -s $final && -s $checkpoint ]]; then
    /usr/bin/python3 - "$final" "$ontology" "$sha" <<'PY'
import json, sys
r = json.load(open(sys.argv[1]))
assert r["ont"] == sys.argv[2] and r["binary_sha256"] == sys.argv[3], r
assert r["status"] == "ok" or r["ont"] == "ore_ont_1194.owl", r
PY
    continue
  fi
  rm -f "$final" "$checkpoint" "${final}.tmp"
  /usr/bin/python3 "$runner" --kind km --arm "$label" \
    --ontology "/ibex/scratch/hohndor/km/corpus/$ontology" \
    --binary "$binary" --binary-sha "$sha" --workers 16 \
    --timeout 240 --memcap-mb 20480 \
    --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ontology.sig.gz" \
    --gold-kind konclude --workdir "${SLURM_TMPDIR:-/tmp}/km-final-pair-${index}-${label}" \
    --failures-dir "$root/failures" --checkpoint "$checkpoint" \
    --capture-km-route --env KM_ROUTE=auto > "${final}.tmp"
  /usr/bin/python3 - "${final}.tmp" "$ontology" "$sha" <<'PY'
import json, sys
r = json.load(open(sys.argv[1]))
assert r["ont"] == sys.argv[2] and r["binary_sha256"] == sys.argv[3], r
assert r["status"] in {"ok", "error"}, r
assert r["status"] == "ok" or r["ont"] == "ore_ont_1194.owl", r
PY
  mv "${final}.tmp" "$final"
done
/usr/bin/python3 - "$root/results/${ontology}.0-${order[0]}.json" "$root/results/${ontology}.1-${order[1]}.json" <<'PY'
import json, sys
a, b = (json.load(open(path)) for path in sys.argv[1:])
keys = (
    "status", "verdict", "signature_sha256", "consistent", "missing", "extra",
    "missing_unsat", "extra_unsat", "subsumptions", "unsatisfiable",
)
assert all(a.get(key) == b.get(key) for key in keys), (a, b)
PY
echo "PAIR_COMPLETE index=$index ontology=$ontology order=${order[*]}"
