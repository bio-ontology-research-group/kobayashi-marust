#!/bin/bash
#SBATCH --job-name=km-7914-reuse-ab
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/7914-regression-20260813/reuse-ab-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/7914-regression-20260813
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
bin=$root/bin/km-53eb64a
expected=$(cut -d' ' -f1 "$bin.sha256")
[[ $(sha256sum "$bin" | cut -d' ' -f1) == "$expected" ]]
mkdir -p "$root/reuse-results" "$root/reuse-failures"
work=${SLURM_TMPDIR:-/tmp}/km-7914-reuse-${SLURM_JOB_ID}
for arm in reuse_on reuse_off; do
  extra=()
  [[ $arm == reuse_off ]] && extra+=(--env KM_HT_NO_NATIVE_BACKEND_REUSE=1)
  out="$root/reuse-results/${arm}.json"
  PYTHONPATH="$harness" /usr/bin/python3 "$harness/full_panel_run_one.py" \
    --kind km --arm "7914_${arm}" \
    --ontology /ibex/scratch/hohndor/km/corpus/ore_ont_7914.owl \
    --binary "$bin" --workers 16 --timeout 240 --memcap-mb 20480 \
    --gold /ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__ore_ont_7914.owl.sig.gz \
    --gold-kind konclude --workdir "$work/$arm" --failures-dir "$root/reuse-failures" \
    --checkpoint "$root/reuse-results/${arm}.checkpoint.json" --capture-km-route \
    --env KM_ROUTE=ht_bridge "${extra[@]}" > "$out.tmp"
  /usr/bin/python3 - "$out.tmp" "$expected" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2]
assert r["checkpointed"] and r["selected_route_trace"] == "ht_bridge"
assert r["status"] == "ok" and r["verdict"] == "match", r
PY
  mv "$out.tmp" "$out"
done
/usr/bin/python3 - "$root/reuse-results/reuse_on.json" "$root/reuse-results/reuse_off.json" <<'PY'
import json,sys
rows=[json.load(open(p)) for p in sys.argv[1:]]
assert len({r["signature_sha256"] for r in rows}) == 1
print([(r["arm"],r["wall_s"],r["peak_mb"]) for r in rows])
PY
echo REUSE_AB_COMPLETE
