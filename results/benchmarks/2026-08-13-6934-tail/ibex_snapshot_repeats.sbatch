#!/bin/bash
#SBATCH --job-name=km-6934-snapshot-repeats
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:18:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/6934-snapshot-move-20260813/repeats-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/6934-snapshot-move-20260813
base=/ibex/scratch/hohndor/km/candidate-78d5674-atomic-abox-20260813
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
out=$root/repeats-$SLURM_JOB_ID
mkdir -p "$out" "$root/failures"
for repetition in 1 2 3; do
  for arm in baseline candidate; do
    if [[ $arm == baseline ]]; then bin=$base/km; else bin=$root/km; fi
    expected=$(sha256sum "$bin" | cut -d' ' -f1)
    work=${SLURM_TMPDIR:-/tmp}/km-6934-snapshot-$arm-$repetition-$SLURM_JOB_ID
    /usr/bin/python3 "$harness/full_panel_run_one.py" \
      --kind km --arm "6934_snapshot_${arm}_${repetition}" \
      --ontology /ibex/scratch/hohndor/km/corpus/ore_ont_6934.owl \
      --binary "$bin" --workers 16 --timeout 240 --memcap-mb 20480 \
      --gold /ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__ore_ont_6934.owl.sig.gz \
      --gold-kind konclude --workdir "$work" --failures-dir "$root/failures" \
      --checkpoint "$out/$arm-$repetition.checkpoint.json" --capture-km-route \
      --env KM_ROUTE=auto > "$out/$arm-$repetition.json.tmp"
    python3 - "$out/$arm-$repetition.json.tmp" "$expected" <<'PY'
import json,sys
r=json.load(open(sys.argv[1])); assert r["binary_sha256"]==sys.argv[2] and r["checkpointed"]
assert r["status"]=="ok" and r["verdict"]=="match",r
PY
    mv "$out/$arm-$repetition.json.tmp" "$out/$arm-$repetition.json"
  done
done
python3 - "$out" <<'PY'
import json,pathlib,statistics,sys
root=pathlib.Path(sys.argv[1]); rows={}
for arm in ("baseline","candidate"):
    rs=[json.load(open(root/f"{arm}-{i}.json")) for i in (1,2,3)]
    assert len({r["signature_sha256"] for r in rs})==1
    rows[arm]={"wall_mean":statistics.mean(r["wall_s"] for r in rs),
               "wall_median":statistics.median(r["wall_s"] for r in rs),
               "peak_mean":statistics.mean(r["peak_mb"] for r in rs)}
assert json.load(open(root/"baseline-1.json"))["signature_sha256"] == json.load(open(root/"candidate-1.json"))["signature_sha256"]
print(rows)
PY
echo REPEATS_COMPLETE
