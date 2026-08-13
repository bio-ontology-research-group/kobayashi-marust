#!/bin/bash
#SBATCH --job-name=km-large-el-timing
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-5
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/large-el-timing-20260813/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/large-el-timing-20260813
binary=/ibex/scratch/hohndor/km/14817-thread-candidate-20260813/km
expected=c2947579daf2fff7fb723eb5e8f7d27bc021e0ee6e80878445d727c1b7eaaac2
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected" ]]
onts=(8737 1559 15280 13482 10750 1012)
ont=ore_ont_${onts[${SLURM_ARRAY_TASK_ID:?}]}.owl
work=${SLURM_TMPDIR:-/tmp}/km-large-el-timing-${SLURM_JOB_ID}
mkdir -p "$work" "$root/results"
timeout 240 /usr/bin/time -v env KM_ROUTE=auto KM_TIMING=1 \
  KM_OFN_TIMING=1 KM_ELC_TIMING=1 \
  "$binary" classify "/ibex/scratch/hohndor/km/corpus/$ont" \
  > "$work/$ont.json" 2> "$root/results/$ont.timing.tmp"
/usr/bin/python3 - "$work/$ont.json" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
if r.get("complete") is False:
    raise SystemExit(f"incomplete result: {r}")
PY
mv "$root/results/$ont.timing.tmp" "$root/results/$ont.timing"
echo "TIMING_COMPLETE ontology=$ont"
