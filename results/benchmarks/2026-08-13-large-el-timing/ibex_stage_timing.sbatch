#!/bin/bash
#SBATCH --job-name=km-large-el-stages
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-3
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/large-el-timing-20260813/stage-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/large-el-timing-20260813
binary=/ibex/scratch/hohndor/km/14817-thread-candidate-20260813/km
expected=c2947579daf2fff7fb723eb5e8f7d27bc021e0ee6e80878445d727c1b7eaaac2
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected" ]]
onts=(8737 1559 13482 15280)
ont=ore_ont_${onts[${SLURM_ARRAY_TASK_ID:?}]}.owl
work=${SLURM_TMPDIR:-/tmp}/km-large-el-stages-${SLURM_JOB_ID}
mkdir -p "$work" "$root/stages"
/usr/bin/time -v env KM_ROUTE=auto KM_OFN_TIMING=1 \
  "$binary" ofn "/ibex/scratch/hohndor/km/corpus/$ont" --meta "$work/meta.json" \
  > "$work/clauses.json" 2> "$root/stages/$ont.frontend.tmp"
/usr/bin/time -v env KM_ELC_TIMING=1 \
  "$binary" elc < "$work/clauses.json" > "$work/out.json" \
  2> "$root/stages/$ont.elc.tmp"
/usr/bin/python3 - "$work/meta.json" "$work/out.json" <<'PY'
import json,sys
for path in sys.argv[1:]:
    json.load(open(path))
PY
mv "$root/stages/$ont.frontend.tmp" "$root/stages/$ont.frontend"
mv "$root/stages/$ont.elc.tmp" "$root/stages/$ont.elc"
echo "STAGE_TIMING_COMPLETE ontology=$ont clauses=$(stat -c %s "$work/clauses.json")"
