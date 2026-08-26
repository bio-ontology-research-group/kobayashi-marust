#!/bin/bash
#SBATCH --job-name=km-nominal-v4-trace
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:05:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --array=0-1%2
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-nominal-projection-v4-20260825/phase-trace/slurm-%A_%a.out

set -euo pipefail
ids=(148 8480)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/v110-nominal-projection-v4-20260825
expected=69fe6f20b41d688c63032e093087032a64d39152ef4f6417d77dd12be44b5b35
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$expected" ]]
mkdir -p "$root/phase-trace"
out="$root/phase-trace/ore_ont_${id}.json"
err="$root/phase-trace/ore_ont_${id}.timing"
env KM_ROUTE=auto KM_ABOX_DISJOINT_UNION_CHECK=1 KM_TIMING=1 \
  "$root/km" classify "/ibex/scratch/hohndor/km/corpus/ore_ont_${id}.owl" \
  > "$out.tmp" 2> "$err.tmp"
/usr/bin/python3 - "$out.tmp" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r.get("consistent") is True, r
assert isinstance(r.get("subsumptions"), list), sorted(r)
assert isinstance(r.get("unsatisfiable"), list), sorted(r)
assert r.get("dropped") == 0, {k: r.get(k) for k in ("consistent", "dropped")}
PY
mv "$out.tmp" "$out"
mv "$err.tmp" "$err"
echo NOMINAL_V4_PHASE_TRACE_COMPLETE ontology="$id"
