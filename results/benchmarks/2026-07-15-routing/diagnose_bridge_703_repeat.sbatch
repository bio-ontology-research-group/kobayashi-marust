#!/bin/bash
# Reproduce the exact clean matrix environment repeatedly to distinguish an
# option-contract error from order/timing nondeterminism in the bridge race.
#SBATCH --job-name=km-bridge-703-rep
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/bridge-703-rep-%j.out

set -euo pipefail
km_root=/ibex/scratch/hohndor/km
root=$km_root/routing_20260715
runner=$root/bench_one_matrix_frozen.py
km=$root/km-profiled-final3
ontology=ore_ont_703.owl
local_ontology=${SLURM_TMPDIR:-/tmp}/$ontology
/usr/bin/cp "$km_root/corpus/$ontology" "$local_ontology"
work=${SLURM_TMPDIR:-/tmp}/km-bridge-703-repeat-$SLURM_JOB_ID
out=$root/diagnose-bridge-703-repeat.jsonl
fail=$root/diagnose-bridge-703-repeat-failures
rm -rf "$work" "$fail"
mkdir -p "$work" "$fail"
: > "$out"
km_sha=$(/usr/bin/sha256sum "$km" | /usr/bin/cut -d' ' -f1)

for replicate in $(seq 1 20); do
  /usr/bin/python3 "$runner" --kind km --arm current --order-index "$replicate" \
    --ontology "$local_ontology" --binary "$km" --binary-sha "$km_sha" \
    --gold "$km_root/gold/konclude__$ontology.sig.gz" \
    --workdir "$work" --failures-dir "$fail" --timeout 240 --memcap-mb 20480 \
    --env KM_ROUTE=manual --env KM_THREADS=16 --env KM_PAR_MEM_GB=18 \
    --env KM_HT_MEM_GB=18 --env KM_KEEP_CHAIN_AXIOMS=1 \
    --env KM_HT_ONLY=certified --env KM_NO_ELC=1 \
    --env KM_NO_ABSORB_PORTFOLIO=1 --env KM_ABSORB=0 \
    --env KM_NO_HT_QO_ROUTER=1 --env KM_NO_HT_SHOQ=1 \
    --env KM_NO_HT_CARD=1 --env KM_TRIGGER_ABSORB=1 \
    --env KM_BRIDGE_PROBE_BUDGET_S=30 --env KM_BRIDGE_RETRY_ROUNDS=0 \
    --env KM_HT_SATURATION_BUDGET_S=180 --env KM_HT_ONLY=bridge \
    --env KM_HT_MODE=race >> "$out"
done

/usr/bin/python3 - "$out" <<'PY'
import collections
import json
import sys

rows = [json.loads(line) for line in open(sys.argv[1]) if line.strip()]
print("rows", len(rows))
print("outcomes", collections.Counter(
    (row["status"], row["verdict"], row.get("missing"), row.get("extra"),
     row.get("subsumptions")) for row in rows))
print("wall", [row["wall_s"] for row in rows])
PY

/usr/bin/rm -rf "$work" "$local_ontology"
