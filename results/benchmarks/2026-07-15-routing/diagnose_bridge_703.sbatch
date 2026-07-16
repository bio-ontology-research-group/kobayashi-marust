#!/bin/bash
# Isolate the seven-pair bridge incompleteness found by the early definitive
# matrix audit. This is a diagnostic, not a training panel.
#SBATCH --job-name=km-bridge-703
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/bridge-703-%j.out

set -euo pipefail
km_root=/ibex/scratch/hohndor/km
root=$km_root/routing_20260715
km=$root/km-profiled-final3
ontology=ore_ont_703.owl
local_ontology=${SLURM_TMPDIR:-/tmp}/$ontology
/usr/bin/cp "$km_root/corpus/$ontology" "$local_ontology"
out=$root/diagnose-bridge-703
rm -rf "$out"
mkdir -p "$out"

run() {
  local arm=$1
  shift
  /usr/bin/env \
    KM_ROUTE=manual KM_THREADS=16 KM_PAR_MEM_GB=18 KM_HT_MEM_GB=18 \
    KM_KEEP_CHAIN_AXIOMS=1 KM_HT_ONLY=bridge KM_NO_ELC=1 \
    KM_NO_ABSORB_PORTFOLIO=1 KM_ABSORB=0 KM_NO_HT_QO_ROUTER=1 \
    KM_NO_HT_SHOQ=1 KM_NO_HT_CARD=1 KM_TRIGGER_ABSORB=1 \
    KM_BRIDGE_PROBE_BUDGET_S=30 KM_BRIDGE_RETRY_ROUNDS=0 \
    KM_HT_SATURATION_BUDGET_S=180 KM_HT_MODE=race KM_HT_STATS=1 \
    KM_BRIDGE_PROGRESS=1 KM_HT_SAT_RESIDUE=1 KM_TIMING=1 "$@" \
    /usr/bin/time -v -o "$out/$arm.time" \
    "$km" classify "$local_ontology" \
    > "$out/$arm.json" 2> "$out/$arm.stderr"
}

run current
run no_saturation KM_HT_NO_SATURATION=1
run saturation_no_cache KM_HT_NO_SATCACHE=1
run no_associated_cache KM_HT_NO_ASSOC_EXP_CACHE=1

/usr/bin/python3 - "$out" "$km_root/gold/konclude__$ontology.sig.gz" "$root" <<'PY'
import gzip
import json
import os
import sys

out, gold_path, root = sys.argv[1:]
sys.path.insert(0, root)
import ore_canon

pairs = set()
unsat = set()
with gzip.open(gold_path, "rt", encoding="utf-8") as handle:
    gold_consistent = handle.readline().strip() == "1"
    in_unsat = False
    for line in handle:
        line = line.strip()
        if line == "#UNSAT":
            in_unsat = True
        elif line and in_unsat:
            unsat.add(ore_canon.localname(line))
        elif line:
            left, right = map(ore_canon.localname, line.split())
            if left != right and right not in ("Thing", "owlThing", "owlNothing"):
                pairs.add((left, right))

for arm in ("current", "no_saturation", "saturation_no_cache", "no_associated_cache"):
    text = open(os.path.join(out, arm + ".json"), encoding="utf-8").read()
    consistent, actual, actual_unsat, capped = ore_canon.canonicalize(text, "json")
    row = {
        "arm": arm,
        "consistent": consistent,
        "capped": capped,
        "pairs": len(actual),
        "missing": sorted(pairs - actual),
        "extra": sorted(actual - pairs),
        "missing_unsat": sorted(unsat - actual_unsat),
        "extra_unsat": sorted(actual_unsat - unsat),
        "consistency_mismatch": consistent != gold_consistent,
    }
    print(json.dumps(row, sort_keys=True))
PY

/usr/bin/rm -f "$local_ontology"
