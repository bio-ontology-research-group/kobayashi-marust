#!/bin/bash
# Diagnose why current ht_bridge defers on historically exact ORE 12653.
#SBATCH --job-name=km-v11-12653-bridge-guard
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:05:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v11-20260731/12653-bridge-guard/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v11-20260731
km_root=/ibex/scratch/hohndor/km
probe=$root/12653-bridge-guard
work=${SLURM_TMPDIR:-/tmp}/km-v11-12653-bridge-guard-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work" "$probe"

set +e
timeout 240 /usr/bin/prlimit --as=21474836480 -- \
  env \
    KM_ROUTE=ht_bridge \
    KM_DUMP_TIN="$probe/tinput.json" \
    KM_HT_STATS=1 \
    "$root/km" classify "$km_root/corpus/ore_ont_12653.owl" \
    > "$probe/classification.json.tmp" \
    2> "$probe/classification.stderr"
rc=$?
set -e

test -s "$probe/tinput.json"
/usr/bin/python3 - "$probe/tinput.json" "$rc" > "$probe/summary.json.tmp" <<'PY'
import json
import sys

path, rc = sys.argv[1], int(sys.argv[2])
tin = json.load(open(path))
mirrors = []
for axiom in tin.get("source_axioms", []):
    if axiom.get("kind") != "equivalent":
        continue
    for named_side, definition_side in (
        (axiom.get("left"), axiom.get("right")),
        (axiom.get("right"), axiom.get("left")),
    ):
        if not isinstance(named_side, dict) or "Name" not in named_side:
            continue
        if not isinstance(definition_side, dict):
            continue
        forall = definition_side.get("Forall")
        if forall is None:
            continue
        mirrors.append(axiom)
        break
summary = {
    "ontology": "ore_ont_12653.owl",
    "returncode": rc,
    "inverse": tin.get("inverse"),
    "number": tin.get("number"),
    "dropped": tin.get("dropped"),
    "fenced": len(tin.get("fenced", [])),
    "fence_reasons": sorted(
        fence.get("reason") for fence in tin.get("fenced", [])
    ),
    "nominals": len(tin.get("nominals", [])),
    "source_axioms": len(tin.get("source_axioms", [])),
    "candidate_equivalent_named_forall_axioms": mirrors,
}
print(json.dumps(summary, sort_keys=True))
PY
/usr/bin/mv "$probe/summary.json.tmp" "$probe/summary.json"
/usr/bin/mv "$probe/classification.json.tmp" "$probe/classification.json"
echo "TASK_COMPLETE ontology=ore_ont_12653.owl rc=$rc"
