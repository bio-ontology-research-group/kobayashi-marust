#!/bin/bash
# Regression probe for ontologies whose parallel allocation burst previously
# killed the whole batch cgroup before a terminal row could be published.
# Success means a checkpointed terminal row exists, not that the ontology is OK.
#SBATCH --job-name=km-cgroup-probe
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=64G
#SBATCH --exclusive
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/integrated-main-full-20260730/slurm-%x-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/integrated-main-full-20260730
km_root=/ibex/scratch/hohndor/km
ontology=ore_ont_3524.owl
probe=$root/containment-probe-$SLURM_JOB_ID
work=${SLURM_TMPDIR:-/tmp}/km-cgroup-probe-$SLURM_JOB_ID
/usr/bin/mkdir -p "$probe" "$work"
/usr/bin/cp "$km_root/corpus/$ontology" "$work/$ontology"

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm km_reasoner_step_containment_probe \
  --ontology "$work/$ontology" \
  --binary "$root/ibex_reasoner_step.sh" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$probe/failures" \
  --checkpoint "$probe/$ontology.checkpoint.json" \
  --env KM_ROUTE=auto \
  > "$probe/$ontology.json.tmp"

/usr/bin/python3 - "$probe/$ontology.json.tmp" "$ontology" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[2]:
    raise SystemExit(f"ontology mismatch: {row}")
if not row.get("checkpointed"):
    raise SystemExit(f"missing terminal checkpoint: {row}")
if row.get("status") not in {"ok", "timeout", "memout", "error", "unsupported"}:
    raise SystemExit(f"invalid terminal status: {row}")
print(json.dumps(row, sort_keys=True))
PY
/usr/bin/mv "$probe/$ontology.json.tmp" "$probe/$ontology.json"
echo "CONTAINMENT_PROBE_COMPLETE ontology=$ontology"
