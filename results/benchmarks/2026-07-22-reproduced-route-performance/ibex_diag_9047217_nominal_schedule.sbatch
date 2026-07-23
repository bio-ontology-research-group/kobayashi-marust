#!/bin/bash
# Capture the real 10621 converted-input fields used by the nominal scheduler.
# This is a bounded diagnostic only; timeout is expected and no taxonomy is accepted.
#SBATCH --job-name=km-9047217-diag
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:03:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/target-f40713c/slurm-%x-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/target-f40713c
binary=$root/bin/km-9047217-ibex
runner=$root/drivers/validate_tail_runner.py
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_10621.owl
out=$root/diagnostics/$SLURM_JOB_ID
/usr/bin/mkdir -p "$out"

set +e
/usr/bin/python3 -I "$runner" \
    --kind km --label 10621-certified-scheduler-diagnostic \
    --ontology "$ontology" --binary "$binary" \
    --output-dir "$out/run" --timeout 20 --memcap-mb 20480 \
    --env KM_ROUTE=certified_nominals --env KM_TIMING=1 \
    --env KM_THREADS=16 --env KM_PAR_MEM_GB=18 --env KM_HT_MEM_GB=18 \
    --env "KM_DUMP_TIN=$out/tin.json"
runner_rc=$?
set -e
[[ $runner_rc -ne 0 ]]
[[ -s $out/tin.json ]]

/usr/bin/python3 - "$out/tin.json" "$out/run/run.json" <<'PY'
import json
from pathlib import Path
import sys

tin = json.loads(Path(sys.argv[1]).read_text())
run = json.loads(Path(sys.argv[2]).read_text())
abox = tin.get("nominal_abox", {})
summary = {
    "run_status": run.get("status"),
    "peak_mb": run.get("peak_mb"),
    "complete": abox.get("complete"),
    "unsupported": abox.get("unsupported"),
    "individuals": len(abox.get("individuals", [])),
    "positive_roles": len(abox.get("role_assertions", [])),
    "negative_roles": len(abox.get("negative_role_assertions", [])),
    "different": len(abox.get("different", [])),
    "dropped": tin.get("dropped"),
    "fenced": tin.get("fenced"),
    "nominals": len(tin.get("nominals", [])),
    "cards": len(tin.get("card_defs", [])),
    "inverse": tin.get("inverse"),
    "number": tin.get("number"),
    "queries": len(tin.get("queries", [])),
}
print(json.dumps(summary, sort_keys=True))
PY
/usr/bin/sha256sum "$binary" "$ontology" "$out/tin.json"
echo NOMINAL_SCHEDULER_DIAGNOSTIC_COMPLETE
