#!/bin/bash
#SBATCH --job-name=km-83bb37a-screen
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/screen-83bb37a-posting-remove-20260802/screen-%A_%a.out

set -euo pipefail
base=/ibex/scratch/hohndor/km/screen-83bb37a-posting-remove-20260802
km_root=/ibex/scratch/hohndor/km
expected_bin=$(cut -d" " -f1 "$base/km.sha256")
actual_bin=$(sha256sum "$base/km" | cut -d" " -f1)
test "$actual_bin" = "$expected_bin"
case "$SLURM_ARRAY_TASK_ID" in
  0) id=1194; arm=posting_remove_auto_1194; route_args=(--env KM_ROUTE=auto) ;;
  1) id=1194; arm=posting_remove_manual_2t_225_1194; route_args=(--env KM_ROUTE=manual \
       --env KM_MECHANISM=cb --env KM_THREADS=2 --env KM_PAR_MEM_GB=18 \
       --env KM_KEEP_CHAIN_AXIOMS=1 --env KM_NO_ELC=1 --env KM_NO_HT_RACE=1 \
       --env KM_NO_HT_RULES=1 --env KM_NO_ABSORB_PORTFOLIO=1 --env KM_NO_RETRY=1 \
       --env KM_ABSORB=0 --env KM_NOMINALS=1 --env KM_CENTRAL_TIME_CAP=225 \
       --env KM_COMP_IND_BITS=15) ;;
  2) id=8480; arm=posting_remove_auto_8480; route_args=(--env KM_ROUTE=auto) ;;
  3) id=15846; arm=posting_remove_auto_15846; route_args=(--env KM_ROUTE=auto) ;;
  *) exit 64 ;;
esac
ont=ore_ont_${id}.owl
work=${SLURM_TMPDIR:-/tmp}/km-posting-remove-${id}-${SLURM_ARRAY_TASK_ID}-${SLURM_JOB_ID}
mkdir -p "$base/results" "$base/failures" "$work"

PYTHONPATH="$base" /usr/bin/python3 -c \
  'import full_panel_fingerprint, full_panel_run_one, ore_canon, tree_watchdog'

/usr/bin/python3 "$base/full_panel_run_one.py" \
  --kind km --arm "$arm" --ontology "$km_root/corpus/$ont" --binary "$base/km" \
  --workers 16 --timeout 240 --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__${ont}.sig.gz" --gold-kind konclude \
  --workdir "$work/run" --failures-dir "$base/failures" \
  --checkpoint "$base/results/${SLURM_ARRAY_TASK_ID}.checkpoint.json" \
  --capture-km-route "${route_args[@]}" > "$base/results/${SLURM_ARRAY_TASK_ID}.json.tmp"

/usr/bin/python3 - "$base/results/${SLURM_ARRAY_TASK_ID}.json.tmp" "$ont" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["ont"] == sys.argv[2] and r.get("checkpointed"), r
assert r.get("selected_route_trace"), r
assert r["status"] in {"ok","timeout","memout","error","unsupported"}, r
PY
mv "$base/results/${SLURM_ARRAY_TASK_ID}.json.tmp" "$base/results/${SLURM_ARRAY_TASK_ID}.json"
echo "TASK_COMPLETE task=$SLURM_ARRAY_TASK_ID ontology=$ont"
