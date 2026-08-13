#!/bin/bash
#SBATCH --job-name=km-10621-bridge
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:15:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/10621-sequential-bridge-20260813/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/10621-sequential-bridge-20260813
candidate=/ibex/scratch/hohndor/km/candidate-78d5674-atomic-abox-20260813
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
expected=d19938110369da96167feddf2a257550bf80aca1793afd40154d18d303663f8e
ont=ore_ont_10621.owl
[[ $(sha256sum "$candidate/km" | cut -d" " -f1) == "$expected" ]]
cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]
PYTHONPATH="$harness" /usr/bin/python3 -c \
  'import full_panel_fingerprint, full_panel_run_one, full_panel_run_one_collision_safe, full_panel_run_one_fulliri_only, ore_canon, tree_watchdog'

mkdir -p "$root/results" "$root/failures"
work=${SLURM_TMPDIR:-/tmp}/km-10621-${SLURM_JOB_ID}
for route in auto ht_bridge certified_nominals; do
  out="$root/results/${ont}__${route}.json"
  /usr/bin/python3 "$harness/full_panel_run_one.py" \
    --kind km --arm "10621_${route}" \
    --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
    --binary "$candidate/km" --workers 16 --timeout 240 --memcap-mb 20480 \
    --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
    --gold-kind konclude --workdir "$work/$route" --failures-dir "$root/failures" \
    --checkpoint "$root/results/${ont}__${route}.checkpoint.json" \
    --capture-km-route --env "KM_ROUTE=$route" > "$out.tmp"
  /usr/bin/python3 - "$out.tmp" "$ont" "$expected" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["ont"] == sys.argv[2]
assert r["binary_sha256"] == sys.argv[3]
assert r["checkpointed"]
assert r["status"] in {"ok","timeout","memout","error","unsupported"}
if r["status"] == "ok": assert r["verdict"] == "match", r
PY
  mv "$out.tmp" "$out"
done
echo PANEL_COMPLETE ontology=$ont
