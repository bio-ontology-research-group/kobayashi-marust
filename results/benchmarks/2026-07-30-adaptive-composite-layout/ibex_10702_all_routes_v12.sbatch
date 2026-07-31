#!/bin/bash
# Exhaust the current named route surface on 10702 without contending with the
# complete production sweep. Submit with a dependency on that sweep.
#SBATCH --job-name=km-v12-10702-routes
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --nodelist=cn512-06-r,cn512-07-l,cn512-02-r,cn512-11-r,cn512-03-r,cn512-08-r,cn512-14-r,cn512-05-l,cn512-03-l,cn512-16-l
#SBATCH --nodes=1
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --exclusive
#SBATCH --array=0-35%5
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v12-full-20260731/10702-routes/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v12-full-20260731
km_root=/ibex/scratch/hohndor/km
probe=$root/10702-routes
ontology=ore_ont_10702.owl
expected_binary=bac80ee342b621730cdc28d1d0a1f6616be7ee0da3fda35db2a6f69fc14806ec
routes=(
  default default8 default1
  production_all production_all8 production_all1
  certified_card_nominals certified_card_proxy_abox
  cb_plain16 cb_plain8 cb_plain1
  cb_absorb16 cb_absorb8 cb_absorb1
  cb_trigger16 cb_trigger8 cb_trigger1
  cb_absorb_portfolio16
  elc elc_cert lean
  ht_general ht_qo ht_shoq ht_card ht_bridge
  certified_nominals ht_features ht_full ht_rules
  tableau tab_race card_fn nominals seq_on seq_off
)
index=${SLURM_ARRAY_TASK_ID:?}
route=${routes[$index]}
cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
if [[ $cpu_model != *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]; then
  echo "UNEXPECTED_CPU_MODEL model=[$cpu_model]" >&2
  exit 2
fi
test "$(/usr/bin/sha256sum "$root/km" | /usr/bin/cut -d' ' -f1)" = "$expected_binary"

work=${SLURM_TMPDIR:-/tmp}/km-v12-10702-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work/run" "$probe/results" "$probe/failures"
result=$probe/results/${index}__${route}.json
checkpoint=$probe/results/${index}__${route}.checkpoint.json

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm "km_10702_${route}" \
  --ontology "$km_root/corpus/$ontology" \
  --binary "$root/km" \
  --binary-sha "$expected_binary" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$probe/failures" \
  --checkpoint "$checkpoint" \
  --env "KM_ROUTE=$route" \
  > "$result.tmp"

/usr/bin/python3 - "$result.tmp" "$route" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("requested_route") != sys.argv[2]:
    raise SystemExit(f"route provenance mismatch: {row}")
if not row.get("checkpointed"):
    raise SystemExit(f"missing terminal checkpoint: {row}")
if row.get("status") not in {"ok", "timeout", "memout", "error", "unsupported"}:
    raise SystemExit(f"invalid terminal status: {row}")
PY
/usr/bin/mv "$result.tmp" "$result"
echo "ROUTE_COMPLETE ontology=$ontology route=$route"
